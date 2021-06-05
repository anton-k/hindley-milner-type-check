-- | This module contains the abstract syntax of Hindley-Milner types.
module Type.Check.HM.Type (
    IsVar(..),
    HasLoc(..),
    DefLoc(..),
    -- * Monomorphic types.
    TypeF(..),
    Type(..),
    varT,
    conT,
    arrowT,
    tupleT,
    listT,
    -- * Typed values
    Typed(..),

    -- * Polymorphic types.
    SignatureF(..),
    Signature(..),
    forAllT,
    monoT,
    stripSignature,
    splitSignature,
    typeToSignature,
    getTypeVars,

    VarSet(..),
    differenceVarSet,
    varSetToList,
    memberVarSet,

    HasTypeVars(..),
    LocFunctor(..),
    setLoc,
    TypeFunctor(..),

    extractFunType,
    extractArrow,

    isMono,
    isPoly
) where

--------------------------------------------------------------------------------

import Control.DeepSeq (NFData(..))
import Control.Monad

import Data.Containers.ListUtils (nubOrdOn)
import Data.Data
import Data.Eq.Deriving
import Data.Ord.Deriving
import Data.Fix
import Data.Foldable
import Data.Function (on)
import Data.Map.Strict (Map)
import Data.Monoid
import Data.String
import Data.Tuple (swap)
import Data.Text (Text)

import GHC.Generics

import qualified Data.List as L
import qualified Data.Map.Strict as M

import Text.Show.Deriving

--------------------------------------------------------------------------------

-- | Class to get source code location.
class HasLoc f where
  -- | Type for source code location
  type Loc f :: *

  -- | Get the source code location.
  getLoc :: f -> Loc f

-- | Type class for default location
class DefLoc f where
  defLoc :: f

-- | Functions we need for variables to do type-inference.
class (Show v, Ord v) => IsVar v where
  -- | Canonical leters for pretty output
  prettyLetters :: [v]

instance IsVar String where
  prettyLetters = stringPrettyLetters

instance IsVar Text where
  prettyLetters = stringPrettyLetters

instance IsVar Int where
  prettyLetters = [0..]

stringPrettyLetters :: IsString a => [a]
stringPrettyLetters = fmap fromString $ [1..] >>= flip replicateM ['a'..'z']

instance DefLoc () where
  defLoc = ()

-- | Type functor. Arguments are
--
-- * @loc@ - source code locations
--
-- * @var@ - variable name
--
-- * @r@ - recursion
--
-- There are only two requried constructors: @VarT@ and @ConT@
-- other constructors are used for convenience of pretty-printing the type.
data TypeF loc var r
    = VarT loc var      -- ^ Variables
    | ConT loc var [r]  -- ^ type constant with list of arguments
    | ArrowT loc r r    -- ^ Special case of ConT that is rendered as ->
    | TupleT loc [r]    -- ^ Special case of ConT that is rendered as (,,,)
    | ListT loc r       -- ^ Special case of ConT that is rendered as [a]
    deriving (Eq, Ord, Show, Functor, Foldable, Traversable, Generic, Data)

$(deriveShow1 ''TypeF)
$(deriveEq1   ''TypeF)
$(deriveOrd1  ''TypeF)

-- | Values that are tagged explicitly with their type.
data Typed loc v a = Typed
  { typed'type  :: Type loc v
  , typed'value :: a
  } deriving (Show, Eq, Ord, Functor, Foldable, Traversable, Data)

-- | Monomorphic types.
newtype Type loc var = Type { unType :: Fix (TypeF loc var) }
  deriving (Show, Eq, Ord, Generic, Data)

instance HasLoc (Type loc v) where
  type Loc (Type loc v) = loc
  getLoc (Type (Fix x)) = case x of
    VarT   loc _   -> loc
    ConT   loc _ _ -> loc
    ArrowT loc _ _ -> loc
    TupleT loc _   -> loc
    ListT  loc _   -> loc

instance (NFData loc, NFData var) => NFData (Type loc var) where
  rnf (Type m) = foldFix go m where
    go = \case
      VarT   l v   -> rnf l `seq` rnf v
      ConT   l v x -> rnf l `seq` rnf v `seq` rnf x
      ArrowT l a b -> rnf l `seq` rnf a `seq` rnf b
      TupleT l x   -> rnf l `seq` rnf x
      ListT  l x   -> rnf l `seq` rnf x

-- | 'varT' @loc x@ constructs a type variable named @x@ with source code at @loc@.
varT :: loc -> var -> Type loc var
varT loc var = Type $ Fix $ VarT loc var

-- | 'conT' @loc x@ constructs a type constant named @x@ with source code at @loc@.
conT :: loc -> var -> [Type loc var] -> Type loc var
conT loc name args = Type $ Fix $ ConT loc name $ fmap unType $ args

-- | 'arrowT' @loc t0 t1@ constructs an arrow type from @t0@ to @t1@ with source code at @loc@.
arrowT :: loc -> Type loc v -> Type loc v -> Type loc v
arrowT loc (Type t0) (Type t1) = Type $ Fix $ ArrowT loc t0 t1

-- | 'tupleT' @loc ts@ constructs tuple of types @ts@ with source code at @loc@.
tupleT :: loc -> [Type loc var] -> Type loc var
tupleT loc ts = Type $ Fix $ TupleT loc $ fmap unType ts

-- | 'listT' @loc t@ constructs list of @t@ with source code at @loc@.
listT :: loc -> Type loc var -> Type loc var
listT loc (Type t) = Type $ Fix $ ListT loc t

--------------------------------------------------------------------------------

-- | Functor for signature is a special type that we need for type inference algorithm.
-- We specify which variables in the type are schematic (non-free).
data SignatureF loc var r
    = ForAllT loc var r     -- ^ specify schematic variable
    | MonoT (Type loc var)  -- ^ contains the type
    deriving (Eq, Ord, Show, Functor, Foldable, Traversable, Data)

$(deriveShow1 ''SignatureF)
$(deriveEq1   ''SignatureF)
$(deriveOrd1  ''SignatureF)

-- | Signaure is a special type that we need for type inference algorithm.
-- We specify which variables in the type are schematic (non-free).
newtype Signature loc var = Signature { unSignature :: Fix (SignatureF loc var)
  } deriving (Show, Eq, Ord, Data)

instance Functor (Signature loc) where
  fmap f (Signature x) = Signature $ foldFix go x
    where
      go = \case
        ForAllT loc var a -> Fix $ ForAllT loc (f var) a
        MonoT ty          -> Fix $ MonoT $ fmap f ty

instance Functor (Type a) where
  fmap f (Type x) = Type $ foldFix go x
    where
      go = \case
        VarT loc name      -> Fix $ VarT loc $ f name
        ConT loc name args -> Fix $ ConT loc (f name) args
        ArrowT loc a b     -> Fix $ ArrowT loc a b
        TupleT loc as      -> Fix $ TupleT loc as
        ListT loc a        -> Fix $ ListT loc a

instance HasLoc (Signature loc var) where
  type Loc (Signature loc var) = loc
  getLoc (Signature x) = foldFix go x
    where
      go = \case
        MonoT ty        -> getLoc ty
        ForAllT loc _ _ -> loc

-- | Mapping over source code locations. It's like functor but for source code locations.
class LocFunctor f where
  mapLoc :: (locA -> locB) -> f locA var -> f locB var

-- | Sets the source code location to given value for all expressions in the functor.
setLoc :: LocFunctor f => loc -> f locA v -> f loc v
setLoc loc = mapLoc (const loc)

instance LocFunctor Type where
  mapLoc f (Type x) = Type $ foldFix go x
    where
      go = \case
        VarT loc name      -> Fix $ VarT (f loc) name
        ConT loc name args -> Fix $ ConT (f loc) name args
        ArrowT loc a b     -> Fix $ ArrowT (f loc) a b
        TupleT loc as      -> Fix $ TupleT (f loc) as
        ListT loc a        -> Fix $ ListT (f loc) a

instance LocFunctor Signature where
  mapLoc f (Signature x) = Signature $ foldFix go x
    where
      go = \case
        ForAllT loc var a -> Fix $ ForAllT (f loc) var a
        MonoT ty          -> Fix $ MonoT $ mapLoc f ty

-- | Mapps over all types that are contained in the value
class TypeFunctor f where
  mapType :: (Type loc var -> Type loc var) -> f loc var -> f loc var

instance TypeFunctor Type where
  mapType f = f

-- | 'forAllT' @x t@ universally quantifies @x@ in @t@.
forAllT :: loc -> v -> Signature loc v -> Signature loc v
forAllT loc x (Signature t) = Signature $ Fix $ ForAllT loc x t

-- | 'monoT' @t@ lifts a monomorophic type @t@ to a polymorphic one.
monoT :: Type loc src -> Signature loc src
monoT = Signature . Fix . MonoT

-- | Converts simple type to signature with all free variables set to schematic.
typeToSignature :: (Eq loc, Ord v) => Type loc v -> Signature loc v
typeToSignature ty = foldr (\(v, src) a -> forAllT src v a) (monoT ty) vs
  where
    vs = tyVarsInOrder ty

-- | Reads all type-variables.
getTypeVars :: (Ord var, HasTypeVars f) => f src var -> [(src, var)]
getTypeVars = varSetToList . tyVars

--------------------------------------------------------------------------------

-- | The class of types which have free type variables.
class HasTypeVars f where
    -- | 'tyVars' @t@ calculates the set of free type variables in @t@.
    tyVars :: Ord var => f src var -> VarSet src var

    -- | 'tyVarsInOrder' @t@ is like 'tyVars' @t@, except that the type
    -- variables are returned in the order in which they are encountered.
    tyVarsInOrder :: (Eq src, Ord var) => f src var -> [(var, src)]

instance HasTypeVars Type where
    tyVars = foldFix go . unType
      where
        go = \case
          VarT loc v    -> VarSet $ M.singleton v loc
          ConT _ _ args -> mconcat args
          ArrowT _ a b  -> mappend a b
          TupleT _ as   -> mconcat as
          ListT _ a     -> a

    tyVarsInOrder = nubOrdOn fst . foldFix go . unType
      where
        go = \case
          VarT loc var -> [(var, loc)]
          ConT _ _ as  -> mconcat as
          ArrowT _ a b -> mappend a b
          TupleT _ as  -> mconcat as
          ListT _ a    -> a


instance HasTypeVars Signature where
    tyVars = foldFix go . unSignature
      where
        go = \case
          MonoT t       -> tyVars t
          ForAllT _ x t -> VarSet $ M.delete x $ unVarSet t

    tyVarsInOrder = nubOrdOn fst . foldFix go . unSignature
      where
        go = \case
          MonoT t         -> tyVarsInOrder t
          ForAllT src x t -> L.deleteBy ((==) `on` fst) (x, src) t

--------------------------------------------------------------------------------

-- | Set with information on source code locations.
-- We use it to keep the source code locations for variables.
newtype VarSet src var = VarSet { unVarSet :: Map var src }
  deriving (Semigroup, Monoid)

-- | 'difference' for @VarSet@'s
differenceVarSet :: Ord var => VarSet src var -> VarSet src var -> VarSet src var
differenceVarSet (VarSet a) (VarSet b) = VarSet $ a `M.difference` b

-- | Converts varset to list.
varSetToList :: VarSet src var -> [(src, var)]
varSetToList (VarSet m) = fmap swap $ M.toList m

-- | Checks membership of the item in the varset.
memberVarSet :: Ord var => var -> VarSet src var -> Bool
memberVarSet k (VarSet m) = M.member k m

--------------------------------------------------------------------------------

-- | Removes all information on variables in the type.
-- it gets the thing that we store in constructor @MonoT@.
stripSignature :: Signature src var -> Type src var
stripSignature = foldFix go . unSignature
  where
    go = \case
      ForAllT _ _ r -> r
      MonoT ty -> ty

-- | Separates type variables from type definition.
splitSignature :: Signature loc var -> ([var], Type loc var)
splitSignature (Signature x) = flip foldFix x $ \case
  ForAllT _ v (vs, t) -> (v:vs, t)
  MonoT t             -> ([], t)

-- | If underlying type is a function with several arguments it extracts its list of arguments and result type.
extractFunType :: Type loc var -> ([Type loc var], Type loc var)
extractFunType ty = case extractArrow ty of
  Just (lhs, rhs) ->
    let (args, rhs') = extractFunType rhs
    in  (lhs : args, rhs')
  Nothing         -> ([], ty)

-- | If underlying type is an arrow it extracts its single argument and result type.
extractArrow :: Type loc var -> Maybe (Type loc var, Type loc var)
extractArrow (Type (Fix x)) = case x of
  ArrowT _ a b -> Just (Type a, Type b)
  _            -> Nothing

------------------------------------

-- | Checks that type is monomorphic.
isMono :: Type loc var -> Bool
isMono (Type t) = getAll $ flip foldFix t $ \case
  VarT _ _  -> All False
  other     -> fold other

-- | Checks that type is polymorphic.
isPoly :: Type loc var -> Bool
isPoly = not . isMono
