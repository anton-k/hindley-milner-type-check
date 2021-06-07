-- | This module contains type annotations for terms of the language.
module Type.Check.HM.TyTerm(
    Ann(..)
  , TyTerm(..)
  , termType
  , termSignature
  , tyVarE
  , tyPrimE
  , tyAppE
  , tyLamE
  , tyLetE
  , tyLetRecE
  , tyAssertTypeE
  , tyCaseE
  , tyConstrE
  , tyBottomE
  , mapType
) where

import Control.Arrow

import Data.Fix
import Data.Containers.ListUtils (nubOrdOn)
import Data.Foldable
import Data.Eq.Deriving
import Data.Ord.Deriving
import Text.Show.Deriving

import Type.Check.HM.Subst
import Type.Check.HM.Type
import Type.Check.HM.Term

import qualified Data.DList as D

-- | Type to annotate nodes of AST.
-- We use it for type annotations.
data Ann note f a = Ann
  { ann'note  :: note
  , ann'value :: f a
  } deriving (Show, Eq, Functor, Foldable, Traversable)

$(deriveShow1 ''Ann)
$(deriveEq1   ''Ann)
$(deriveOrd1  ''Ann)


-- | Terms with type annotations for all subexpressions.
newtype TyTerm prim loc v = TyTerm { unTyTerm :: Fix (Ann (Type loc v) (TermF prim loc v)) }
  deriving (Show, Eq)

termType :: TyTerm prim loc v -> Type loc v
termType (TyTerm (Fix (Ann ty _))) = ty

termSignature :: (Ord v, Eq loc) => TyTerm prim loc v -> Signature loc v
termSignature = typeToSignature . termType

-- tyTerm :: Type loc v -> TermF loc var (Ann () ) -> TyTerm loc var
tyTerm :: Type loc v -> TermF prim loc v (Fix (Ann (Type loc v) (TermF prim loc v))) -> TyTerm prim loc v
tyTerm ty x = TyTerm $ Fix $ Ann ty x

-- | 'varE' @loc x@ constructs a variable whose name is @x@ with source code at @loc@.
tyVarE :: Type loc var -> loc -> var -> TyTerm prim loc var
tyVarE ty loc var =  tyTerm ty $ Var loc var

-- | 'varE' @loc x@ constructs a variable whose name is @x@ with source code at @loc@.
tyPrimE :: Type loc var -> loc -> prim -> TyTerm prim loc var
tyPrimE ty loc prim =  tyTerm ty $ Prim loc prim

-- | 'appE' @loc a b@ constructs an application of @a@ to @b@ with source code at @loc@.
tyAppE :: Type loc v -> loc -> TyTerm prim loc v -> TyTerm prim loc v -> TyTerm prim loc v
tyAppE ty loc (TyTerm l) (TyTerm r) = tyTerm ty $ App loc l r

-- | 'lamE' @loc x e@ constructs an abstraction of @x@ over @e@ with source code at @loc@.
tyLamE :: Type loc v -> loc -> v -> TyTerm prim loc v -> TyTerm prim loc v
tyLamE ty loc x (TyTerm e) = tyTerm ty $ Lam loc x e

-- | 'letE' @loc binds e@ constructs a binding of @binds@ in @e@ with source code at @loc@.
-- No recursive bindings.
tyLetE :: Type loc v -> loc -> Bind loc v (TyTerm prim loc v) -> TyTerm prim loc v -> TyTerm prim loc v
tyLetE ty loc bind (TyTerm e) = tyTerm ty $ Let loc (fmap unTyTerm bind) e

-- | 'letRecE' @loc binds e@ constructs a recursive binding of @binds@ in @e@ with source code at @loc@.
tyLetRecE :: Type loc v -> loc -> [Bind loc v (TyTerm prim loc v)] -> TyTerm prim loc v -> TyTerm prim loc v
tyLetRecE ty loc binds (TyTerm e) = tyTerm ty $ LetRec loc (fmap (fmap unTyTerm) binds) e

-- | 'assertTypeE' @loc term ty@ constructs assertion of the type @ty@ to @term@.
tyAssertTypeE :: loc -> TyTerm prim loc v -> Type loc v -> TyTerm prim loc v
tyAssertTypeE loc (TyTerm a) ty = tyTerm ty $ AssertType loc a ty

-- | 'caseE' @loc expr alts@ constructs case alternatives expression.
tyCaseE :: Type loc v -> loc -> TyTerm prim loc v -> [CaseAlt loc v (TyTerm prim loc v)] -> TyTerm prim loc v
tyCaseE ty loc (TyTerm e) alts = tyTerm ty $ Case loc e $ fmap (fmap unTyTerm) alts

-- | 'constrE' @loc ty tag arity@ constructs constructor tag expression.
tyConstrE :: loc -> Type loc v -> v -> TyTerm prim loc v
tyConstrE loc ty tag = tyTerm ty $ Constr loc ty tag

-- | 'bottomE' @loc@ constructs bottom value.
tyBottomE :: Type loc v -> loc -> TyTerm prim loc v
tyBottomE ty loc = tyTerm ty $ Bottom loc

instance LocFunctor (TyTerm prim) where
  mapLoc f (TyTerm x) = TyTerm $ foldFix go x
    where
      go (Ann annTy term) = Fix $ Ann (mapLoc f annTy) $ case term of
        Var loc v    -> Var (f loc) v
        Prim loc p   -> Prim (f loc) p
        App loc a b  -> App (f loc) a b
        Lam loc v a  -> Lam (f loc) v a
        Let loc v a  -> Let (f loc) (v { bind'loc = f $ bind'loc v }) a
        LetRec loc vs a -> LetRec (f loc) (fmap (\b ->  b { bind'loc = f $ bind'loc b }) vs) a
        AssertType loc r sig -> AssertType (f loc) r (mapLoc f sig)
        Constr loc ty v -> Constr (f loc) (mapLoc f ty) v
        Case loc e alts -> Case (f loc) e (fmap (mapAlt f) alts)
        Bottom loc -> Bottom (f loc)

      mapAlt g alt@CaseAlt{..} = alt
        { caseAlt'loc  = g caseAlt'loc
        , caseAlt'args = fmap (mapTyped g) caseAlt'args
        , caseAlt'constrType = mapLoc g caseAlt'constrType
        }

      mapTyped g (Typed ty val) = Typed (mapLoc g ty) (first g val)

instance TypeFunctor (TyTerm prim) where
  mapType f (TyTerm x) = TyTerm $ foldFix go x
    where
      go (Ann ty term) = Fix $ Ann (f ty) $
        case term of
          Constr loc cty cons -> Constr loc (f cty) cons
          Case loc e alts          -> Case loc e $ fmap applyAlt alts
          other                    -> other

      applyAlt alt@CaseAlt{..} = alt
        { caseAlt'args       = fmap applyTyped caseAlt'args
        , caseAlt'constrType = f caseAlt'constrType
        }

      applyTyped ty@Typed{..} = ty { typed'type = f typed'type }

instance CanApply (TyTerm prim) where
  apply subst term = mapType (apply subst) term

instance HasTypeVars (TyTerm prim) where
  tyVars (TyTerm x) = foldFix (\(Ann ty term) -> tyVars ty <> fold term) x

  tyVarsInOrder (TyTerm x) =
    nubOrdOn fst $ D.toList $ foldFix (\(Ann ty term) -> D.fromList (tyVarsInOrder ty) <> fold term) x



