-- | Defines type-inference algorithm.
--
-- For type inference we have to define instance of the Lang class:
--
-- > data NoPrim
-- >   deriving (Show)
-- >
-- > data TestLang
-- >
-- > instance Lang TestLang where
-- >   type Src  TestLang = ()              -- ^ define type for source code locations
-- >   type Var  TestLang = Text            -- ^ define type for variables
-- >   type Prim TestLang = NoPrim          -- ^ define type for primitive operators
-- >   getPrimType _ _ = error "No primops"   -- ^ reports types for primitives
--
-- Also we define context for type inference that holds types for all known variables
-- Often it defines types for all global variables or functions that are external.
--
-- > context = Context $ Map.fromList [...]
--
-- Then we can use inference to derive type for given term with @inferType@ or
-- we can derive types for all sub-expressions of given term with @inferTerm@.
-- See module in the test "TM.Infer" for examples of the usage.
--
-- > termI,termK :: Term NoPrim () Text
-- >
-- > -- I combinator
-- > termI = lamE () "x" $ varE () "x"
-- > -- K combinator
-- > termK = lamE () "x" $ lamE () "y" $ varE () "x"
-- >
-- > -- Let's infer types
-- > typeI = inferType mempty termI
-- > typeK = inferType mempty termK
--
-- There are functions to check that two types unify (@unifyTypes@) or that one type
-- is subtype of another one (@subtypeOf@).
module Type.Check.HM.Infer(
  -- * Context
    Context(..)
  , insertCtx
  , lookupCtx
  , ContextOf
  -- * Inference
  , inferType
  , inferTerm
  , inferTypeList
  , inferTermList
  , subtypeOf
  , unifyTypes
  -- * Utils
  , closeSignature
  , printInfer
) where

import Control.Monad.Identity
import Control.Monad.Writer.Strict

import Control.Applicative
import Control.Arrow (second)
import Control.Monad.Except
import Control.Monad.State.Strict

import Data.Bifunctor (bimap)
import Data.Fix
import Data.Function (on)
import Data.Map.Strict (Map)
import Data.Maybe

import Type.Check.HM.Lang
import Type.Check.HM.Term
import Type.Check.HM.Subst
import Type.Check.HM.Type
import Type.Check.HM.TypeError
import Type.Check.HM.TyTerm
import Type.Check.HM.Pretty

import qualified Data.Map.Strict as M
import qualified Data.Set as S
import qualified Data.List as L

-- | Context holds map of proven signatures for free variables in the expression.
newtype Context loc v = Context { unContext :: Map v (Signature loc v) }
  deriving (Show, Eq, Semigroup, Monoid)

-- | Type synonym for context.
type ContextOf q = Context (Src q) (Var q)

instance CanApply Context where
  apply subst = Context . fmap (apply subst) . unContext

-- | Insert signature into context
insertCtx :: Ord v => v -> Signature loc v ->  Context loc v -> Context loc v
insertCtx v sign (Context ctx) = Context $ M.insert v sign ctx

-- | Lookup signature by name in the context of inferred terms.
lookupCtx :: Ord v => v -> Context loc v -> Maybe (Signature loc v)
lookupCtx v (Context ctx) = M.lookup v ctx

-- | Wrapper with ability to generate fresh names
data Name v
  = Name v
  | FreshName !Int
  deriving (Show, Eq, Ord)

fromNameVar :: Name v -> Either (TypeError loc v) v
fromNameVar = \case
  Name v      -> Right v
  FreshName _ -> Left FreshNameFound

instance IsVar a => IsVar (Name a) where
  prettyLetters = fmap Name (prettyLetters :: [a])

-- Synonyms to simplify typing
type Context' loc v = Context (Origin loc) (Name v)
type Type' loc v = Type (Origin loc) (Name v)
type Signature' loc v = Signature (Origin loc) (Name v)
type Subst' loc v = Subst (Origin loc) (Name v)
type Bind' loc v a = Bind (Origin loc) (Name v) a
type VarSet' loc v = VarSet (Origin loc) (Name v)

type ContextOf' q = Context (Origin (Src q)) (Name (Var q))
type TypeOf' q = Type (Origin (Src q)) (Name (Var q))
type TermOf' q = Term (Prim q) (Origin (Src q)) (Name (Var q))
type TyTermOf' q = TyTerm (Prim q) (Origin (Src q)) (Name (Var q))
type SignatureOf' q = Signature (Origin (Src q)) (Name (Var q))
type SubstOf' q = Subst (Origin (Src q)) (Name (Var q))
type BindOf' q a = Bind (Origin (Src q)) (Name (Var q)) a
type CaseAltOf' q = CaseAlt (Origin (Src q)) (Name (Var q))

-- | We leave in the context only terms that are truly needed.
-- To check the term we need only variables that are free in the term.
-- So we can safely remove everything else and speed up lookup times.
restrictContext :: Ord v => Term prim loc v -> Context loc v -> Context loc v
restrictContext t (Context ctx) = Context $ M.intersection ctx fv
  where
    fv = M.fromList $ fmap (, ()) $ S.toList $ freeVars t

wrapContextNames :: Ord v => Context loc v -> Context loc (Name v)
wrapContextNames = fmapCtx Name
  where
    fmapCtx f (Context m) = Context $ M.mapKeys f $ M.map (fmap f) m

wrapTermNames :: Term prim loc v -> Term prim loc (Name v)
wrapTermNames = fmap Name

markProven :: Context loc v -> Context (Origin loc) v
markProven = Context . M.map (mapLoc Proven) . unContext

markUserCode :: Term prim loc v -> Term prim (Origin loc) v
markUserCode = mapLoc UserCode

chooseUserOrigin :: Show a => Origin a -> Origin a -> a
chooseUserOrigin x y = case (x, y) of
  (UserCode a, _) -> a
  (_, UserCode a) -> a
  _               -> fromOrigin x

-- | Type-tag for source locations to distinguish proven types from those
-- that have to be checked.
--
-- We use it on unification failure to show source locations in the user code and not in the
-- expression that is already was proven.
data Origin a
  = Proven a
  -- ^ Proven source code location
  | UserCode a
  -- ^ User source code (we type-check it)
  deriving (Show, Functor)

fromOrigin :: Origin a -> a
fromOrigin = \case
  Proven   a -> a
  UserCode a -> a

instance Eq a => Eq (Origin a) where
  (==) = (==) `on` fromOrigin

instance Ord a => Ord (Origin a) where
  compare = compare `on` fromOrigin

instance HasLoc a => HasLoc (Origin a) where
  type Loc (Origin a) = Loc a
  getLoc = getLoc . fromOrigin

-- | Type-inference monad.
-- Contains integer counter for fresh variables and possibility to report type-errors.
newtype InferM loc var a = InferM (StateT Int (Writer [TypeError loc (Name var)]) a)
  deriving (Functor, Applicative, Monad, MonadState Int, MonadWriter [TypeError loc (Name var)])

-- | Runs inference monad.
runInferM :: InferM loc var a -> Either [TypeError loc (Name var)] a
runInferM (InferM m) = case runWriter $ evalStateT m 0 of
  (res, []) -> Right res
  (_, errs) -> Left errs

type InferOf q = InferM (Src q) (Var q) (Out (Prim q) (Src q) (Var q))

-- | Type-inference function.
-- We provide a context of already proven type-signatures and term to infer the type.
inferType :: Lang q => ContextOf q -> TermOf q -> Either [ErrorOf q] (TypeOf q)
inferType ctx term = fmap termType $ inferTerm ctx term

-- | Infers types for all subexpressions of the given term.
-- We provide a context of already proven type-signatures and term to infer the type.
inferTerm :: Lang q => ContextOf q -> TermOf q -> Either [ErrorOf q] (TyTermOf q)
inferTerm ctx term =
  case runInferM $ infer (wrapContextNames $ markProven $ restrictContext term ctx) (wrapTermNames $ markUserCode term) of
    Right (_, tyTerm) -> toTyTerm tyTerm
    Left errs -> Left $ fmap (fromTypeErrorNameVar . normaliseType) errs
  where
    toTyTerm = either (Left . pure) Right . fromTyTermNameVar . normaliseType . mapLoc fromOrigin

type Out prim loc var = ( Subst (Origin loc) (Name var)
                        , TyTerm prim (Origin loc) (Name var)
                        )

-- | Infers types for bunch of terms. Terms can be recursive and not-sorted by depndencies.
inferTermList :: Lang q => ContextOf q -> [Bind (Src q) (Var q) (TermOf q)] -> Either [ErrorOf q] [Bind (Src q) (Var q) (TyTermOf q)]
inferTermList ctx defs = case defs of
  []  -> pure []
  d:_ ->
    let topLoc = bind'loc d
    in  fmap fromLetExpr $ inferTerm ctx (toLetExpr topLoc defs)
  where
    toLetExpr loc ds = letRecE loc (fmap toBind ds) (bottomE loc)

    fromLetExpr = \case
      (TyTerm (Fix (Ann _ (LetRec _ bs _)))) -> fmap fromBind bs
      _                                      -> error "Imposible happened. Found non let-rec expression"

    toBind = id
    fromBind = fmap TyTerm

-- | Infers types for bunch of terms. Terms can be recursive and not-sorted by depndencies.
-- It returns only top-level types for all terms.
inferTypeList :: Lang q => ContextOf q -> [Bind (Src q) (Var q) (TermOf q)] -> Either [ErrorOf q] [Bind (Src q) (Var q) (TypeOf q)]
inferTypeList ctx defs = fmap (fmap (fmap termType)) $ inferTermList ctx defs

infer :: Lang q => ContextOf' q -> TermOf' q -> InferOf q
infer ctx (Term (Fix x)) = case x of
  Var loc v           -> inferVar ctx loc v
  Prim loc p          -> inferPrim loc p
  App loc a b         -> inferApp ctx loc (Term a) (Term b)
  Lam loc v r         -> inferLam ctx loc v (Term r)
  Let loc v a         -> inferLet ctx loc (fmap Term v) (Term a)
  LetRec loc vs a     -> inferLetRec ctx loc (fmap (fmap Term) vs) (Term a)
  AssertType loc a ty -> inferAssertType ctx loc (Term a) ty
  Constr loc ty tag   -> inferConstr loc ty tag
  Case loc e alts     -> inferCase ctx loc (Term e) (fmap (fmap Term) alts)
  Bottom loc          -> inferBottom loc

retryWithBottom :: Lang q => TypeError (Src q) (Name (Var q)) -> Origin (Src q) -> InferOf q
retryWithBottom err loc = do
  tell [err]
  inferBottom loc

inferVar :: Lang q => ContextOf' q -> Origin (Src q) -> Name (Var q) -> InferOf q
inferVar ctx loc v = {- trace (unlines ["VAR", ppShow ctx, ppShow v]) $ -}
  case M.lookup v (unContext ctx) of
    Nothing  -> retryWithBottom (NotInScopeErr (fromOrigin loc) v) loc
    Just sig -> do ty <- newInstance $ setLoc loc sig
                   return (mempty, tyVarE ty loc v)

inferPrim :: Lang q => Origin (Src q) -> Prim q -> InferOf q
inferPrim loc prim =
  return (mempty, tyPrimE ty loc prim)
  where
    ty = fmap Name $ mapLoc UserCode $ getPrimType (fromOrigin loc) prim

inferApp :: Lang q => ContextOf' q -> Origin (Src q) -> TermOf' q -> TermOf' q -> InferOf q
inferApp ctx loc f a = {- fmap (\res -> trace (unlines ["APP", ppCtx ctx, ppShow' f, ppShow' a, ppShow' $ snd res]) res) $-} do
  tvn <- fmap (varT loc) $ freshVar
  res <- inferTerms ctx [f, a]
  case res of
    (phi, [(tf, f'), (ta, a')]) -> case unify phi tf (arrowT loc ta tvn) of
      Left err    -> retryWithBottom err loc
      Right subst -> let ty   = apply subst tvn
                         term = tyAppE ty loc (apply subst f') (apply subst a')
                     in  pure (subst, term)

    _               -> error "Impossible has happened!"

inferLam :: Lang q => ContextOf' q -> Origin (Src q) -> Name (Var q) -> TermOf' q -> InferOf q
inferLam ctx loc x body = do
  tvn <- freshVar
  (phi, bodyTyTerm) <- infer (ctx1 tvn) body
  let ty = arrowT loc (apply phi (varT loc tvn)) (termType bodyTyTerm)
  return (phi, tyLamE ty loc x bodyTyTerm)
  where
    ctx1 tvn = insertCtx x (newVar loc tvn) ctx

inferLet :: Lang q => ContextOf' q -> Origin (Src q) -> BindOf' q (TermOf' q) -> TermOf' q -> InferOf q
inferLet ctx loc v body = do
  (phi, rhsTyTerm) <- infer ctx $ bind'rhs v
  let tBind = termType rhsTyTerm
  ctx1 <- addDecls [fmap (const tBind) v] (apply phi ctx)
  (subst, bodyTerm) <- infer ctx1 body
  let subst1 = phi <> subst
      tyBind = v { bind'rhs = apply subst1 rhsTyTerm }
  return ( subst1
         , apply subst1 $ tyLetE (termType bodyTerm) loc tyBind bodyTerm
         )

inferLetRec :: forall q . Lang q
  => ContextOf' q -> Origin (Src q) -> [BindOf' q (TermOf' q)] -> TermOf' q
  -> InferOf q
inferLetRec ctx topLoc vs body = do
  lhsCtx <- getTypesLhs vs
  (phi, rhsTyTerms) <- inferTerms (ctx <> Context (M.fromList lhsCtx)) exprBinds
  let (tBinds, bindsTyTerms) = unzip rhsTyTerms
  case unifyRhs ctx lhsCtx phi tBinds of
    Right (ctx1, lhsCtx1, subst) -> inferBody bindsTyTerms ctx1 lhsCtx1 subst body
    Left err                     -> retryWithBottom err topLoc
  where
    exprBinds = fmap bind'rhs vs
    locBinds  = fmap bind'loc vs

    getTypesLhs :: [BindOf' q (TermOf' q)] -> InferM (Src q) (Var q) [(Name (Var q), SignatureOf' q)]
    getTypesLhs lhs = mapM (\b -> fmap ((bind'lhs b, ) . newVar (bind'loc b)) freshVar) lhs

    unifyRhs context lhsCtx phi tBinds =
      fmap (\subst -> (context1, lhsCtx1, subst)) $ unifyl phi ts tBinds
      where
        context1 = apply phi context
        lhsCtx1  = fmap (second $ apply phi) lhsCtx
        ts = fmap (oldBvar . snd) lhsCtx1

    oldBvar = foldFix go . unSignature
      where
        go  = \case
          MonoT t       -> t
          ForAllT _ _ t -> t

    inferBody termBinds context lhsCtx subst expr = do
      ctx1 <- addDecls (zipWith (\loc (v, ty) -> Bind loc v ty) locBinds $ fmap (second $ oldBvar . apply subst) lhsCtx) $ apply subst context
      (phi, bodyTerm) <- infer ctx1 expr
      let tyBinds = zipWith (\bind rhs -> bind { bind'rhs = rhs }) vs termBinds
      return (subst <> phi, tyLetRecE (termType bodyTerm) topLoc tyBinds bodyTerm)

inferAssertType :: Lang q => ContextOf' q -> Origin (Src q) -> TermOf' q -> TypeOf' q -> InferOf q
inferAssertType ctx loc a ty = do
  (phi, aTyTerm) <- infer ctx a
  case genSubtypeOf phi ty (termType aTyTerm) of
    Right subst -> do
      let subst' = phi <> subst
      return (subst', apply subst' $ tyAssertTypeE loc aTyTerm ty)
    Left err -> retryWithBottom err loc

inferConstr :: Lang q => Origin (Src q) -> TypeOf' q -> Name (Var q) -> InferOf q
inferConstr loc ty tag = do
  vT <- newInstance $ typeToSignature ty
  return (mempty, tyConstrE loc vT tag)

inferCase :: forall q . Lang q
  => ContextOf' q -> Origin (Src q) -> TermOf' q -> [CaseAltOf' q (TermOf' q)]
  -> InferOf q
inferCase ctx loc e caseAlts = do
  (phi, tyTermE) <- infer ctx e
  (psi, tRes, tyAlts) <- inferAlts phi (termType tyTermE) $ caseAlts
  return ( psi
         , apply psi $ tyCaseE tRes loc (apply psi tyTermE) $ fmap (applyAlt psi) tyAlts)
  where
    inferAlts :: SubstOf' q -> TypeOf' q -> [CaseAltOf' q (TermOf' q)] -> InferM (Src q) (Var q) (SubstOf' q, TypeOf' q, [CaseAltOf' q (TyTermOf' q)])
    inferAlts substE tE alts =
      fmap (\(subst, _, tRes, as) -> (subst, tRes, L.reverse as)) $ foldM go (substE, tE, tE, []) alts
      where
        go initSt@(subst, tyTop, _, res) alt = do
          (phi, tRes, alt1) <- inferAlt (applyAlt subst alt)
          let subst1 = subst <> phi
          case unify subst1 (apply subst1 tyTop) (apply subst1 $ caseAlt'constrType alt1) of
            Right subst2 -> pure (subst2, apply subst2 tyTop, apply subst2 tRes, applyAlt subst2 alt1 : res)
            Left err     -> do
              tell [err]
              pure initSt

    inferAlt :: CaseAltOf' q (TermOf' q) -> InferM (Src q) (Var q) (SubstOf' q, TypeOf' q, CaseAltOf' q (TyTermOf' q))
    inferAlt preAlt = do
      alt <- newCaseAltInstance preAlt
      let argVars = fmap  (\ty -> (snd $ typed'value ty, (fst $ typed'value ty, typed'type ty))) $ caseAlt'args alt
          ctx1 = Context (M.fromList $ fmap (second $ monoT . snd) argVars) <> ctx
      (subst, tyTermRhs) <- infer ctx1 $ caseAlt'rhs alt
      let args = fmap (\(v, (argLoc, tv)) -> Typed (apply subst tv) (argLoc, v)) argVars
          alt' = alt
                  { caseAlt'rhs = tyTermRhs
                  , caseAlt'args = args
                  , caseAlt'constrType = apply subst $ caseAlt'constrType alt
                  }
      return (subst, termType tyTermRhs, alt')

    newCaseAltInstance :: CaseAltOf' q (TermOf' q) -> InferM (Src q) (Var q) (CaseAltOf' q (TermOf' q))
    newCaseAltInstance alt = do
      tv <- newInstance $ typeToSignature $ getCaseType alt
      let (argsT, resT)= splitFunT tv
      return $ alt
        { caseAlt'constrType = resT
        , caseAlt'args = zipWith (\aT ty -> ty { typed'type = aT }) argsT $ caseAlt'args alt
        }

    getCaseType :: CaseAltOf' q (TermOf' q) -> TypeOf' q
    getCaseType CaseAlt{..} = funT (fmap typed'type caseAlt'args) caseAlt'constrType

    splitFunT :: TypeOf' q -> ([TypeOf' q], TypeOf' q)
    splitFunT arrT = go [] arrT
      where
        go argsT (Type (Fix t)) = case t of
          ArrowT _loc a b -> go (Type a : argsT) (Type b)
          other           -> (reverse argsT, Type $ Fix other)


    funT :: [TypeOf' q] -> TypeOf' q -> TypeOf' q
    funT argsT resT = foldr (\a b -> arrowT (getLoc a) a b) resT argsT

    applyAlt subst alt@CaseAlt{..} = alt
      { caseAlt'constrType = apply subst caseAlt'constrType
      , caseAlt'args       = fmap applyTyped caseAlt'args
      , caseAlt'rhs        = apply subst caseAlt'rhs
      }
      where
        applyTyped ty@Typed{..} = ty { typed'type = apply subst $ typed'type }

inferBottom :: Lang q => Origin (Src q) -> InferOf q
inferBottom loc = do
  ty <- fmap (varT loc) freshVar
  return (mempty, tyBottomE ty loc)

newInstance :: IsVar v => Signature loc (Name v) -> InferM loc' v (Type loc (Name v))
newInstance = fmap (uncurry apply) . foldFixM go . unSignature
  where
    go = \case
      MonoT ty -> return (mempty, ty)
      ForAllT loc v (Subst m, ty) -> fmap (\nv -> (Subst $ M.insert v (varT loc nv) m, ty)) freshVar

newVar :: loc -> v -> Signature loc v
newVar loc tvn = monoT $ varT loc tvn

freshVar :: IsVar v => InferM loc v (Name v)
freshVar = do
  n <- get
  put $ n + 1
  return $ FreshName n

inferTerms :: Lang q
  => ContextOf' q
  -> [TermOf' q]
  -> InferM (Src q) (Var q) (SubstOf' q, [(TypeOf' q, TyTermOf' q)])
inferTerms ctx ts = case ts of
  []   -> return $ (mempty, [])
  a:as -> do
    (phi, termA) <- infer ctx a
    let ta = termType termA
    (psi, tas) <- inferTerms (apply phi ctx) as
    return ( phi <> psi
           , (apply psi ta, apply psi termA) : tas
           )

-- | Unification function. Checks weather two types unify.
-- First argument is current substitution.
unify :: (IsVar v, Show loc)
  => Subst' loc v
  -> Type' loc v
  -> Type' loc v
  -> Either (TypeError loc (Name v)) (Subst' loc v)
unify phi (Type (Fix x)) (Type (Fix y)) = {- trace (unlines ["UNIFY", ppShow tx, ppShow ty]) $ -}
  case (x, y) of
    (VarT loc tvn, t) ->
        let phiTvn = applyVar phi loc tvn
            phiT   = apply phi (Type (Fix t))
        in  if phiTvn `eqIgnoreLoc` varT loc tvn
              then extend phi loc tvn phiT
              else unify phi phiTvn phiT
    (a, VarT locB v) -> unify phi (varT locB v) (Type $ Fix a) -- (conT locA name $ fmap Type ts)
    (ConT locA n xs, ConT locB m ys) ->
      if n == m
        then unifyl phi (fmap Type xs) (fmap Type ys)
        else unifyErr locA locB
    (ArrowT _ a1 a2, ArrowT _ b1 b2) -> unifyl phi (fmap Type [a1, a2]) (fmap Type [b1, b2])
    (TupleT locA xs, TupleT locB ys) ->
      if length xs == length ys
        then unifyl phi (fmap Type xs) (fmap Type ys)
        else unifyErr locA locB
    (ListT _ a, ListT _ b) -> unify phi (Type a) (Type b)
    (a, b) -> unifyErr (getLoc $ Type $ Fix a) (getLoc $ Type $ Fix b)
  where
    unifyErr locA locB = throwError $
      UnifyErr (chooseUserOrigin locA locB)
               (mapLoc fromOrigin $ Type (Fix x))
               (mapLoc fromOrigin $ Type (Fix y))

eqIgnoreLoc :: Eq v => Type loc v -> Type loc v -> Bool
eqIgnoreLoc = (==) `on` mapLoc (const ())

applyVar :: IsVar v => Subst' loc v -> Origin loc -> Name v -> Type' loc v
applyVar (Subst subst) loc v = fromMaybe (varT loc v) $ M.lookup v subst

extend
  :: (IsVar v, MonadError (TypeError loc (Name v)) m)
  => Subst' loc v -> Origin loc -> Name v -> Type' loc v -> m (Subst' loc v)
extend phi loc tvn ty
  | varT loc tvn `eqIgnoreLoc` ty = return phi
  | memberVarSet tvn (tyVars ty)  = throwError $ OccursErr (fromOrigin loc) (mapLoc fromOrigin ty)
  | otherwise                     = return $ phi <> delta tvn ty

unifyl :: (IsVar v, Show loc)
  => Subst' loc v
  -> [Type' loc v]
  -> [Type' loc v]
  -> Either (TypeError loc (Name v)) (Subst' loc v)
unifyl subst as bs = foldr go (return subst) $ zip as bs
  where
    go (a, b) eSubst = (\t -> unify t a b) =<< eSubst

-- | Checks if first argument one type is subtype of the second one.
subtypeOf :: (IsVar v, Show loc, Eq loc)
  => Type loc v -> Type loc v -> Either (TypeError loc v) (Subst loc v)
subtypeOf a b =
  join $ bimap (fromTypeErrorNameVar . normaliseType) (fromSubstNameVar . fromSubstOrigin) $
    genSubtypeOf mempty (fmap Name $ mapLoc Proven a) (fmap Name $ mapLoc UserCode b)

genSubtypeOf :: (IsVar v, Show loc)
  => Subst' loc v
  -> Type' loc v
  -> Type' loc v
  -> Either (TypeError loc (Name v)) (Subst' loc v)
genSubtypeOf phi tx@(Type (Fix x)) ty@(Type (Fix y)) = case (x, y) of
  (_, VarT _ _) -> unify phi tx ty
  (ConT locA n xs, ConT locB m ys) ->
    if n == m
      then subtypeOfL phi (fmap Type xs) (fmap Type ys)
      else subtypeErr locA locB
  (ArrowT _ a1 a2, ArrowT _ b1 b2) -> subtypeOfL phi (fmap Type [a1, a2]) (fmap Type [b1, b2])
  (TupleT locA as, TupleT locB bs) ->
    if length as == length bs
      then subtypeOfL phi (fmap Type as) (fmap Type bs)
      else subtypeErr locA locB
  (ListT _ a, ListT _ b) -> genSubtypeOf phi (Type a) (Type b)
  (VarT locA _, _) -> subtypeErr locA (getLoc ty)
  _ -> subtypeErr (getLoc tx) (getLoc ty)
  where
    subtypeErr locA locB = throwError
      $ SubtypeErr (chooseUserOrigin locA locB) (mapLoc fromOrigin tx) (mapLoc fromOrigin ty)

subtypeOfL :: (IsVar v, Show loc)
  => Subst' loc v
  -> [Type' loc v]
  -> [Type' loc v]
  -> Either (TypeError loc (Name v)) (Subst' loc v)
subtypeOfL subst as bs = foldr go (return subst) $ zip as bs
  where
    go (a, b) eSubst = (\t -> genSubtypeOf t a b) =<< eSubst

addDecls :: IsVar v
  => [Bind (Origin loc) (Name v) (Type' loc v)]
  -> Context' loc v
  -> InferM loc v (Context' loc v)
addDecls vs ctx =
  foldM  (\c b -> addDecl unknowns b c) ctx vs
  where
    unknowns = foldMap tyVars $ unContext ctx

addDecl :: forall loc v . IsVar v
  => VarSet' loc v
  -> Bind' loc v (Type' loc v)
  -> Context' loc v
  -> InferM loc v (Context' loc v)
addDecl unknowns b ctx = do
  scheme <- toScheme unknowns (bind'rhs b)
  return $ Context . M.insert (bind'lhs b) scheme . unContext $ ctx
  where
    toScheme :: VarSet' loc v -> Type' loc v -> InferM loc v (Signature' loc v)
    toScheme uVars ty = do
      (subst, newVars) <- fmap (\xs -> (toSubst xs, fmap (\((loc, _), v) -> (loc, v)) xs)) $
          mapM (\sv -> fmap ((sv, )) freshVar) $ varSetToList schematicVars
      return $ foldr (uncurry forAllT) (monoT (apply subst ty)) newVars
      where
        schematicVars = tyVars ty `differenceVarSet` uVars

    toSubst = Subst . M.fromList . fmap (\((loc, v), a) -> (v, varT loc a))

-------------------------------------------------------
-- pretty letters for variables in the result type

-- | Converts variable names to human-readable format.
normaliseType :: (HasTypeVars m, CanApply m, IsVar v, Show loc, Eq loc) => m loc (Name v) -> m loc (Name v)
normaliseType ty = apply (normaliseSubst ty) ty

normaliseSubst :: (HasTypeVars m, Show loc, Eq loc, IsVar v) => m loc v -> Subst loc v
normaliseSubst x =
  Subst $ M.fromList $
    zipWith (\(nameA, loc) nameB -> (nameA, varT loc nameB)) (tyVarsInOrder x) prettyLetters

------------------------------------------------
--

-- | Checks weather two types unify. If they do it returns substitution that unifies them.
unifyTypes :: (Show loc, IsVar v, Eq loc) => Type loc v -> Type loc v -> Either (TypeError loc v) (Subst loc v)
unifyTypes a b =
  join $ bimap (fromTypeErrorNameVar . normaliseType) (fromSubstNameVar . fromSubstOrigin) $
    unify mempty (fmap Name $ mapLoc Proven a) (fmap Name $ mapLoc UserCode b)

------------------------------------------------
-- recover name and origin wrappers

fromTypeErrorNameVar :: TypeError loc (Name var) -> TypeError loc var
fromTypeErrorNameVar = either id id . \case
    OccursErr loc ty     -> fmap (OccursErr loc) (fromTypeNameVar ty)
    UnifyErr loc tA tB   -> liftA2 (UnifyErr loc) (fromTypeNameVar tA) (fromTypeNameVar tB)
    SubtypeErr loc tA tB -> liftA2 (SubtypeErr loc) (fromTypeNameVar tA) (fromTypeNameVar tB)
    NotInScopeErr loc v  -> fmap (NotInScopeErr loc) $ fromNameVar v
    EmptyCaseExpr loc    -> pure $ EmptyCaseExpr loc
    FreshNameFound       -> pure FreshNameFound

fromTypeNameVar :: Type loc (Name var) -> Either (TypeError loc var) (Type loc var)
fromTypeNameVar (Type x) = fmap Type $ foldFixM go x
  where
    go :: TypeF loc (Name var) (Fix (TypeF loc var)) -> Either (TypeError loc var) (Fix (TypeF loc var))
    go = \case
      VarT loc v     -> fmap (Fix . VarT loc) $ fromNameVar v
      ConT loc v as  -> fmap (\con -> Fix $ ConT loc con as) $ fromNameVar v
      ArrowT loc a b -> pure $ Fix $ ArrowT loc a b
      TupleT loc as  -> pure $ Fix $ TupleT loc as
      ListT loc as   -> pure $ Fix $ ListT loc as

fromTyTermNameVar :: TyTerm prim loc (Name var) -> Either (TypeError loc var) (TyTerm prim loc var)
fromTyTermNameVar (TyTerm x) = fmap TyTerm $ foldFixM go x
  where
    go (Ann annTy term) = liftA2 (\t val -> Fix $ Ann t val) (fromTypeNameVar annTy) $ case term of
      Var loc v           -> fmap (Var loc) $ fromNameVar v
      Prim loc p          -> pure $ Prim loc p
      App loc a b         -> pure $ App loc a b
      Lam loc v a         -> fmap (\arg -> Lam loc arg a) $ fromNameVar v
      Let loc bind a      -> fmap (\b -> Let loc b a) $ fromBind bind
      LetRec loc binds a  -> fmap (\bs -> LetRec loc bs a) $ mapM fromBind binds
      AssertType loc a ty -> fmap (AssertType loc a) $ fromTypeNameVar ty
      Constr loc t v      -> liftA2 (Constr loc) (fromTypeNameVar t) (fromNameVar v)
      Bottom loc          -> pure $ Bottom loc
      Case loc e alts     -> fmap (Case loc e) $ mapM fromAlt alts

    fromBind b = fmap (\a -> b { bind'lhs = a }) $ fromNameVar $ bind'lhs b

    fromAlt alt@CaseAlt{..} =
      liftA3 (\tag args constrType -> alt { caseAlt'tag = tag, caseAlt'args = args, caseAlt'constrType = constrType })
        (fromNameVar caseAlt'tag)
        (mapM fromTyped caseAlt'args)
        (fromTypeNameVar caseAlt'constrType)

    fromTyped Typed{..} = liftA2 Typed (fromTypeNameVar typed'type) (mapM fromNameVar typed'value)

fromSubstNameVar :: Ord v => Subst loc (Name v) -> Either (TypeError loc v) (Subst loc v)
fromSubstNameVar (Subst m) = fmap (Subst . M.fromList) $ mapM uncover $ M.toList m
  where
    uncover (v, ty) = liftA2 (,) (fromNameVar v) (fromTypeNameVar ty)

fromSubstOrigin :: Ord v => Subst (Origin loc) v -> Subst loc v
fromSubstOrigin = Subst . M.map (mapLoc fromOrigin) . unSubst

-- | Substitutes all type arguments with given types.
closeSignature :: Ord var => [Type loc var] -> Signature loc var -> Type loc var
closeSignature argTys sig = apply (Subst $ M.fromList $ zip argNames argTys) monoTy
  where
    (argNames, monoTy) = splitSignature sig

----------------------------------------------------------------------------------

-- | Pretty printer for result of type-inference
printInfer :: (PrettyLang q) => (Either [ErrorOf q] (TypeOf q)) -> IO ()
printInfer = \case
  Right ty  -> putStrLn $ show $ pretty ty
  Left errs -> mapM_ (putStrLn . (++ "\n") . show . pretty) errs


