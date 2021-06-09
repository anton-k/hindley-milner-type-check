{-# OPTIONS_GHC -Wno-orphans #-}
-- | Pretty printer for types and terms.
module Type.Check.HM.Pretty(
    PrettyVar
  , FixityCtx(..)
  , PrintCons(..)
  , OpFix(..)
  , Fixity(..)
  , Pretty(..)
) where

import Data.Bool
import Data.Fix
import Data.Maybe
import Data.Text (Text)
import Data.Text.Prettyprint.Doc

import Type.Check.HM.Type
import Type.Check.HM.Term
import Type.Check.HM.TypeError

-- | Type to query fixity of infix operations in type variables.
data FixityCtx var a = FixityCtx
  { fixity'context :: var -> Maybe OpFix   -- ^ Function that provides fixity-type for a given variable
  , fixity'data    :: a                    -- ^ content
  }

-- | Ignores fixity information
noFixity :: forall v a . a -> FixityCtx v a
noFixity = FixityCtx (const Nothing)

-- | This class is useful to define the way to print special cases
-- like constructors for tuples or lists.
class PrintCons v where
  printCons :: v -> [Doc ann] -> Doc ann

instance PrintCons Int where
  printCons name args = hsep $ pretty name : args

instance PrintCons String where
  printCons name args = hsep $ pretty name : args

instance PrintCons Text where
  printCons name args = hsep $ pretty name : args

isPrefix :: (v -> Maybe OpFix) -> v -> Bool
isPrefix getFixity = isNothing . getFixity

isInfix :: (v -> Maybe OpFix) -> v -> Bool
isInfix a = not . isPrefix a

type PrettyVar a = (Pretty a, PrintCons a, IsVar a)

instance (PrettyVar v) => Pretty (Signature loc v) where
  pretty = pretty . noFixity @v

instance (PrettyVar v) => Pretty (FixityCtx v (Signature loc v)) where
  pretty (FixityCtx getFixity sign) = foldFix go $ unSignature sign
    where
      go = \case
        ForAllT _ _ r -> r
        MonoT ty      -> pretty (FixityCtx getFixity ty)

instance (PrettyVar v) => Pretty (Type loc v) where
  pretty = pretty . noFixity @v

instance (PrettyVar v) => Pretty (FixityCtx v (Type loc v)) where
  pretty (FixityCtx getFixity ty) = go False initCtx $ unType ty
    where
      go :: Bool -> FixityContext v -> Fix (TypeF loc v) -> Doc ann
      go isArrPrev ctx (Fix expr) = case expr of
        VarT _ name   -> pretty name
        ConT _ name [a, b] | isInfix getFixity name -> fromBin name a b
        ConT _ name as -> fromCon isArrPrev name as
        ArrowT _ a b -> fromArrow a b
        TupleT _ as -> fromTuple as
        ListT _ a -> fromList a
        where
          fromCon isArr name args = maybeParens (not (null args) && not isArr && needsParens getFixity ctx OpFunAp) $
            printCons name $ fmap (go False (FcRight OpFunAp)) args

          fromBin op a b = maybeParens (needsParens getFixity ctx (Op op)) $ hsep
            [ go True (FcLeft $ Op op) a
            , pretty op
            , go True (FcRight $ Op op) b
            ]

          fromArrow a b = maybeParens (needsParens getFixity ctx ArrowOp) $ hsep
            [ go True (FcLeft ArrowOp ) a
            , "->"
            , go True (FcRight ArrowOp) b
            ]

          fromTuple as = parens $ hsep $ punctuate comma $ fmap (pretty . FixityCtx getFixity . Type) as

          fromList a = brackets $ pretty $ FixityCtx getFixity $ Type a

      initCtx = FcNone

maybeParens :: Bool -> Doc ann -> Doc ann
maybeParens cond = bool id parens cond

needsParens :: (v -> Maybe OpFix) -> FixityContext v -> Operator v -> Bool
needsParens getFixity = \case
  FcNone      -> const False
  FcLeft ctx  -> fcLeft ctx
  FcRight ctx -> fcRight ctx
  where
    fcLeft ctxt op
      | comparePrec' ctxt op == PoLT = False
      | comparePrec' ctxt op == PoGT = True
      | comparePrec' ctxt op == PoNC = True
      -- otherwise the two operators have the same precedence
      | fixity' ctxt /= fixity' op = True
      | fixity' ctxt == FixLeft = False
      | otherwise = True

    fcRight ctxt op
      | comparePrec' ctxt op == PoLT = False
      | comparePrec' ctxt op == PoGT = True
      | comparePrec' ctxt op == PoNC = True
      -- otherwise the two operators have the same precedence
      | fixity' ctxt /= fixity' op = True
      | fixity' ctxt == FixRight = False
      | otherwise = True

    comparePrec' = comparePrec getFixity
    fixity' = fixity getFixity

data PartialOrdering = PoLT | PoGT | PoEQ | PoNC
  deriving Eq

-- | Defines fixity type and order of infix operation
data OpFix = OpFix
  { opFix'fixity :: !Fixity
  -- ^ fixity type
  , opFix'prec   :: !Int
  -- ^ fixity order
  }

-- | Infix operation can be left or right associative or associativity is not known.
data Fixity = FixLeft | FixRight | FixNone
  deriving Eq

data Operator v = OpFunAp | Op v | ArrowOp
  deriving (Eq, Ord)

data FixityContext v = FcNone | FcLeft (Operator v) | FcRight (Operator v)

{-
initEnv :: FixityEnv
initEnv = Map.fromList
  [ (Op "->", OpFix FixRight 2) ]
-}

getFixityEnv :: (v -> Maybe OpFix) -> Operator v -> Maybe OpFix
getFixityEnv getFixity = \case
  OpFunAp -> Nothing
  Op v    -> getFixity v
  ArrowOp -> Just $ OpFix FixRight 2

comparePrec :: (v -> Maybe OpFix) -> Operator v -> Operator v -> PartialOrdering
comparePrec getFixity a b = case (getFixityEnv getFixity a, getFixityEnv getFixity b) of
  (Just opA, Just opB) -> toPo (opFix'prec opA) (opFix'prec opB)
  _                    -> PoNC
  where
    toPo m n
      | m < n     = PoLT
      | m > n     = PoGT
      | otherwise = PoEQ


fixity :: (v -> Maybe OpFix) -> Operator v -> Fixity
fixity getFixity op = maybe FixNone opFix'fixity $ getFixityEnv getFixity op

-----------------------------------------------------------------
-- pretty terms

instance (PrettyVar v, Pretty prim) => Pretty (Term prim loc v) where
  pretty = pretty . noFixity @v

instance (PrettyVar v, Pretty prim) => Pretty (FixityCtx v (Term prim loc v)) where
  pretty (FixityCtx getFixity (Term x)) = foldFix prettyTermF x
    where
      prettyTermF = \case
        Var _ v            -> pretty v
        Prim _ p           -> pretty p
        App _ a b          -> parens $ hsep [a, b]
        Lam _ v a          -> parens $ hsep [hcat ["\\", pretty v], "->", a]
        Let _ v a          -> onLet [v] a
        LetRec _ vs a      -> onLet vs a
        AssertType _ r sig -> parens $ hsep [r, "::", pretty $ FixityCtx getFixity sig]
        Constr _ tag       -> pretty tag
        Case _ e alts      -> vcat [ hsep ["case", e, "of"], indent 4 $ vcat $ fmap onAlt alts]
        Bottom _           -> "_|_"
        where
          onLet vs body =
            vcat [ hsep ["let", indent 4 $ vcat $ fmap (\Bind{..} -> hsep [pretty bind'lhs, "=", bind'rhs]) vs]
                 , hsep ["in ", body]]

          onAlt CaseAlt{..} = hsep
            [ pretty caseAlt'tag, hsep $ fmap (pretty . snd) caseAlt'args
            , "->"
            , caseAlt'rhs ]

-----------------------------------------------------------------
-- pretty errors

instance (Pretty loc, PrettyVar var) => Pretty (TypeError loc var) where
  pretty = pretty . noFixity @var

instance (Pretty loc, PrettyVar var) => Pretty (FixityCtx var (TypeError loc var)) where
  pretty (FixityCtx getFixity tyErr) = case tyErr of
    OccursErr src name     -> err src $ hsep ["Occurs error", prettyTy name]
    UnifyErr src tyA tyB   -> err src $ hsep ["Type mismatch got", inTicks $ prettyTy tyB, "expected", inTicks $ prettyTy tyA]
    NotInScopeErr src name -> err src $ hsep ["Not in scope", pretty name]
    SubtypeErr src tyA tyB -> err src $ hsep ["Subtype error", inTicks $ prettyTy tyB, "expected", inTicks $ prettyTy tyA]
    EmptyCaseExpr src      -> err src $ "Case-expression should have at least one alternative case"
    FreshNameFound         -> "Impossible happened: failed to eliminate fresh name on type-checker stage"
    ConsArityMismatch src tag expected actual -> err src $ hsep ["Case-expression arguments mismatch for ", pretty tag, ". Expected ", pretty expected, " arguments, but got ", pretty actual]
    where
      err src msg = vcat [hcat [pretty src, ": error: "], indent 4 msg]
      inTicks x = hcat ["'", x, "'"]
      prettyTy = pretty . FixityCtx getFixity


