{-# OPTIONS_GHC -Wno-orphans #-}
-- | Pretty printer for types and terms.
module Type.Check.HM.Pretty(
    HasPrefix(..)
  , PrintCons(..)
  , OpFix(..)
  , Fixity(..)
) where

import Data.Bool
import Data.Fix
import Data.Maybe
import Data.Text (Text)
import Data.Text.Prettyprint.Doc

import Type.Check.HM.Type
import Type.Check.HM.Term

-- | Class to querry fixity of infix operations.
class IsVar v => HasPrefix v where
  getFixity :: v -> Maybe OpFix

instance HasPrefix Text where
  getFixity = const Nothing

instance HasPrefix String where
  getFixity = const Nothing

instance HasPrefix Int where
  getFixity = const Nothing

-- | This class is useful to define the way to print special cases
-- like constructors for tuples or lists.
class PrintCons v where
  printCons :: v -> [Doc ann] -> Doc ann

instance PrintCons Text where
  printCons name args = hsep $ pretty name : args

isPrefix :: HasPrefix v => v -> Bool
isPrefix = isNothing . getFixity

isInfix :: HasPrefix v => v -> Bool
isInfix  = not . isPrefix

instance (Pretty v, PrintCons v, HasPrefix v) => Pretty (Signature loc v) where
  pretty = foldFix go . unSignature
    where
      go = \case
        ForAllT _ _ r -> r
        MonoT ty      -> pretty ty

instance (HasPrefix v, PrintCons v, Pretty v) => Pretty (Type loc v) where
  pretty = go False initCtx . unType
    where
      go :: Bool -> FixityContext v -> Fix (TypeF loc v) -> Doc ann
      go isArrPrev ctx (Fix expr) = case expr of
        VarT _ name   -> pretty name
        ConT _ name [a, b] | isInfix name -> fromBin name a b
        ConT _ name as -> fromCon isArrPrev name as
        ArrowT _ a b -> fromArrow a b
        TupleT _ as -> fromTuple as
        ListT _ a -> fromList a
        where
          fromCon isArr name args = maybeParens (not (null args) && not isArr && needsParens ctx OpFunAp) $
            printCons name $ fmap (go False (FcRight OpFunAp)) args

          fromBin op a b = maybeParens (needsParens ctx (Op op)) $ hsep
            [ go True (FcLeft $ Op op) a
            , pretty op
            , go True (FcRight $ Op op) b
            ]

          fromArrow a b = maybeParens (needsParens ctx ArrowOp) $ hsep
            [ go True (FcLeft ArrowOp ) a
            , "->"
            , go True (FcRight ArrowOp) b
            ]

          fromTuple as = parens $ hsep $ punctuate comma $ fmap (pretty . Type) as

          fromList a = brackets $ pretty $ Type a

      initCtx = FcNone

maybeParens :: Bool -> Doc ann -> Doc ann
maybeParens cond = bool id parens cond

needsParens :: HasPrefix v => FixityContext v -> Operator v -> Bool
needsParens = \case
  FcNone      -> const False
  FcLeft ctx  -> fcLeft ctx
  FcRight ctx -> fcRight ctx
  where
    fcLeft ctxt op
      | comparePrec ctxt op == PoLT = False
      | comparePrec ctxt op == PoGT = True
      | comparePrec ctxt op == PoNC = True
      -- otherwise the two operators have the same precedence
      | fixity ctxt /= fixity op = True
      | fixity ctxt == FixLeft = False
      | otherwise = True

    fcRight ctxt op
      | comparePrec ctxt op == PoLT = False
      | comparePrec ctxt op == PoGT = True
      | comparePrec ctxt op == PoNC = True
      -- otherwise the two operators have the same precedence
      | fixity ctxt /= fixity op = True
      | fixity ctxt == FixRight = False
      | otherwise = True

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

getFixityEnv :: HasPrefix v => Operator v -> Maybe OpFix
getFixityEnv = \case
  OpFunAp -> Nothing
  Op v    -> getFixity v
  ArrowOp -> Just $ OpFix FixRight 2

comparePrec :: HasPrefix v => Operator v -> Operator v -> PartialOrdering
comparePrec a b = case (getFixityEnv a, getFixityEnv b) of
  (Just opA, Just opB) -> toPo (opFix'prec opA) (opFix'prec opB)
  _                    -> PoNC
  where
    toPo m n
      | m < n     = PoLT
      | m > n     = PoGT
      | otherwise = PoEQ


fixity :: HasPrefix v => Operator v -> Fixity
fixity op = maybe FixNone opFix'fixity $ getFixityEnv op

---------------------------------------

instance (HasPrefix v, PrintCons v, Pretty v, Pretty prim) => Pretty (Term prim loc v) where
  pretty (Term x) = foldFix prettyTermF x
    where
      prettyTermF = \case
        Var _ v            -> pretty v
        Prim _ p           -> pretty p
        App _ a b          -> parens $ hsep [a, b]
        Lam _ v a          -> parens $ hsep [hcat ["\\", pretty v], "->", a]
        Let _ v a          -> onLet [v] a
        LetRec _ vs a      -> onLet vs a
        AssertType _ r sig -> parens $ hsep [r, "::", pretty sig]
        Constr _ _ tag     -> pretty tag
        Case _ e alts      -> vcat [ hsep ["case", e, "of"], indent 4 $ vcat $ fmap onAlt alts]
        Bottom _           -> "_|_"
        where
          onLet vs body =
            vcat [ hsep ["let", indent 4 $ vcat $ fmap (\Bind{..} -> hsep [pretty bind'lhs, "=", bind'rhs]) vs]
                 , hsep ["in ", body]]

          onAlt CaseAlt{..} = hsep
            [ pretty caseAlt'tag, hsep $ fmap (pretty . snd . typed'value) caseAlt'args
            , "->"
            , caseAlt'rhs ]

