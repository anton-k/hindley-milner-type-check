{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DerivingStrategies #-}
-- | This module contains types for structured type errors.
module Type.Check.HM.TypeError where

import Control.DeepSeq (NFData)
import Data.Data
import Data.Function (on)
import GHC.Generics    (Generic)
import Type.Check.HM.Type
import Type.Check.HM.Subst

import qualified Data.List as L

-- | Type errors.
data TypeError loc var
  = OccursErr  loc (Type loc var)                 -- ^ error of mismatch of polymorphic constructors, infinite type. Like [a] = a
  | UnifyErr   loc (Type loc var) (Type loc var)  -- ^ Unification error
  | SubtypeErr loc (Type loc var) (Type loc var)  -- ^ Subtype error (happens on explicit type assertions)
  | NotInScopeErr loc var                         -- ^ Missing signature in context for free-variable.
  | EmptyCaseExpr loc                             -- ^ no case alternatives in the case expression
  | FreshNameFound                                -- ^ internal error with fresh name substitution
  deriving stock    (Show, Eq, Functor, Generic, Data)
  deriving anyclass (NFData)

instance LocFunctor TypeError where
  mapLoc f = \case
    OccursErr loc ty     -> OccursErr (f loc) (mapLoc f ty)
    UnifyErr loc tA tB   -> UnifyErr (f loc) (mapLoc f tA) (mapLoc f tB)
    SubtypeErr loc tA tB -> SubtypeErr (f loc) (mapLoc f tA) (mapLoc f tB)
    NotInScopeErr loc v  -> NotInScopeErr (f loc) v
    EmptyCaseExpr loc    -> EmptyCaseExpr (f loc)
    FreshNameFound       -> FreshNameFound

instance HasTypeVars TypeError where
  tyVars = \case
    OccursErr _ ty     -> tyVars ty
    UnifyErr _ a b     -> tyVars a <> tyVars b
    SubtypeErr _ a b   -> tyVars a <> tyVars b
    NotInScopeErr _ _  -> mempty
    EmptyCaseExpr _    -> mempty
    FreshNameFound     -> mempty

  tyVarsInOrder err = L.nubBy ((==) `on` fst) $ case err of
    OccursErr _ ty     -> tyVarsInOrder ty
    UnifyErr _ a b     -> tyVarsInOrder a <> tyVarsInOrder b
    SubtypeErr _ a b   -> tyVarsInOrder a <> tyVarsInOrder b
    NotInScopeErr _ _  -> mempty
    EmptyCaseExpr _    -> mempty
    FreshNameFound     -> mempty

instance CanApply TypeError where
  apply f = \case
    OccursErr loc ty   -> OccursErr loc $ apply f ty
    UnifyErr loc a b   -> UnifyErr loc (apply f a) (apply f b)
    SubtypeErr loc a b -> SubtypeErr loc (apply f a) (apply f b)
    other              -> other

