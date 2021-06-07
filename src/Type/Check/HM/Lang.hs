{-# Language TypeFamilyDependencies #-}
-- | Main class for the library that defines common types and primitives for the language.
module Type.Check.HM.Lang(
  -- * Lang
    Lang(..)
  , TypeOf
  , TermOf
  , TyTermOf
  , SubstOf
  , ErrorOf
) where

import Type.Check.HM.Term
import Type.Check.HM.Subst
import Type.Check.HM.Type
import Type.Check.HM.TypeError
import Type.Check.HM.TyTerm

-- | Main class to define inference API.
-- For type inference we have to define instance of the Lang class:
--
-- > data NoPrim
-- >   deriving (Show)
-- >
-- > data TestLang
-- >
-- > instance Lang TestLang where
-- >   type Src  TestLang = ()
-- >   type Var  TestLang = Text
-- >   type Prim TestLang = NoPrim
-- >   getPrimType _ = error "No primops"
--
class
  ( IsVar (Var q)
  , Show (Src q)
  , Show (Prim q)
  , Eq (Src q)
  ) => Lang q where

  -- | Variables for our language. Notice that this type should be injective in relation to type of @Lang@.
  -- We need to have unique type of variables for each language definition.
  type Var q = r | r -> q

  -- | Source code locations
  type Src q

  -- | Primitives
  type Prim q

  -- | Reports type for primitive.
  getPrimType :: Prim q -> TypeOf q

-- | Types of our language
type TypeOf q = Type (Src q) (Var q)

-- | |Terms of our language
type TermOf q = Term (Prim q) (Src q) (Var q)

-- | Typed terms of our language
type TyTermOf q = TyTerm (Prim q) (Src q) (Var q)

-- | Type errors of our language
type ErrorOf q = TypeError (Src q) (Var q)

-- | Type substitutions
type SubstOf q = Subst (Src q) (Var q)



