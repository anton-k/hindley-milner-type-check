{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}
-- | Tests for language with lambda calculus with numbers and booleans.
module TM.NumLang where

import Data.String
import Test.Tasty
import Test.Tasty.HUnit

import Data.Either
import qualified Type.Check.HM as T
import qualified Data.Map.Strict as M

infixr ~>

data CodeLoc = CodeLoc
  { codeLoc'line :: Int
  , codeLoc'col  :: Int
  }
  deriving (Show, Eq)

-- | Primitives of our language.
-- We support integers and booleans
data Prim
  = PInt CodeLoc Int     -- ^ integers
  | PBool CodeLoc Bool   -- ^ booleans
  deriving (Show, Eq)

-- | Type for variables
type Var = String

-- types for the language

type Ty = T.Type CodeLoc Var

(~>) :: Ty -> Ty -> Ty
(~>) a b = T.arrowT defLoc a b

boolT, intT :: Ty
boolT = T.conT defLoc "Bool" []
intT  = T.conT defLoc "Int" []

-- | Language tag (we need it for Lang instance)
data NumLang

-- | Instanciate to provide the right components of the language
instance T.Lang NumLang where
  type Src  NumLang = CodeLoc   -- ^ source code locations
  type Var  NumLang = Var       -- ^ variables
  type Prim NumLang = Prim      -- ^ primitives

  -- what type is assigned to primitive literals of the language
  getPrimType = \case
    PInt  loc _ -> T.conT loc "Int"  []
    PBool loc _ -> T.conT loc "Bool" []

-- | Expressions for our language
newtype Expr = Expr { unExpr :: T.Term Prim CodeLoc Var }

-- | In real case we should get this info from parser.
-- For example we assign same code location to all expressions.
defLoc :: CodeLoc
defLoc = CodeLoc 0 0

-- primitives

-- | constructor for integer literals
int :: Int -> Expr
int = Expr . T.primE defLoc . PInt defLoc

-- | constructor for boolean literals
bool :: Bool -> Expr
bool = Expr . T.primE defLoc . PBool defLoc

-- numeric expressions

instance Num Expr where
  (+) = app2 "+"
  (*) = app2 "*"
  (-) = app2 "-"
  negate = app "negate"
  fromInteger = int . fromInteger
  abs = error "undefined"
  signum = error "undefined"

-- boolean expressions

-- | Boolean &&
andB :: Expr -> Expr -> Expr
andB = app2 "&&"

-- | Boolean ||
orB :: Expr -> Expr -> Expr
orB = app2 "||"

-- | Boolean negation
notB :: Expr -> Expr
notB = app "not"

-- comparisons

eq, neq, gt, lt, gte, lte :: Expr -> Expr -> Expr
eq  = app2 "=="
neq = app2 "/="
lt  = app2 "<"
gt  = app2 ">"
lte = app2 "<="
gte = app2 ">="

-- if then else

-- | If-expressions
if_ :: Expr -> Expr -> Expr -> Expr
if_ = app3 "if"

----------------------------------------------------------
-- lambda calc

-- Variables (construct them from string literals)
instance IsString Expr where
  fromString = Expr . T.varE defLoc

toBind :: Var -> Expr -> T.Bind CodeLoc Var (T.Term Prim CodeLoc Var)
toBind v (Expr e) = T.Bind defLoc v e

-- | Application
app :: Expr -> Expr -> Expr
app (Expr a) (Expr b) = Expr $ T.appE defLoc a b

-- | Binary application
app2 :: Expr -> Expr -> Expr -> Expr
app2 a b c = app (app a b) c

-- | Ternary application
app3 :: Expr -> Expr -> Expr -> Expr -> Expr
app3 a b c d = app (app2 a b c) d

-- | Let-expressions
let_ :: Var -> Expr -> Expr -> Expr
let_ v e (Expr body) = Expr $ T.letE defLoc (toBind v e) body

-- | Let-expressions with recursion
letRec :: [(Var, Expr)] -> Expr -> Expr
letRec es (Expr body) = Expr $ T.letRecE defLoc (fmap (uncurry toBind) es) body

-- | Lambda-expressions
lam :: Var -> Expr -> Expr
lam v (Expr fun) = Expr $ T.lamE defLoc v fun

----------------------------------------------------------
-- custom constructors

-- types for custom types
pointT, circleT, rectT :: Ty
pointT  = T.conT defLoc "Point" []
circleT = T.conT defLoc "Circle" []
rectT = T.conT defLoc "Rect" []

-- | Point constructor
point :: Expr -> Expr -> Expr
point = app2 (Expr $ T.constrE defLoc (intT ~> intT ~> pointT) "Point")

circle :: Expr -> Expr -> Expr
circle = app2 (Expr $ T.constrE defLoc (pointT ~> intT ~> circleT) "Circle")

rect :: Expr -> Expr -> Expr
rect = app2 (Expr $ T.constrE defLoc (pointT ~> pointT ~> rectT) "Rect")

casePoint :: Expr -> (Var, Var) -> Expr -> Expr
casePoint (Expr e) (x, y) (Expr body) = Expr $ T.caseE defLoc e
  [T.CaseAlt defLoc "Point" [tyVar intT x, tyVar intT y] pointT body]

caseCircle :: Expr -> (Var, Var) -> Expr -> Expr
caseCircle (Expr e) (x, y) (Expr body) = Expr $ T.caseE defLoc e
  [T.CaseAlt defLoc "Circle" [tyVar pointT x, tyVar intT y] circleT body]

caseRect :: Expr -> (Var, Var) -> Expr -> Expr
caseRect (Expr e) (x, y) (Expr body) = Expr $ T.caseE defLoc e
  [T.CaseAlt defLoc "Rect" [tyVar pointT x, tyVar pointT y] rectT body]

tyVar :: Ty -> Var -> T.Typed CodeLoc Var (CodeLoc, Var)
tyVar ty v = T.Typed ty (defLoc, v)

----------------------------------------------------------
-- Type inference context
--
-- We define in context type signatures for all known functions
-- or functions that were already derived on previous steps of compilation.

-- | Context contains types for all known definitions
defContext :: T.Context CodeLoc Var
defContext = T.Context $ M.fromList $ mconcat
  [ booleans
  , nums
  , comparisons
  , [("if", forA $ T.monoT $ boolT ~> aT ~> aT ~> aT)]
  ]
  where
    booleans =
      [ "&&"  `is` (boolT ~> boolT ~> boolT)
      , "||"  `is` (boolT ~> boolT ~> boolT)
      , "not" `is` (boolT ~> boolT)
      ]

    nums =
      [ "+"  `is` (intT ~> intT ~> intT)
      , "*"  `is` (intT ~> intT ~> intT)
      , "-"  `is` (intT ~> intT ~> intT)
      , "negate" `is` (intT ~> intT)
      ]

    comparisons = fmap ( `is` (intT ~> intT ~> boolT)) ["==", "/=", "<", ">", "<=", ">="]

    is a b = (a, T.monoT b)

    -- forall a . ...
    forA = T.forAllT defLoc "a"

    -- a type variable "a"
    aT = T.varT defLoc "a"


----------------------------------------------------------
-- examples

intExpr1 :: Expr
intExpr1 = negate $ ((20::Expr) + 30) * 100

boolExpr1 :: Expr
boolExpr1 = andB (andB (notB ((intExpr1 `lte` 1000) `orB` (2 `gt` 0))) (bool True)) (5 `neq` (2 + 2))

failExpr1 :: Expr
failExpr1 = lam "x" $ 2 + "x" `eq` (bool True)

failExpr2 :: Expr
failExpr2 = 2 + bool True

failExpr3 :: Expr
failExpr3 = 2 + "missingVar"

-- | Simple integer function
intFun1 :: Expr
intFun1 = lam "x" ((1 + "x") * 10)

-- | Square distance of the point to zero
squareDist :: Expr
squareDist = lam "x" $ lam "y" $ "x" * "x" + "y" * "y"

-- | Check that point is inside circle
insideCircle :: Expr
insideCircle = lam "d" $ lam "x" $ lam "y" $
  let_ "squareDist" squareDist
    (app2 "squareDist" "x" "y") `lt` ("d" * "d")

-- | Factorial
fact :: Expr
fact = lam "x" $ letRec
  [ ("fac", lam "n" $ if_ (eq "n" 0) 1 ("n" * app "fac" ("n" - 1)))
  ]
  (app "fac" "x")

-- | Greatest common divisor
gcd' :: Expr
gcd' = lam "x" $ lam "y" $ defAbs $ defMod $
  letRec
    [ ("gcd", lam "a" $ lam "b" $ if_ ("b" `eq` 0) (app "abs" "a") (app2 "gcd" "b" (app2 "mod" "a" "b")))
    ]
  (app2 "gcd" "x" "y")
  where
    defAbs = let_ "abs" (lam "a" $ if_ ("a" `gte` 0) "a" (negate "a"))
    defMod = let_ "mod" (lam "a" $ lam "b" $ letRec [("go", lam "m" $ lam "n" $ if_ ("m" `lt` "n") "m" (app2 "go" ("m" - "n") "n"))] (app2 "go" "a" "b"))

-- geometry examples

addPointLam :: Expr
addPointLam = lam "a" $ lam "b" $
  casePoint "a" ("ax", "ay") $
    casePoint "b" ("bx", "by") $ point ("ax" + "bx") ("ay" + "by")

negatePointLam :: Expr
negatePointLam = lam "p" $ casePoint "p" ("px", "py") $
  point (negate "px") (negate "py")

addPoint :: Expr -> Expr -> Expr
addPoint = app2 addPointLam

negatePoint :: Expr -> Expr
negatePoint = app negatePointLam

rectSquare :: Expr
rectSquare = lam "r" $ defAbs $ caseRect "r" ("p1", "p2") $
  casePoint "p1" ("p1x", "p1y") $ casePoint "p2" ("p2x", "p2y") $
    app "abs" $ ("p1x" - "p2x") * ("p1y" - "p2y")
  where
    defAbs = let_ "abs" (lam "a" $ if_ ("a" `gte` 0) "a" (negate "a"))

insideCircle2 :: Expr
insideCircle2 = lam "c" $ lam "p" $ caseCircle "c" ("center", "rad") $
  casePoint (addPoint "center" (negatePoint "p")) ("ax", "ay") $
    app3 insideCircle "rad" "ax" "ay"

----------------------------------------------------------
-- tests

tests :: TestTree
tests = testGroup "lambda calculus with numbers and booleans"
  [ check "int expr"        intT                            intExpr1
  , check "bool expr"       boolT                           boolExpr1
  , check "int fun"         (intT ~> intT)                  intFun1
  , check "square dist fun" (intT ~> intT ~> intT)          squareDist
  , check "inside circle"   (intT ~> intT ~> intT ~> boolT) insideCircle
  , check "factorial"       (intT ~> intT)                  fact
  , check "gcd"             (intT ~> intT ~> intT)          gcd'
  , fails "Fail mismatch 1" failExpr1
  , fails "Fail mismatch 2" failExpr2
  , fails "Fail missing var" failExpr3
  , check "add points"      (pointT ~> pointT ~> pointT)    addPointLam
  , check "negate point"    (pointT ~> pointT)              negatePointLam
  , check "rect square"     (rectT ~> intT)                 rectSquare
  , check "inside circle 2" (circleT ~> pointT ~> boolT)    insideCircle2
  ]
  where
    infer = T.inferType defContext . unExpr
    check msg ty expr = testCase msg $ Right ty @=? (infer expr)
    fails msg expr = testCase msg $ assertBool "Detected wrong type" $ isLeft (infer expr)

