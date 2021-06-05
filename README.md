# Type inference for functional programming languages 

## Introduction

The algorithm implementation is taken from the book 
"The implementation of functional programming languages" by Simon L. Peyton Jones.
We can type-check polymorphic lambda-functions with it.
The algorithm is augmented with generic source code locations and variable names.
Also language supports user-defined types, case-expressions, polymorphic types and bottoms.

It is generic in source code locations and variable names. Note that if you don't
need to use source code locations you can use type `()` for it. 

## Tutorial

Let look at how to use the library with simple example. We are going to 
define a tiny language with lambda calculus, integer and boolean expressions and custom data types.
Complete code for this tutorial can be found in tests at `test/TM/NumLang.hs`

To use the type-checker we need to specify which types we use for variable names,
source code locations and primitive literals. Let's define thoase types:


### Language definition

```haskell
-- | Code locations
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
```

The type `CodeLoc` contains line and colum for location of the term. This info 
can be useful for reporting of errors of parsing or type-checker. This info is supplied
by parser. Each term is annotated with code locations.

The type `Prim` contains literals of our language. We support integers and booleans.
The type `Var` tells us that we are going to use plain strings for names of the variables.

For AST of the language we are going to reuse the AST provided by the type-checker library.

```haskell
import qualified Type.Check.HM as T

-- | Expressions for our language
newtype Expr = Expr { unExpr :: T.Term Prim CodeLoc Var }
```

#### Terms

Let's look at the type `Term` to know what is available to us:

```haskell
-- | The type of terms.
newtype Term prim loc v = Term { unTerm :: Fix (TermF prim loc v) }
  deriving (Show, Eq, Data)
```

```haskell
-- | Term functor. The arguments are
-- @loc@ for source code locations, @v@ for variables, @r@ for recurion.
data TermF prim loc v r
    = Var loc v                       -- ^ Variables.
    | Prim loc prim                   -- ^ Primitives.
    | App loc r r                     -- ^ Applications.
    | Lam loc v r                     -- ^ Abstractions.
    | Let loc (Bind loc v r) r        -- ^ Let bindings.
    | LetRec loc [Bind loc v r] r     -- ^ Recursive  let bindings
    | AssertType loc r (Type loc v)   -- ^ Assert type.
    | Case loc r [CaseAlt loc v r]    -- ^ case alternatives
    | Constr loc (Type loc v) v       -- ^ constructor with tag and arity, also we should provide the type
                                      --   of constructor as a function for a type-checker
    | Bottom loc                      -- ^ value of any type that means failed program.
    deriving (Show, Eq, Functor, Foldable, Traversable, Data)
```

We can see that AST is minimal but quite capable language. 
It can express lambda calculus with let-expressions, case-expressions for pattern matching,
recursive let-exprressionsm custom constructors, type-assertions and bottoms.

It's defined in Fix-point style. The last parameter of functor `TermF` is going to be recursive
parameter in the `Term`. If you are not familiar with fixed-point types you can look at the
library `data-fix`. Herre is a quick example of list data-type defined in this style:

```haskell
data ListF a rec = Nil | Cons a rec
  deriving (Functor)

type List = Fix ListF
```

The type Fix ties the knot of recursion:

```haskell
newtype Fix f = Fix (f (Fix f))
```

#### Expressions of the language

Let's look again at the type of our language:

```haskell
-- | Expressions for our language
newtype Expr = Expr { unExpr :: T.Term Prim CodeLoc Var }
```

To use type checker we need to specify which types are used for primitives, variables and source code locations.
Ro do it we need to provide instance of the class `Type.Check.HMLang`:

```haskell
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
```

We use language tag `NumLang` to define the instance. 
Also note the function `getPrimType` it provides types for our literals.
It's assumed that literals have definite type. 

In normal scenario users write the code in our language and we can parse it and type-check prior to execution.
But for this example we are going to build expressions with Haskell. Let's define useful functions for that.

The cool feature of the library is that it supports source code locations. It automatically
derives the spot of error for you. The values for source code come from parser. 
But for this example we are going to simplify the task and ignore the parsing stage.
Thus we just use fake locations:

```haskell
defLoc :: CodeLoc
defLoc = CodeLoc 0 0
```

Let's define functions for literals (primitives):

```haskell
-- | constructor for integer literals
int :: Int -> Expr
int = Expr . T.primE defLoc . PInt defLoc

-- | constructor for boolean literals
bool :: Bool -> Expr
bool = Expr . T.primE defLoc . PBool defLoc

```

We can construct constant integers and booleans. 
Let's define couple of helper functions for application of the expressions.
With the functions we can apply function with one, two or three arguments:

```haskell
-- | Application
app :: Expr -> Expr -> Expr
app (Expr a) (Expr b) = Expr $ T.appE defLoc a b

-- | Binary application
app2 :: Expr -> Expr -> Expr -> Expr
app2 a b c = app (app a b) c

-- | Ternary application
app3 :: Expr -> Expr -> Expr -> Expr -> Expr
app3 a b c d = app (app2 a b c) d
```

The function `appE` is a helper function that is defined in the library to build
application of terms.

Also let's reuse Haskell string literals for variables:

```haskell
{-# LANGUAGE OverloadedStrings #-}

import Data.String

-- Variables (construct them from string literals)
instance IsString Expr where
  fromString = Expr . T.varE defLoc
```

This instance with usage of extension `OverloadedStrings` let's us write
variables for our language as ordinary Haskell strings.

Let's define numeric expressions:

```haskell
instance Num Expr where
  (+) = app2 "+"
  (*) = app2 "*"
  (-) = app2 "-"
  negate = app "negate"
  fromInteger = int . fromInteger
  abs = error "undefined"
  signum = error "undefined"
```

We imagine that we know the type definitions for `"+"`, `"*"`, `"negate"` etc.
They are primitive operations of our language.

Let's define boolean expressions:

```
-- | Boolean &&
andB :: Expr -> Expr -> Expr
andB = app2 "&&"

-- | Boolean ||
orB :: Expr -> Expr -> Expr
orB = app2 "||"

-- | Boolean negation
notB :: Expr -> Expr
notB = app "not"
```

For them to be useful we should have some interaction between
integers and booleans. We can do it with comparison operators:

```haskell
eq, neq, gt, lt, gte, lte :: Expr -> Expr -> Expr
eq  = app2 "=="
neq = app2 "/="
lt  = app2 "<"
gt  = app2 ">"
lte = app2 "<="
gte = app2 ">="

```

Also we can define operator for `if-then-else` branching:

```
-- | If-expressions
if_ :: Expr -> Expr -> Expr -> Expr
if_ = app3 "if"
```

We can create simple expressions with integers and numbers. But what about functions?
Are we going to support them? That's exactly what lambda-abstraction does:

```
-- | Lambda-expressions
lam :: Var -> Expr -> Expr
lam v (Expr fun) = Expr $ T.lamE defLoc v fun
```

It's the same as: `\v -> fun` in Haskell. Note that our language support 
only lambdas with single argument. But it can be easily extended with curry trick:

```haskell
lam "a" $ lam "b" $ ("a" + 2) * "b"
```

We have defined the function: `\a -> \b -> (a + 2) * b`

Let's also define useful functions for let-expressions:

```haskell
-- | Let-expressions
let_ :: Var -> Expr -> Expr -> Expr
let_ v e (Expr body) = Expr $ T.letE defLoc (toBind v e) body

-- | Let-expressions with recursion
letRec :: [(Var, Expr)] -> Expr -> Expr
letRec es (Expr body) = Expr $ T.letRecE defLoc (fmap (uncurry toBind) es) body

toBind :: Var -> Expr -> T.Bind CodeLoc Var (T.Term Prim CodeLoc Var)
toBind v (Expr e) = T.Bind defLoc v e
```

Note that they are slightly different. In Haskell we are used to single let-expression
for every case. But in the type-checker we distinguish recursive and non-recursive cases.
The non-recursive `let_` can only define variable. We can not use it in the right-hand side of
the definition. So the expression:

```
let fac x = if (x <= 0) then 1 else (x * fac (x - 1))
in  fac 10
```

Is going to produce error that `fac` is undefined.
For this case we have to use recursive let-expression: `T.letRecE`.
The recursive version should be fine to type-check.
Prior to type-check we can derive which let-expression is recursive and which is not.

### Type-checker context

To use the inference algorithm we have to provide type-checker context:

```haskell
newtype Context = Context (Map v (Signature loc v))
```

#### Types and signatures

The context contains all signatures for known functions. Known functions can 
be primitive operators or functions which are already were type-cheked and loaded from
other library modules.

Note the difference between `Type` and `Signature`. The type can be:

```haskell
newtype Type = Type (Fix TypeF)

data TypeF loc var r
    = VarT loc var      -- ^ Variables
    | ConT loc var [r]  -- ^ type constant with list of arguments
    | ArrowT loc r r    -- ^ Special case of ConT that is rendered as ->
    | TupleT loc [r]    -- ^ Special case of ConT that is rendered as (,,,)
    | ListT loc r       -- ^ Special case of ConT that is rendered as [a]
    deriving (Eq, Ord, Show, Functor, Foldable, Traversable, Generic, Data)

```

The type is also defined in fixed-point style.
Type can be variable, constructor with arguments (like `Maybe Int` or `Either a b`),
arrow (like `a -> b`), tuple (`(a, b, Int)`) or list (`[a]`).
The special cases for tuple and list can be expressed with `ConT` with arguments
but they are provided here for pretty-printer. The pretty-printer is going to render them
like Haskell does with parens and brackets.

Type signatures contain information on weather type is polymorphic or monomorphic:

```
-- | Functor for signature is a special type that we need for type inference algorithm.
-- We specify which variables in the type are schematic (non-free).
data SignatureF loc var r
    = ForAllT loc var r     -- ^ specify schematic variable
    | MonoT (Type loc var)  -- ^ contains the type
    deriving (Eq, Ord, Show, Functor, Foldable, Traversable, Data)

-- | Signaure is a special type that we need for type inference algorithm.
-- We specify which variables in the type are schematic (non-free).
newtype Signature loc var = Signature { unSignature :: Fix (SignatureF loc var)
  } deriving (Show, Eq, Ord, Data)
```

#### Constant types 

The case `ForAllT` introduces polymorphic parameters. The top-level case `MonoT` 
signifies that there are no parameters in the type.
The `ForAllT` behaves just like keyword `forall` in Haskell. 

Let's  define types for our literals:

```haskell
type Ty = T.Type CodeLoc Var

boolT, intT :: Ty
boolT = T.conT defLoc "Bool" []
intT  = T.conT defLoc "Int" []
```

The constant type is constructor-type with no arguments.

#### Arrow type

Let's define handy function for arrow type:

```haskell
infixr ~>

(~>) :: Ty -> Ty -> Ty
(~>) a b = T.arrowT defLoc a b
```

#### Context for our language

Let's define types for numeric expressions:

```haskell
is a b = (a, T.monoT b)

nums =
  [ "+"      `is` (intT ~> intT ~> intT)
  , "*"      `is` (intT ~> intT ~> intT)
  , "-"  `    is` (intT ~> intT ~> intT)
  , "negate" `is` (intT ~> intT)
  ]
```

Boolean ones look almost the same:

```haskell
booleans =
  [ "&&"  `is` (boolT ~> boolT ~> boolT)
  , "||"  `is` (boolT ~> boolT ~> boolT)
  , "not" `is` (boolT ~> boolT)
  ]
```

We assume that comparisons work only for integer arguments:

```haskell
comparisons = fmap ( `is` (intT ~> intT ~> boolT)) ["==", "/=", "<", ">", "<=", ">="]
```

In the signature for `if-then-else` we encounter type-parameter:

```
ifSig = (if", forA $ T.monoT $ boolT ~> aT ~> aT ~> aT)
  where
    -- forall a . ...
    forA = T.forAllT defLoc "a"

    -- a type variable "a"
    aT = T.varT defLoc "a"
```

With all definitions we can define context for type-inference:

```haskell
import qualified Data.Map.Strict as M

-- | Context contains types for all known definitions
defContext :: T.Context CodeLoc Var
defContext = T.Context $ M.fromList $ mconcat
  [ booleans
  , nums
  , comparisons
  , [ifSig]
  ]
```

### Type-check expressions

Let's define simple expressions for our language and type-check them:

```haskell
intExpr1 = negate $ ((20::Expr) + 30) * 100
```

Let's define couple of helpers to check that type is correct:

```haskell
infer = T.inferType defContext . unExpr
check ty expr = Right ty == (infer expr)
```

Let's check that the expression is correct:

```haskell
check intT intExpr1
```

Let's type-check a function:

```haskell
intFun1 = lam "x" ((1 + "x") * 10)

check (intT ~> intT) intFun1
```

Let's define factorial function:

```haskell
-- | Factorial
fact :: Expr
fact = lam "x" $ letRec
  [ ("fac", lam "n" $ if_ (eq "n" 0) 1 ("n" * app "fac" ("n" - 1)))
  ]
  (app "fac" "x")

check (intT ~> intT) fact
```

In the file `test/Tm/NumLang.hs` you can find many more examples.

### User-defined types and pattern matching

we can type-check expressions with user defined data-types. 
For user's data types we assume that for any constructor we know its type.
We augment all constructor expressions and case-expressions with information on
data-types.

Let's define data-type of points and rectangles and type-check the function 
that calculates the square of rectangle.

Let's begin with types for our types:

```haskell
-- types for custom types
pointT, rectT :: Ty
pointT  = T.conT defLoc "Point" []
rectT = T.conT defLoc "Rect" []
```

Let's also define constructors:

```haskell
-- | Point constructor
point :: Expr -> Expr -> Expr
point = app2 (Expr $ T.constrE defLoc (intT ~> intT ~> pointT) "Point")

-- | Rectangle constructor
rect :: Expr -> Expr -> Expr
rect = app2 (Expr $ T.constrE defLoc (pointT ~> pointT ~> rectT) "Rect")
```

Note that we can use already defined type for point in the definition of rectangle.

#### case-expressions and pattern matching

Let's define functions for pattern-matching. Pattern-matching is executed with case expressions.
Let's look at the type of case-expression:


```haskell
   | Case loc r [CaseAlt loc v r]    -- ^ case alternatives

 -- | Case alternatives
data CaseAlt loc v a = CaseAlt
  { caseAlt'loc   :: loc
  -- ^ source code location
  , caseAlt'tag   :: v
  -- ^ tag of the constructor
  , caseAlt'args  :: [Typed loc v (loc, v)]
  -- ^ arguments of the pattern matching
  , caseAlt'constrType :: Type loc v
  -- ^ type of the result expression, they should be the same for all cases
  , caseAlt'rhs   :: a
  -- ^ right-hand side of the case-alternative
  }
  deriving (Show, Eq, Functor, Foldable, Traversable, Data)

```

Seems to be quite involved, but let's break it appart.
Case expression takes in location, expression against which pattern matching happens
and the list of laternatives. 

In Haskell example:

```haskell
case expr of
  alt1 
  alt2  
```

Becomes `Case location expr [alt1, alt2]`
The alternative type looks scary at first. In haskell we used to something like this:

```haskell
Just a  -> f a
Nothing -> "nothing there"
```

We can see in the case alternative three distinct parts:

* constructor `Just`

* it's arguments `a`

* right-hand side expression `f a`

In the `CaseAlt` we provide additional information on:

* `caseAlt'loc` is source code location

* `caseAlt'tag` is constructor name

* `caseAlt'args` are arguments of the constructor. Note that they are typed, ie we 
    have to provide the type information for arguments explicitly. We know this by the name of the constructor.

* `caseAlt'constrType` is the type of the result (for example `Maybe Int`)

* `caseAlt'rhs` is right hand side of the case-expression (`f a`).

With this in mind let's define  ahelper for `case`-expressions over points:

```haskell
casePoint :: Expr -> (Var, Var) -> Expr -> Expr
casePoint (Expr e) (x, y) (Expr body) = Expr $ T.caseE defLoc e
  [T.CaseAlt defLoc "Point" [tyVar intT x, tyVar intT y] pointT body]

tyVar :: Ty -> Var -> T.Typed CodeLoc Var (CodeLoc, Var)
tyVar ty v = T.Typed ty (defLoc, v)
```

Also we can define the same function for rectangles:

```haskell
caseRect :: Expr -> (Var, Var) -> Expr -> Expr
caseRect (Expr e) (x, y) (Expr body) = Expr $ T.caseE defLoc e
  [T.CaseAlt defLoc "Rect" [tyVar pointT x, tyVar pointT y] rectT body]
```

#### Expressions with user-defined types

Let's define addition of points:

```haskell
addPointLam :: Expr
addPointLam = lam "a" $ lam "b" $
  casePoint "a" ("ax", "ay") $
    casePoint "b" ("bx", "by") $ point ("ax" + "bx") ("ay" + "by")
```

This is the same as a Haskell exression:

```haskell
addPoint = \a -> \b -> 
  case a of
    Point ax ay -> 
      case b of
        Point bx by -> Point (ax + bx) (ay + by)
```

Let's type check:

```haskell
check (pointT ~> pointT ~> pointT) addPointLam
```

Let's define negation of the point:

```haskell
negatePointLam :: Expr
negatePointLam = lam "p" $ casePoint "p" ("px", "py") $
  point (negate "px") (negate "py")

check (pointT ~> pointT) negatePointLam
```

The cool thing is that we can reuse the definition to construct expressions:

```haskell
addPoint :: Expr -> Expr -> Expr
addPoint = app2 addPointLam

negatePoint :: Expr -> Expr
negatePoint = app negatePointLam
```

Now we are ready to define the square of rectangle:

```haskell
rectSquare :: Expr
rectSquare = lam "r" $ defAbs $ caseRect "r" ("p1", "p2") $
  casePoint "p1" ("p1x", "p1y") $ casePoint "p2" ("p2x", "p2y") $
    app "abs" $ ("p1x" - "p2x") * ("p1y" - "p2y")
  where
    defAbs = let_ "abs" (lam "a" $ if_ ("a" `gte` 0) "a" (negate "a"))
```

In Haskell it would look like:

```haskell
rectSquare = \r -> 
  let abs = \a -> if (a >= 0) then a  else (negate a)
  in  case r of
        Rect p1 p2 -> case p1 of
                        Point p1x p1y -> case p2 of
                                           Point p2x p2y -> abs ((p1x - p2x) * (p1y - p2y))
```

Let's check the type:

```haskell
check (rectT ~> intT) rectSquare
```

Yuo can find out more examples in the directory `test`. With that 
we have covered almost all key features of the library. 
Happy type checking!

