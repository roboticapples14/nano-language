# Nano Overview
Nano is an interpreter for a subset of Haskell

The overall objective of this assignment is to fully understand the notions of
scoping,
binding,
environments and closures
by implementing an interpreter for a subset of Haskell.

## Types:
The following data types (in Types.hs) are used to represent the different elements of the language.

Binary Operators
Nano uses the following binary operators encoded within the interpreter as values of type Binop.

data Binop
  = Plus
  | Minus
  | Mul
  | Div
  | Eq
  | Ne
  | Lt
  | Le
  | And
  | Or
  | Cons

## Expressions
All Nano programs correspond to expressions, each of which will be represented within your interpreter by Haskell values of type Expr:

data Expr
  = EInt  Int
  | EBool Bool
  | ENil
  | EVar Id
  | EBin Binop Expr Expr
  | EIf  Expr Expr  Expr
  | ELet Id   Expr  Expr
  | EApp Expr Expr
  | ELam Id   Expr
  deriving (Eq)
where Id is just a type alias for String used to represent variable names:

type Id = String

## Expressions
The following lists some example Nano expressions, and the corresponding values of type Expr used to represent the expression inside your interpreter.

Let-expressions
The let-expression

let x = 3 in x + x		
is represented by

ELet "x" (EInt 3)
  (EBin Plus (EVar "x") (EVar "x"))
Anonymous function definitions
The function

\x -> x + 1
is represented by

ELam "x" (EBin Plus (EVar "x") (EInt 1))
Function applications (also known as "function calls")
The function application

f x									
is represented by

EApp (EVar "f") (EVar "x")
(Recursive) named function definitions
The expression

let f = \x -> f x in
  f 5	    
is represented by

ELet "f" (ELam "x" (EApp (EVar "f") (EVar "x")))
  (EApp (Var "f") (EInt 5))


## Values
We will represent Nano values, i.e., the results of evaluation, using the following datatype:

data Value
  = VInt  Int
  | VBool Bool
  | VClos Env Id Expr
  | VNil
  | VPair Value Value
  | VPrim (Value -> Value)
where an Env is simply a dictionary -- a list of pairs of variable names and the values they are bound to:

type Env = [(Id, Value)]
Intuitively, the Nano integer value 4 and Boolean value True are represented respectively as VInt 4 and VBool True.

VClos env "x" e represents a function with argument "x" and body expression e that was defined in an environment env.