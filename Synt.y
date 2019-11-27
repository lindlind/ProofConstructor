{
module Synt where
import Lex
}

%name parse Expr
%name parseFirstLine Task
%name getVariables VExpr
%tokentype { Token }
%error { parseError }

%token
    ","                             { TComma }
    "|-"                            { TProve }
    "("                             { TOpenBracket }
    ")"                             { TCloseBracket }
    "->"                            { TImpl }
    "|"                             { TOr   }
    "&"                             { TAnd  }
    "!"                             { TNot  }
    var                             { TVar $$ }

%%

Task:
    Context "|-" Expr               { $3 : $1 }

Context:
                                    { [] }
    | Expr                          { [$1] }
    | Expr "," Context              { $1 : $3 }

Expr:
    Disj                            { $1 }
    | Disj "->" Expr                { Impl $1 $3 }

Disj:
    Conj                            { $1 }
    | Disj "|" Conj                 { Or $1 $3 }

Conj:
    Neg                             { $1 }
    | Conj "&" Neg                  { And $1 $3 }

Neg:
    "!" Neg                         { Not $2 }
    | var                           { Var $1 }
    | "(" Expr ")"                  { $2 }

VExpr:
    VDisj                           { $1 }
    | VDisj "->" VExpr              { $1 ++ $3 }

VDisj:
    VConj                           { $1 }
    | VDisj "|" VConj               { $1 ++ $3 }

VConj:
    VNeg                            { $1 }
    | VConj "&" VNeg                { $1 ++ $3 }

VNeg:
    "!" VNeg                        { $2 }
    | var                           { [$1] }
    | "(" VExpr ")"                 { $2 }

{
parseError :: [Token] -> a
parseError _ = error "Parse error"

data Expr = Impl Expr Expr | Or Expr Expr | And Expr Expr | Not Expr | Var String deriving (Eq, Ord)

instance Show Expr where
  show (Impl a b) = "(" ++ show a ++ "->" ++ show b ++ ")"
  show (Or a b) = "(" ++ show a ++ "|" ++ show b ++ ")"
  show (And a b) = "(" ++ show a ++ "&" ++ show b ++ ")"
  show (Not a) = "!" ++ show a
  show (Var a) = a
}