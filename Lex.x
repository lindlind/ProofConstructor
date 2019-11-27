{
module Lex where
}

%wrapper "basic"

$digit = 0-9
$alpha = [A-Z]

tokens :-
    $white                          ;
    ","                             { \s -> TComma }
    "|-"                            { \s -> TProve }
    "("                             { \s -> TOpenBracket }
    ")"                             { \s -> TCloseBracket }
    "->"                            { \s -> TImpl }
    "|"                             { \s -> TOr   }
    "&"                             { \s -> TAnd  }
    "!"                             { \s -> TNot  }
    $alpha [$alpha $digit \_ \']*   { \s -> TVar s }

{
data Token = TNewLine | TComma | TProve | TOpenBracket | TCloseBracket | TImpl | TOr | TAnd | TNot | TVar String deriving (Eq, Show)
}