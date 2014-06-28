{
module SystemF.Parser where

-- References:
-- http://www.haskell.org/onlinereport/exps.html

import Data.Maybe       (fromMaybe)
import qualified Language.Java.Syntax as J (Op (..))

import SystemF.Syntax
import SystemF.Lexer    
import SystemF.TypeInference    (inferType)
}

%name parser
%tokentype  { Token }
%error      { parseError }

%token

"("      { OParen }
")"      { CParen }
"/\\"    { TLam }
"\\"     { Lam }
":"      { Colon }
"forall" { Forall }
"->"     { Arrow }
"."      { Dot }
"let"    { Let }
"="      { Eq }
"in"     { In }
"fix"    { Fix }
"Int"    { TypeInt }
"if0"    { If0 }
"then"   { Then }
"else"   { Else }
","      { Comma }

"*"      { PrimOp J.Mult   }
"/"      { PrimOp J.Div    }
"%"      { PrimOp J.Rem    }
"+"      { PrimOp J.Add    }
"-"      { PrimOp J.Sub    }
"<"      { PrimOp J.LThan  }
"<="     { PrimOp J.LThanE }
">"      { PrimOp J.GThan  }
">="     { PrimOp J.GThanE }
"=="     { PrimOp J.Equal  }
"!="     { PrimOp J.NotEq  }
"&&"     { PrimOp J.CAnd   }
"||"     { PrimOp J.COr    }

INTEGER  { Integer $$ }
UPPERID  { UpperId $$ }
LOWERID  { LowerId $$ }
UNDERID  { UnderId $$ }

-- Precedence and associativity directives
%nonassoc EOF

%right "in"
%right "->"
%nonassoc "else"

-- http://en.wikipedia.org/wiki/Order_of_operations#Programming_languages
%left "||"
%left "&&"
%nonassoc "==" "!="
%nonassoc "<" "<=" ">" ">="
%left "+" "-"
%left "*" "/" "%"

%nonassoc UMINUS

%%

-- Reference for rules:
-- https://github.com/ghc/ghc/blob/master/compiler/parser/Parser.y.pp#L1453

exp : infixexp %prec EOF        { $1 }

infixexp
    : exp10                     { $1 }
    | infixexp "*" exp10        { \e -> FPrimOp ($1 e) J.Mult   ($3 e) }
    | infixexp "/" exp10        { \e -> FPrimOp ($1 e) J.Div    ($3 e) }
    | infixexp "%" exp10        { \e -> FPrimOp ($1 e) J.Rem    ($3 e) }
    | infixexp "+" exp10        { \e -> FPrimOp ($1 e) J.Add    ($3 e) }
    | infixexp "-" exp10        { \e -> FPrimOp ($1 e) J.Sub    ($3 e) }
    | infixexp "<" exp10        { \e -> FPrimOp ($1 e) J.LThan  ($3 e) }
    | infixexp "<=" exp10       { \e -> FPrimOp ($1 e) J.LThanE ($3 e) }
    | infixexp ">"  exp10       { \e -> FPrimOp ($1 e) J.GThan  ($3 e) }
    | infixexp ">=" exp10       { \e -> FPrimOp ($1 e) J.GThanE ($3 e) }
    | infixexp "==" exp10       { \e -> FPrimOp ($1 e) J.Equal  ($3 e) }
    | infixexp "!=" exp10       { \e -> FPrimOp ($1 e) J.NotEq  ($3 e) }
    | infixexp "&&" exp10       { \e -> FPrimOp ($1 e) J.CAnd   ($3 e) }
    | infixexp "||" exp10       { \e -> FPrimOp ($1 e) J.COr    ($3 e) }

exp10 
    : "/\\" tvar "." exp                        { \(tenv, env, venv) -> FBLam (\a -> $4 (($2, a):tenv, env, venv)) }
    | "\\" "(" var ":" typ ")" "." exp          { \(tenv, env, venv) -> FLam ($5 tenv) (\x -> $8 (tenv, ($3, x):env, venv)) }

    -- let x = e1 : T in e2 rewrites to  (\(x : T). e2) e1

    | "let" var "=" exp ":" typ "in" exp  
        { \(tenv, env, venv) -> FApp (FLam ($6 tenv) (\x -> $8 (tenv, ($2, x):env, venv))) ($4 (tenv, env, venv)) }

    -- let x = e1 in e2 rewrites to (\(x : (inferType ... e1)). e2) e1

    | "let" var "=" exp "in" exp  
        { \(tenv, env, venv) -> 
            let e1  = $4 (tenv, env, venv)
                te1 = inferType (tenv, env, venv) e1
            in
            FApp (FLam te1 (\x -> $6 (tenv, ($2, x):env, ($2, te1):venv))) e1 
        }

    -- -- For the old fixpoint syntax

    -- | "fix" var "." "\\" "(" var ":" typ ")" "." exp ":" typ 
    --      { \(tenv, env, venv) -> FFix ($8 tenv) (\y -> \x -> $11 (tenv, ($6, x):($2, y):env)) ($13 tenv) }
  
    | "fix" "(" var ":" atyp "->" typ ")" "." "\\" var "." exp 
        { \(tenv, env, venv) -> FFix ($5 tenv) (\y -> \x -> $13 (tenv, ($11, x):($3, y):env, venv)) ($7 tenv) }

    | "if0" exp "then" exp "else" exp           { \e -> Fif0 ($2 e) ($4 e) ($6 e) }
    | "-" INTEGER %prec UMINUS                  { \e -> FLit (-$2) }
    | fexp                                      { $1 }

fexp
    : fexp aexp         { \(tenv, env, venv) -> FApp  ($1 (tenv, env, venv)) ($2 (tenv, env, venv)) }
    | fexp typ          { \(tenv, env, venv) -> FTApp ($1 (tenv, env, venv)) ($2 tenv) }
    | aexp              { $1 }

aexp   : aexp1          { $1 }

aexp1  : aexp2          { $1 }

aexp2 
    : var               { \(tenv, env, venv) -> FVar $1 (fromMaybe (error $ "Unbound variable: `" ++ $1 ++ "'") (lookup $1 env)) }
    | INTEGER           { \_e -> FLit $1 }
    | aexp "." UNDERID  { \e -> FProj $3 ($1 e) } 
    | "(" exp ")"       { $2 }
    | "(" tup_exprs ")" { \(tenv, env, venv) -> FTuple ($2 (tenv, env, venv)) }

tup_exprs 
    : exp "," exp       { \(tenv, env, venv) -> ($1 (tenv, env, venv):[$3 (tenv, env, venv)]) }
    | exp "," tup_exprs { \(tenv, env, venv) -> ($1 (tenv, env, venv):$3 (tenv, env, venv)) }

typ
    : "forall" tvar "." typ     { \tenv -> FForall (\a -> $4 (($2, a):tenv)) }
    
    -- Require an atyp on the LHS so that `for A. A -> A` cannot be
    -- parsed as `(for A. A) -> A` since `for A. A` is not a valid atyp.
    | atyp "->" typ             { \tenv -> FFun ($1 tenv) ($3 tenv) }

    | atyp                      { $1 }

atyp 
    : tvar              { \tenv -> FTVar (fromMaybe (error $ "Unbound type variable: `" ++ $1 ++ "'") (lookup $1 tenv)) }
    | "Int"             { \_    -> PFInt }
    | "(" typ ")"       { $2 }

var  : LOWERID       { $1 }
tvar : UPPERID       { $1 }

{
parseError :: [Token] -> a
parseError tokens = error $ "Parse error before tokens:\n\t" ++ show tokens

reader :: String -> PFExp t e
reader = (\parser -> parser ([], [], [])) . parser . lexer
}
