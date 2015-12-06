{
--module ParserLambda where
module ParserLambda where
import Data.Char
}

%name parserlamb
%tokentype { Token }
%error { parseError }
%left NEG
%token
	lam { TokenLam } 
	var { TokenVar $$ }
	'.' { TokenPoint }
	'(' { TokenOB }
	')' { TokenCB }
	
%%

-- regras de producao da gramatica

--Term :

CalcLamb : '(' CalcLamb ')'                   { ($2) } 
		|var var 							{( LamApp (Var $1) (Var $2) )}
		
		--|CalcLamb var 						{( LamApp ($1) (Var $2) )}
--
		--|lam var '.' CalcLamb  var 		{( LamApp (LamAbs $2 ($4)) (Var $5 )}
		--|lam var '.' CalcLamb CalcLamb		{( LamApp (LamAbs $2 ($4)) ($5) )}
		

        --|var var 					        { LamApp $1  $2 }
	   --| '(' lam var '.' '('CalcLamb')' ')' { ( LamAbs $3 ( $6 ) ) }

	   | CalcLamb CalcLamb       %prec NEG         { ( LamApp ($1) ($2) ) }
	   |lam var '.' CalcLamb               { LamAbs $2 ( $4 ) }
	   | var                %prec NEG        { (Var $1) }
	   
	   --| '(' CalcLamb CalcLamb ')'          { ( LamApp $2 $3 ) }
	   --| '(' CalcLamb ')' '(' CalcLamb ')'  { ( LamApp $2 $5 ) }
	   --| '(' CalcLamb ')'  CalcLamb  { ( LamApp $2 $4 ) }
	   
	   --| '(' var ')'                               { Var $2 }

{

parseError :: [Token] -> a
parseError b = error "Parse Error"

data CalcLamb 
		= LamAbs Char CalcLamb
		| Var Char
		| LamApp CalcLamb CalcLamb
	deriving Show

data Token 
		= TokenVar Char
		| TokenPoint
		| TokenOB
		| TokenCB
		| TokenLam 
	deriving Show

lexer :: String -> [Token]
lexer [] = []
lexer (c:cs)
	| areEqual (c:(take 2 cs)) "lam" = TokenLam : lexer (tail(tail(tail(cs))))
	| isSpace c = lexer cs
	| isAlpha c = TokenVar c : lexer cs	
lexer ('(':cs) = TokenOB : lexer cs
lexer (')':cs) = TokenCB : lexer cs
lexer ('.':cs) = TokenPoint : lexer cs

areEqual :: String -> String -> Bool
areEqual a b = a == b

}