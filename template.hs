module Main where
import ParserLambda

-- sinteaxe LamAbstrata do calculo lambda

data NTLam
		= NTLamAbs NTLam
		| NTApp NTLam NTLam
		| NTVar Integer
	deriving Show


_charNotInList :: Char->[Char]->Char
_charNotInList x l = if(not (elem x l)) then x else _charNotInList (succ x) l 

charNotInList :: [Char]->Char
charNotInList l = _charNotInList 'a' l
 

freeVars :: CalcLamb -> [Char]
freeVars (Var x)     = [x]
freeVars (LamAbs x t)   = remove x (freeVars t)
freeVars (LamApp t1 t2) = freeVars t1 ++ freeVars t2

_indexOf :: Char->[Char]->Integer->Integer
_indexOf c [] i = -1
_indexOf c (a:b) i = if (c == a) then i else (_indexOf c b (i+1))

indexOf :: Char->[Char]->Integer
indexOf c l = _indexOf c l 0



remove :: Char -> [Char] -> [Char]
remove x [] = []
remove x (a:b) = if (x==a) then b else (a:remove x b)

--- Semântica

subs :: Char -> CalcLamb -> CalcLamb -> CalcLamb
subs x s (Var y) = if (x==y) then s else (Var y)
subs x s (LamAbs y t1) = if ((x /= y) && not(elem y (freeVars s)))
                         then LamAbs y (subs x s t1)
                         else error "problem with subs in LamLamAbs"

nSubs :: Integer->NTLam->NTLam->NTLam
nSubs j s (NTVar k) = if (j==k) then s else (NTVar k)
nSubs j s (NTLamAbs t1) = NTLamAbs (nSubs (j+1) (shifting s 0 1) t1)
nSubs j s (NTApp t1 t2) = NTApp (nSubs j s t1) (nSubs j s t2)

nEval :: NTLam->NTLam
nEval = undefined


shifting :: NTLam->Integer->Integer->NTLam
shifting (NTVar k) cutoff d = if (k<cutoff) then (NTVar k) else (NTVar k+1)
shifting (NTLamAbs t1) cutoff d = NTLamAbs (shifting t1 (cutoff+1) d)
shifting (NTApp t1 t2) cutoff d = NTApp (shifting t1 cutoff d) (shifting t2 cutoff d)


--interpret :: CalcLamb->[Char]->CalcLamb

_toNameless :: CalcLamb->[Char]->NTLam
_toNameless (Var x) gamma = NTVar (indexOf x gamma)
_toNameless (LamAbs x t) gamma = NTLamAbs (_toNameless t ([x] ++ gamma))
_toNameless (LamApp p q) gamma = NTApp (_toNameless p gamma) (_toNameless q gamma) 


toNameless :: CalcLamb->NTLam
toNameless a = _toNameless a (freeVars a)

namelessToNormal :: NTLam->[Char]->CalcLamb
namelessToNormal (NTVar x) gamma = Var (gamma!! (fromIntegral x))
namelessToNormal (NTLamAbs t) gamma = let c = (charNotInList gamma) in (LamAbs c (namelessToNormal t ([c]++gamma)))
namelessToNormal (NTApp t1 t2) gamma = LamApp (namelessToNormal t1 gamma) (namelessToNormal t2 gamma)

testeNameless :: NTLam->CalcLamb
testeNameless l = namelessToNormal l ['a', 'b', 'c'] 

isVal :: CalcLamb->Bool
isVal (Var x) = True
isVal (LamAbs c d) = True
isVal _ = False

eval :: CalcLamb->CalcLamb
eval (Var x) = Var x
eval (LamAbs x t) = LamAbs x t
eval (LamApp (LamAbs x t1) t2) = (subs x t2 t1)
eval (LamApp t1 t2) = if (not (isVal  t1))
						then let t0 = (eval t1)
						 	in (LamApp t0 t2)
					else if(not (isVal t2))
						 then (LamApp t1 (eval t2))
					else
						 (LamApp t1 t2)
 
--main = getContents >>= print . testeNameless . toNameless . parserlamb .lexer 
main = do
	s <- getContents
	let fv = freeVars ((parserlamb.lexer) s)
	print (namelessToNormal ((toNameless . parserlamb .lexer) s) fv)