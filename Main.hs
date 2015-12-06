module Main where
import ParserLambda
import Debug.Trace

-- sinteaxe LamAbstrata do calculo lambda

data NTLam
		= NTLamAbs NTLam
		| NTApp NTLam NTLam
		| NTVar Integer
	deriving (Eq, Show)


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
remove x (a:b) = if (x==a) then remove x b else (a:remove x b)

--- Semântica

subs :: Char -> CalcLamb -> CalcLamb -> CalcLamb
subs x s (Var y) = if (x==y) then s else (Var y)
subs x s (LamAbs y t1) = if ((x /= y) && not(elem y (freeVars s)))
                         then LamAbs y (subs x s t1)
                         else error "problem with subs in LamLamAbs"



--Nameless
shifting :: NTLam->Integer->Integer->NTLam
shifting (NTVar k) cutoff d = if(k >= cutoff) then (NTVar (k+d)) else (NTVar k)
shifting (NTLamAbs t1) cutoff d = (NTLamAbs (shifting t1 (cutoff+1) d))
shifting (NTApp t1 t2) cutoff d = (NTApp (shifting t1 cutoff d) (shifting t2 cutoff d))

nsubs :: Integer->NTLam->NTLam->NTLam
nsubs j (NTVar k) s = if(k == j) then s else (NTVar k)
nsubs j (NTLamAbs t1) s = (NTLamAbs (nsubs (j+1) t1 (shifting s 0 1)))
nsubs j (NTApp t1 t2) s = NTApp (nsubs j t1 s) (nsubs j t2 s)

nIsVal :: NTLam->Bool
nIsVal (NTVar x) = True
--nIsVal (NTLamAbs x) = True
nIsVal (NTLamAbs x) = nIsVal x
nIsVal (NTApp (NTLamAbs x) t2) = False
nIsVal (NTApp t1 t2) = (nIsVal t1) && (nIsVal t2)
--nIsVal _ = False

neval :: NTLam->NTLam
neval (NTVar x) = NTVar x
neval (NTLamAbs x) =  (NTLamAbs (neval x))
--neval (NTApp (NTLamAbs t1) t2) | trace ("\n1-> t1 = " ++ show (NTApp (NTLamAbs t1) t2)) False = undefined
neval (NTApp (NTLamAbs t1) t2) = (neval (shifting (nsubs 0 t1 (shifting t2 0 1)) 0 (-1)))
--neval (NTApp t1 t2) | trace ("\n2-> " ++ show (NTApp t1 t2)) False = undefined
neval (NTApp t1 t2) = if (not (nIsVal  t1))
						then let t0 = (neval t1)
						 	in neval (NTApp t0 t2)
					else if(not (nIsVal t2))
						 then (NTApp t1 (neval t2))
					else
						(NTApp t1 t2)

--neval :: NTLam->NTLam
--neval (NTVar x) = NTVar x
--neval (NTLamAbs x) = NTLamAbs (neval x)
--neval (NTApp (NTLamAbs t1) t2) = neval ((shifting (nsubs 0 t1 (shifting t2 0 1)) 0 (-1)))
--neval (NTApp t1 t2) = neval(NTApp (neval t1) (neval t2))

--
c0 = NTLamAbs(NTLamAbs (NTVar 0))
c1 = NTLamAbs(NTLamAbs ((NTApp (NTVar 1) (NTVar 0))))
c2 = NTLamAbs (NTLamAbs (NTApp (NTVar 1) (NTApp (NTVar 1) (NTVar 0))))
c3 = NTLamAbs (NTLamAbs (NTApp (NTVar 1) (NTApp (NTVar 1) (NTApp (NTVar 1) (NTVar 0)))))
suc =  (toNameless.parserlamb.lexer) ("(lam n .(lam s. (lam z. (s ((n s) z)))))")
soma = NTLamAbs (NTApp (NTVar 0) (NTLamAbs (NTLamAbs (NTLamAbs (NTApp (NTVar 1) (NTApp (NTApp (NTVar 2) (NTVar 1)) (NTVar 0)))))))
plus = (toNameless.parserlamb.lexer) "(lam m. (lam n . (lam s. (lam z . (m s) ((n s) z)))))"
plus2 = (toNameless.parserlamb.lexer) "(lam m. (lam n . (lam s. (lam z . m s (n s z)))))"
pow = NTLamAbs (NTLamAbs (NTApp (NTVar 0) (NTVar 1)))

testeTenso = "(lam m. (lam n . (lam s. (lam z . m s ((n s) z))))) (lam s. lam z . s (s z)) (lam s. lam z . s (s z))"

times = NTLamAbs (NTLamAbs (NTApp (NTApp (NTVar 1) (NTApp plus (NTVar 0))) c0 ))

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


namelessToNumber :: NTLam->Integer
namelessToNumber (NTVar x) = x
namelessToNumber (NTLamAbs x) = namelessToNumber x
namelessToNumber (NTApp t1 t2) = (namelessToNumber t1) + (namelessToNumber t2)



--namelessToNumber :: NTLam->Integer
--namelessToNumber b = _namelessToNumber b 0

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
 

normalToString :: CalcLamb->[Char]
normalToString (Var x) = "("++ (x: ")")
normalToString (LamAbs x t) = "(lam " ++ [x] ++ "." ++ "(" ++ (normalToString t) ++ ")"
normalToString (LamApp t1 t2) = "(" ++ (normalToString t1) ++ ")" ++ " (" ++ (normalToString t2) ++ ")"

--test2 = "(lam n .(lam s. (lam z. (s ((n s) z))))) (w)"



--test :: CalcLamb"
--test = 

--main = getContents >>= print . eval . parserlamb .lexer 
main = do
	s <- getContents
	let fv = freeVars ((parserlamb.lexer) s)
	print (normalToString (namelessToNormal ((neval.toNameless . parserlamb .lexer) s) fv))










