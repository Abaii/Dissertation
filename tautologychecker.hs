module Tautologychecker where 
import Trees

rmdups :: Eq a => [a] -> [a]
rmdups []     = []
rmdups (x:xs) = x : filter (/= x) (rmdups xs)


type Assoc k v = [(k,v)]

type Subst = Assoc Char Bool

find :: Eq k => k -> Assoc k v -> v
find k t = head [v | (k',v) <- t, k == k']

--Evaluates a Formulaosition given a substitution for its variables
eval :: Subst -> Formula -> Bool
eval s (Var x) = find x s
eval s (Not p) = not (eval s p)
eval s (And p q) = eval s p && eval s q
eval s (Or p q) = eval s p || eval s q
eval s (Imply p q) = eval s p <= eval s q

vars :: Formula -> [Char]
vars (Var x) = [x]
vars (Not p) = vars p
vars (And p q) = vars p ++ vars q
vars (Or p q) = vars p ++ vars q
vars (Imply p q) = vars p ++ vars q

bools :: Int -> [[Bool]]
bools 0 = [[]]
bools n = map (False:) bss ++ map (True:) bss
        where bss = bools (n-1)

substs :: Formula -> [Subst]
substs p = map (zip vs) (bools (length vs))
        where vs = rmdups (vars p)

isTaut :: Formula -> Bool
isTaut p = and [eval s p | s <-substs p]