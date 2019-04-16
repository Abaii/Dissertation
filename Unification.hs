module Unification where
import Trees
import Debug.Trace

type Subst = [(Term,Term)]

--- Subsitution: a list of mappings from variables to terms.



{--
    mgu: Compute the most general unifier for a set of terms, takes the set of terms and the current unifier
--}

mgu :: [(Term,Term)] ->  Subst ->  Maybe Subst 
mgu [] sub =  Just sub 
mgu (x:xs) sub 
  |  x' == Nothing = Just []
  | otherwise = mgu xs $ (resMaybe x')++( sub)
      where x' = mgu' x $ sub

--- mgu': Given two terms find a subsitution and append it to a list of substitutions 

mgu' :: (Term, Term) -> Subst -> Maybe Subst 

mgu' (t1@(Variable x),t2@(Variable y)) s
  | t1 == t2 = traceShow("vars")Just $ (t1,t2):s
  | otherwise = Just $ (Variable x, Variable y):s

mgu' ((Func f t),(Func g u)) s
  | f /= g = Nothing
  | length(t) == length(u) = (mgu (zip t u) s)
  | otherwise = Nothing 

mgu' ((Func f t),(Variable x)) s
  | not ((Variable x) `elem` t) = traceShow(s) Just( (Variable x, Func f t):s)
  | otherwise = Nothing
     
mgu' (x, t) s
  | x /= t && x `elem` t' = Nothing
  | applied = Nothing
  | inSub && x `notElem` t' = traceShow(s) Just ((x,t):(newSet))
  | otherwise = Just ((x,t):s)
    where t' = occurance t
          inSub = inSubst x s 
          newSet = replaceTerms s [] t x 
          applied = inSet x s 


replaceTerm :: Term -> Term -> Term -> Term 
replaceTerm term@(Func f t) original new 
  | term == original = new 
  | otherwise = Func f (rp' t [] original new)
replaceTerm (Variable x) original new 
  | Variable x == original = new 

replaceTerms :: Subst -> Subst -> Term -> Term -> Subst 
replaceTerms [] set _ _ = set
replaceTerms _ [] _ _ = [] 
replaceTerms ((t1,t2):xs) set original new  = replaceTerms xs ((t1', t2'):set) original new 
  where t1' = replaceTerm t1 original new 
        t2' = replaceTerm t2 original new 



inSubst :: Term -> Subst -> Bool 
inSubst _ []= True
inSubst term s =term `elem` flatSubst
  where flatSubst = [t | (a,b) <- s, t<-[a,b]]

inSet :: Term -> Subst -> Bool
inSet _ [] = False
inSet t (y@(x,_):ys)
  | t == x = True
  | otherwise = inSet t ys 