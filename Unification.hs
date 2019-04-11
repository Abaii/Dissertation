module Unification where
import Trees
import Debug.Trace


--- Subsitution: a list of mappings from variables to terms.
type Subst = [(Term,Term)]


resMaybe :: Maybe a -> a 
resMaybe Nothing = error "cannot create MGU"
resMaybe (Just a) = a
{--
    mgu: Compute the most general unifier for a set of terms, takes the set of terms and the current unifier
--}

mgu :: [(Term,Term)] ->  Subst ->  Maybe Subst 
mgu [] sub =  Just sub 
mgu (x:xs) sub 
  |  x' == Nothing = Just []
  | otherwise = mgu xs $ (resMaybe x')++( sub)
      where x' = mgu' x $ [] 

--- mgu': Given two terms find a subsitution and append it to a list of substitutions 

mgu' :: (Term, Term) -> Subst -> Maybe Subst 
mgu' (t1@(Variable x),t2@(Variable y)) s
  | t1 == t2 = traceShow("vars")Just $ (t1,t2):s
  | otherwise = Just $ (Variable x, Variable y):s

mgu' ((Func f t),(Func g u)) s
  | f /= g = Nothing
  | length(t) == length(u) =traceShow (s ) Just $ (zip t u)
  | otherwise = Nothing 

mgu' ((Func f t),(Variable x)) s
  | (Variable x) `elem` t && equal = traceShow("hit") Just( (Variable x, Func f t):s)
     where l = length(t) == 1 
           equal = l && (Variable x == head t)
mgu' (x, t) s
  | x /= t && x `elem` t' = Nothing
  | inSub && x `notElem` t' = traceShow("x t") Just ((x,t):(newSet))
    where t' = occurance t
          inSub = inSubst x s 
          newSet = replaceTerms s [] t x 

replaceTerm :: Term -> Term -> Term -> Term 
replaceTerm term@(Func f t) original new 
  | term == original = new 
  | otherwise = Func f (rp' t [] original new)
replaceTerm (Variable x) original new 
  | Variable x == original = new 

replaceTerms :: Subst -> Subst -> Term -> Term -> Subst 
replaceTerms [] set _ _ = set 
replaceTerms ((t1,t2):xs) set original new  = replaceTerms xs ((t1', t2'):set) original new 
  where t1' = replaceTerm t1 original new 
        t2' = replaceTerm t2 original new 

rp' :: [Term] -> [Term] -> Term -> Term-> [Term]
rp' [] newList _ _ = newList
rp' (x@(Variable x'):xs) nTerms original new
  | x == original = rp' xs (new:nTerms) original new
  | otherwise = rp' xs (x:nTerms) original new

rp' (x@(Func f t'):xs) nTerms original new 
  | x == original = rp' xs (new:nTerms) original new
  | otherwise = rp' xs (nTerms++[Func f t'']) original new
    where t'' = rp' t' [] original new


inSubst :: Term -> Subst -> Bool 
inSubst term s =traceShow (flatSubst) term `elem` flatSubst
  where flatSubst = [t | (a,b) <- s, t<-[a,b]]

