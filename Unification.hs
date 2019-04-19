module Unification where
import Trees
import Debug.Trace

type Subst = [(Term,Term)]

--Unify :: apply unfier to tree 
unify :: Subst -> Tree Lf -> Tree Lf 
unify [] tree = tree
unify (x:xs) tree = unify xs (fmap (applySub x) tree)
-- applySub : apply substitution to a labelled formulas 
applySub :: (Term, Term) -> Lf -> Lf 
applySub t (Lf f b) = Lf (applySub' t f) b 
--applySub' : take a subsitution and apply it to a single formula
applySub' :: (Term,Term) -> Formula ->Formula  
applySub' (t,t') (Exist x f@(Pred p terms))  =  (Exist x p') 
  where f' = rp' terms [] t t'
        p' = Pred p f'
applySub' (t,t') (ForAll x f@(Pred p terms)) =  (ForAll x p') 
  where f' = rp' terms [] t t'
        p' = Pred p f'

applySub' (t,t') ( (Pred p terms) ) =  (Pred p terms') 
  where terms' = rp' terms [] t t' 

applySub' t (Not x) = Not (applySub' t x)
applySub' t (And x y) = And (applySub' t x) (applySub' t y)
applySub' t (Or x y) = Or (applySub' t x) (applySub' t y)
applySub' t (Imply x y) = Imply (applySub' t x) (applySub' t y)

-- compute the most general unifier till no changes are made 
mgu :: Maybe Subst -> Maybe Subst -> Maybe Subst 
mgu Nothing _ = Nothing
mgu _ Nothing = Nothing
mgu set set' 
  | set == set' = set' 
  | otherwise = mgu set' (mgu' (resMaybe set') [])
{--
    mgu': Compute the most general unifier for a set of terms, takes the set of terms and the current unifier
--}

mgu' :: [(Term,Term)] ->  Subst ->  Maybe Subst 
mgu' [] sub =  Just sub 
mgu' (((Func (f,a) t),(Func (g,b) u)):xs) sub
  | f /= g =  Nothing
  | a == b && unifiable /= Nothing = mgu' xs ((zip t u)++sub)
  | otherwise = Nothing 
    where unifiable = mgu' (zip t u) [] 
mgu' ((t@(Func _ _), x@(Variable y )):xs) sub = mgu' xs ((x,t):sub)
mgu' o@((x,t):xs) sub 
  | x == t = mgu' xs sub
  | x /= t && x `elem` t' = Nothing
  | inSub && x `notElem` t' = mgu' xs ((x,t):(newSet)) 
  | otherwise = mgu' xs $ reverse ((x,t):sub)
    where t' = occurance t
          inSub = inSubst x sub
          newSet = replaceTerms sub [] x t

replaceTerm :: Term -> Term -> Term -> Term 
replaceTerm term@(Func f t) original new 
  | term == original = new 
  | otherwise = Func f (rp' t [] original new)
replaceTerm (Variable x) original new 
  | Variable x == original = new 
  | otherwise = Variable x

replaceTerms :: Subst -> Subst -> Term -> Term -> Subst 
replaceTerms [] set _ _ = set
replaceTerms ((t1,t2):xs) set original new  = replaceTerms xs ((t1', t2'):set) original new 
  where t1' = replaceTerm t1 original new 
        t2' = replaceTerm t2 original new 



inSubst :: Term -> Subst -> Bool 
inSubst _ []= True
inSubst term s =term `elem` flatSubst
  where flatSubst = [t | (a,b) <- s, t<-[a,b]]

-- inSet :: Term -> Subst -> Bool
-- inSet _ [] = False
-- inSet t (y@(x,_):ys)
--   | t == x = True
--   | otherwise = inSet t ys 

isFunc :: Term -> Bool
isFunc (Func _ _) = True
isFunc t = False

test1 :: Term 
test1 = Func ("f",2) [Variable "X", Variable "X"]
test2 :: Term 
test2 = Func ("f", 2) [Func ("a", 0) [], Func ("b",0) []]

test3 :: Term 
test3 = Func ("f",2) [Variable "X", Func ("b",0) []]

test4 :: Term 
test4 = Func ("f",2) [Func ("a",0) [] ,Variable "Y"]

