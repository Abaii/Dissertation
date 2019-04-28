module Trees where

import Debug.Trace
import System.Random
import Control.Monad
import Control.Monad.State
-- IMPLEMENTING TABLEAUX WITH TREES 

-- Data type for terms 
{-
  function in first order-logic are of the form f(X0...Xn) where f is a function symbol (a constant)
  and X0...Xn are terms, functions of 0-arity are constants
  -- Func (Var, Int) [Term] where Int is the arity, each Func f has its own arity.
-}

type Var = String 
data Term = Variable Var | Func (Var, Int) [Term] deriving (Eq)  

--Formula data type
data Formula = Var Char |
               Not Formula | 
               And Formula Formula | 
               Or Formula Formula | 
               Imply Formula Formula | 
               ForAll Var Formula |
               Exist Var Formula |
               Pred Var [Term]
               deriving Eq
data Direction = L | R 



-- Calculating occurance of variables in a term

occurance :: Term -> [Term]
occurance (Variable x) = [Variable x]
occurance (Func x t) = occuranceA t

occuranceA :: [Term] -> [Term]
occuranceA [] = []
occuranceA (y:ys) = occurance y++(occuranceA ys)

-- Compute all Free Variables in a FOL formula
fV :: Formula -> [Term]
fV (Var x) = [Variable [x]]
fV (Pred x t) = occuranceA t
fV (Not x) = fV x
fV (Imply x y) = fV x ++ fV y
fV (And x y) =  fV x ++ fV y
fV (Or x y) =  fV x ++ fV y
fV (ForAll x f) = filter (\y -> y /= (Variable x)) (fV f)
fV (Exist x f) = filter (\y -> y /= (Variable x)) (fV f)

resMaybe :: Maybe a -> a 
resMaybe Nothing = error "cannot create MGU"
resMaybe (Just a) = a

formula0 :: Formula 
formula0 = Var 'P'
formula1:: Formula
formula1 = And (Imply (Var 'B') (Var 'A')) (Not ( Var 'P'))

conjunction :: Formula 
conjunction = And (Var 'A') (Var 'B')


disjunction :: Formula 
disjunction = Or (Var 'A') (Var 'B')

disjunc1 :: Formula 
disjunc1 =  Or (Or (Var 'A') (Var 'B')) (Var 'C')

disjunc2 :: Formula
disjunc2 =  Or (Or (Or (Var 'A') (Var 'B')) (Var 'C')) (Var 'D')

conDisjunc :: Formula 
conDisjunc = Or (And (Var 'A') (Var 'B')) (Var 'C')
disConjunc :: Formula 
disConjunc =  And (Or (Var 'A') (Var 'B')) (Var 'C')

invalid :: Formula 
invalid = And (Var 'A') (Not (Var 'A'))

valid :: Formula 
valid = Or (Var 'A') (Not (Var 'A'))
formula2 :: Formula 
formula2 = And (And (Var 'P') (Var 'Q')) (Var 'T')
formula3 :: Formula 
formula3 = And (And (And (Var 'P') (Var 'Q')) (Var 'T')) (Var 'X')
formula4 :: Formula 
formula4 = And (And (And (And (Var 'P') (Var 'Q')) (Var 'T')) (Var 'X')) (Var 'C')

p9 :: Formula 
p9 = Or (Not( And (Or (Var 'A') (Var 'B')) (Or (Not (Not (Var 'A'))) (Not (Var 'B'))))) (Var 'A')
implication :: Formula 
implication = Imply (Var 'P') (Var 'Q')
implicationLong :: Formula 
implicationLong = Imply (Var 'P') (Imply (Var 'S') (Imply (Var 'Q') (Var 'P')))

universal :: Formula 
universal = ForAll ("X") (Pred "P" [Variable "X"])
tautUni :: Formula 
tautUni = Or universal (Not universal)
nUniversal :: Formula
nUniversal = ForAll ("X") $  Not (Pred "P" [Variable "X"])
predinvalid = And (ForAll ("X") (Pred "P" [Variable "X"])) (Not (Pred "P" [Variable "X"]))
nofree :: Formula
nofree = Exist ("X") $ Not $ Pred "P" [Variable "X"]
predicate :: Formula 
predicate = Pred "P" [Variable "X"]
existential :: Formula
existential = Exist "X" (Pred "P" [Variable "X", Variable "Y", Variable "Z", Func ("a",0) []])

existential1 :: Formula
existential1 = Exist "X" (Pred "P" [Variable "X"])

f111 :: Formula
f111 = And universal universal
instance Show Term where 
  show (Variable c) = show c
  show (Func s []) = show s
  show (Func s ls) = show(s)++ show(ls)
instance Show Formula where
    show (Var p) =  show p
    show (Not x) =  ("¬(" ++ show(x) ++ ")")
    show (And x y) = ("("++show(x) ++ " ∧ " ++ show(y) ++ ")")
    show (Or x y) = ("("++show(x) ++ " ∨ " ++ show(y)++")")
    show (Imply x y) = ("("++show(x) ++ " -> " ++ show(y)++")") 
    show (ForAll x y) = ("fa"++ show(x) ++"(" ++ show(y) ++ ")")
    show (Exist x y) = ("ex" ++ show(x)++"(" ++ show(y) ++ ")")
    show (Pred x y) = show(x) ++ "(" ++ show(y) ++")" 

data Tree a = Empty | Node a (Tree a) (Tree a) deriving (Show, Eq)
instance Functor Tree where
 fmap f Empty = Empty
 fmap f (Node x left right) = Node (f x) (fmap f left) (fmap f right)
-- Formulas on tree nodes with an 'expanded' attribute
data Lf = Lf {
    formula :: !Formula,
    expanded :: Bool
} deriving ( Eq)

instance Show Lf where 
    show (Lf (Var p) x) = show(Var p) ++ " " ++ show(x)
    show (Lf (Not a) b) = show (Not a) ++ " " ++ show (b)
    show (Lf (And a b) c) = show (And a b) ++ " " ++ show (c)
    show (Lf (Or a b) c) = show (Or a b) ++ " " ++ show (c)
    show (Lf (Imply a b) c) = show (Imply a b) ++ " " ++ show(c)
    show (Lf (ForAll a b) c) = show (ForAll a b)
    show (Lf (Exist a b) c) = show (Exist a b)
    show (Lf (Pred x y) c) = show(Pred x y) 


showTree :: (Eq a, Show a) => Tree a -> [Tree a] -> Int -> Int -> IO()

showTree (Node v Empty Empty) list target c = printProcess (Node v Empty Empty) (list ++ [Empty] ++ [Empty]) target c 
showTree (Node v Empty r) list target c = printProcess (Node v Empty r) (list ++ [Empty] ++ [r]) target c 
showTree (Node v l Empty) list target c = printProcess (Node v l Empty) (list ++ [l] ++ [Empty]) target c 
showTree (Node v l r) list target c
  | l == r && l `notElem` list = showTree (Node v l r) (list ++ [l] ++[r]) target c
  | ( l `notElem` list )  = showTree (Node v l r) (list ++ [l]) target c
  | ( r `notElem` list ) = showTree (Node v l r) (list ++ [r]) target c
  | length(list) < 1 = putStr(show v)
  | otherwise = printProcess (Node v l r) list target c

showTree Empty l t c
  | all (== Empty) l = putStrLn("   Empty   ")
  | otherwise =  printProcess Empty (l ++ [Empty] ++ [Empty]) t c

printProcess :: (Eq a, Show a) => Tree a -> [Tree a] -> Int -> Int -> IO()


printProcess Empty (x:xs) target count 
  |target == count = do
    putStrLn("   Empty    ")
    showTree x xs (target*2) 1
  | otherwise = do
    putStr("   Empty    ")
    showTree x xs target (count+1)

printProcess (Node v l r) (x:xs) target count
  |target == count = do
    putStrLn("   " ++ (show v) ++ "   " )
    showTree x xs (target*2) 1

  |otherwise = do
    putStr("   " ++ (show v) ++ "   " )
    showTree x xs target (count+1)

-- Create counter for variable 
data Counter = Counter {
  varCount :: !Int
}
{-
Given a formula create the corresponding node for a tableaux tree.
-}
createNode :: Formula -> Tree Lf
createNode formula =  Node (Lf ( Not formula) False) Empty Empty

-- rp' - replace all terms, x with t in a list of terms.
rp' :: [Term] -> [Term] -> Term -> Term-> [Term]
rp' [] newList _ _ = newList
rp' (x@(Variable x'):xs) nTerms original new
  | x == original = rp' xs (new:nTerms) original new
  | otherwise = rp' xs (x:nTerms) original new

rp' (x@(Func f t'):xs) nTerms original new 
  | x == original = rp' xs (new:nTerms) original new
  | otherwise = rp' xs (nTerms++[Func f t'']) original new
    where t'' = rp' t' [] original new

subPred :: Formula -> Term -> Term -> Formula 
subPred (Pred p terms) t1 t2 = Pred p terms'
  where terms' = rp' terms [] t1 t2
subPred (Not x) t1 t2 = Not $ subPred x t1 t2
subPred f _ _ = f  
{-
  Replace all occurances x in some quantified formula with x', where x' is a variable not occuring anywhere else in the tableau.
-}
subst :: Formula -> Term -> Formula 
subst (ForAll x p) x' = ForAll x p'
    where p' = subPred p (Variable x) x'
subst  (Exist x p) x' = Exist x p'
  where p' = subPred p (Variable x) x'
subst (And x y ) x' = And (subst x x') (subst y x')
subst (Or x y ) x' = Or (subst x x') (subst y x')
subst (Imply x y ) x' = Imply (subst x x') (subst y x')
subst (Not x ) x' =  Not (subst x x') 

-- All variables and skolem functions
freshvars = ["v"++show(x)| x <- [1..]]

skolems = ["f"++show(x) | x <- [1..]]
{-
  create skolem func
-}
skolemFunc :: Formula -> String -> Term
skolemFunc f s  = Func (s, length(freeVars)) freeVars
  where freeVars = fV f

expandNode :: Tree Lf -> Int -> ([String],[String]) ->  Tree Lf 
expandNode Empty c _  = Empty 
expandNode (Node (Lf (Var x) False) _ _) c _= Node (Lf (Var x) True) Empty Empty 

expandNode (Node (Lf (Not (Var x)) False) _ _) c _ = Node (Lf (Not (Var x )) True)  Empty Empty 

expandNode (Node (Lf (Pred x t) False) _ _) c _ = Node (Lf (Pred x t) True) Empty Empty
expandNode (Node (Lf (Not (Pred x t) )False) _ _) c _ = Node (Lf (Not (Pred x t)) True) Empty Empty


expandNode (Node (Lf (And x y) False) _ _) c _ = Node f' xy' Empty 
      where  f' = Lf (And x y) True
             xy' = Node (Lf x False) (Node (Lf y False) Empty Empty) Empty
 
expandNode (Node (Lf (Or x y) False) _ _) c _ = Node f' x' y'
  where f' = Lf (Or x y) True
        x' = Node (Lf x False) Empty Empty
        y' = Node (Lf y False) Empty Empty

expandNode (Node (Lf (Imply x y) False) _ _) c _ = Node f' x' y'
  where f' =  Lf (Imply x y) True 
        x' = Node (Lf (Not (x)) False) Empty Empty
        y' = Node (Lf y False) Empty Empty 

expandNode (Node (Lf (Not (Imply x y)) False) _ _) c _ = Node f' xy' Empty 
  where f' = (Lf (Not (Imply x y)) True)
        xy' = (Node (Lf x False) (Node (Lf (Not y) False) Empty Empty) Empty)    

-- Double negation law
expandNode (Node (Lf (Not (Not x)) False) _ _) c _  =  Node f' x' Empty
  where f' = (Lf (Not (Not x)) False)  
        x' = (Node (Lf x False) Empty Empty) 
-- De morgans laws
expandNode (Node (Lf (Not (Or x y)) False) _ _) c _   =  Node f' xy' Empty
  where f' = (Lf (Not (Or x y)) True)
        
        xy' = (Node (Lf (Not x) False) (Node (Lf (Not y) False) Empty Empty) Empty )

expandNode (Node (Lf (Not (And x y)) False) _ _) c _  =  Node f' x' y'
  where f' = (Lf (Not (And x y)) True) 
        x' = Node (Lf (Not x) False) Empty Empty
        y' = Node (Lf (Not y) False) Empty Empty

-- FOL rules 

expandNode (Node (Lf f@(Exist x f') False) _ _) c (_, skols) =   Node f1 xy' Empty
  where f1 = (Lf (Exist x f') True)
        sf = skolemFunc f (skols!!c)
        (Exist x f'') = subst f sf
        xy' = (Node (Lf (f'') False) Empty Empty) 

expandNode (Node (Lf f@(ForAll x f') False) _ _) c (fvars,_) = Node f1 xy' Empty
  where f1 = (Lf (ForAll x f') True)
        ForAll x f'' = subst f (Variable (fvars!!c))
        xy' = (Node (Lf(f'' ) False) Empty Empty)  

expandNode (Node (Lf (Not (ForAll x f)) False ) l r) c v = expandNode (Node (Lf (Exist x (Not f)) False) Empty Empty) c v

expandNode (Node (Lf (Not (Exist x f)) False ) l r) c v = expandNode (Node (Lf (ForAll x (Not f)) False) Empty Empty) c v



{-
  insertLR - takes a Lfs and places each argument on the next 
  left and right empty sub tree in an existing tree (Beta rule)
-}
insertLR :: Tree Lf -> Tree Lf -> Tree Lf -> Tree Lf 
insertLR leftF rightF tree@(Node x l r )
  | l == Empty = (Node x leftF rightF)
  | b == Empty && c == Empty = Node x (Node a leftF rightF) r
  | otherwise = insertLR leftF rightF l 
    where (Node a b c) = l
{-
expands a formula and adds the formulas onto the end of the tree depending on whether its an alpha or beta rule.
-}
rules :: Tree Lf -> Tree Lf -> Int ->([String],[String]) -> Tree Lf 
rules Empty tree _  _ = tree 
rules node Empty _ _ = node
rules node tree c lists  =   insertLR l r tree
    where (Node a l r) = expandNode node c lists


-- get variable 
getVar :: Formula -> Formula
getVar (Not formula) = formula
getVar formula = formula

--check for a closed tree 
treeIsClosed :: [Formula] -> Bool 
treeIsClosed [] = False 
treeIsClosed list@(x:xs)
  | var `elem` list && (Not var `elem` list) = True
  | otherwise = treeIsClosed xs
    where var = getVar x 

-- Collect literals of a tree of pred logic 
literals :: [Formula] -> [Formula] -> [Formula]
literals [] lits = lits 
literals (x@(Pred _ _):xs) lits = literals xs (x:lits)
literals (x@(Not (Pred _ _)):xs) lits = literals xs (x:lits )
literals (x:xs) lits = literals xs lits
--collect literals in list of list of FOL formulas
treeliterals :: [[Formula]] -> [[Formula]] -> [[Formula]]
treeliterals (x:[]) list = (literals x []):list
treeliterals (x:xs) list =  treeliterals xs (litTree)
  where litTree = (literals x []):list


-- check for closed tableaux
tableauxIsClosed :: [[Formula]] -> Bool 
tableauxIsClosed [] = True 
tableauxIsClosed (x:xs) 
  | treeIsClosed x = tableauxIsClosed xs 
  | otherwise = False

--Gets branches of a tree
branch :: Tree Lf -> [[Formula]]
branch Empty = [[]]
branch (Node (Lf formula _) Empty Empty) =  [[formula]]
branch (Node (Lf formula _) l r) 
  | r == Empty =  map (formula:) (branch l)
  | otherwise =  map (formula :) (branch l++ branch r)
            


-- createTableaux :: Tree Lf  -> Tree Lf
-- createTableaux Empty = Empty 
-- createTableaux (Node (Lf (Var x) False) l r) = Node (Lf (Var x) True) (createTableaux l) (createTableaux r)  
-- createTableaux (Node (Lf (Not (Var x)) False) l r) = Node (Lf (Not (Var x)) True) (createTableaux l) (createTableaux r)  
-- createTableaux (Node (Lf (Pred x t) False) l r) = Node (Lf (Pred x t) True) (createTableaux l) (createTableaux r)
-- createTableaux (Node (Lf (Not (Pred x t)) False) l r) = Node (Lf (Not (Pred x t)) True) (createTableaux l) (createTableaux r)

-- createTableaux f@(Node (Lf formula expanded) l r)
--   | expanded =  Node (Lf formula expanded) (traceShow ("building left subtree: expanded", f)   createTableaux l) (traceShow ("building right subtree: expanded", f)  createTableaux r)
--   | otherwise =  createTableaux $ rules f (Node (Lf formula True) (traceShow("building left subtree:not expanded", f) createTableaux l)  (traceShow ("building right subtree:  not expanded", f) createTableaux r)) 0



predTableaux ::  Tree Lf -> Int -> ([String], [String]) -> Tree Lf 
predTableaux Empty _ _ = Empty
predTableaux (Node (Lf (Pred x t) False) l r) c v = Node (Lf (Pred x t) True) (predTableaux l (c) v) (predTableaux r (c) v)
predTableaux (Node (Lf (Not (Pred x t)) False) l r) c v = Node (Lf (Not (Pred x t)) True) (predTableaux l c v) (predTableaux r c v)
predTableaux f@(Node (Lf formula True) l r)  c (fvars,skols) =   Node (Lf formula True) (predTableaux l (c+1) (fvars', skols')) (predTableaux r (c+2) (fvars', skols'))
  where (fvars', skols') = ((drop (c+1) fvars), (drop (c+1) skols))
        (fvars'', skols'') = ((drop (c+2) fvars), (drop (c+2) skols))
predTableaux f@(Node (Lf formula False) l r ) c (fvars,skols) = predTableaux newTree (c) (fvars,skols)
  where newTree = rules (f) (Node (Lf formula True) (predTableaux l (c+3) (fvars', skols'))  (predTableaux l (c+4) (fvars'', skols''))) c (fvars,skols)
        (fvars', skols') = ((drop (c+3) fvars), (drop (c+3) skols))
        (fvars'', skols'') = ((drop (c+4) fvars), (drop (c+4) skols))

-- isTautology :: Formula -> Bool 
-- isTautology = tableauxIsClosed . branch . createTableaux . createNode 

test :: [a]-> [a]
test [] = [] 
test list = test (drop 1 list)


p26 :: Formula
p26 = Or (And (Or (And p24 p24) (And p24 p24)) (Or (And p24 p24) (And p24 p24))) (And (Or (And p24 p24) (And p24 p24)) (Or (And p24 p24) (And p24 p24))) 

p24 :: Formula
p24 = And (And (Imply (And (Or (Or (Or (Not (And (Not (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))))) (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))))))) (Var 'C')) (And (Or (Not (And (Not (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))))) (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))))))) (Var 'C')) (Var 'C'))) (Not (Or (Not (And (Not (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))))) (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))))))) (Var 'C')))) (Or (Not (And (Not (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))))) (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))))))) (Var 'C'))) (And (Imply (And (Or (Or (Or (Not (And (Not (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))))) (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))))))) (Var 'C')) (And (Or (Not (And (Not (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))))) (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))))))) (Var 'C')) (Var 'C'))) (Not (Or (Not (And (Not (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))))) (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))))))) (Var 'C')))) (Or (Not (And (Not (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))))) (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))))))) (Var 'C'))) (And (And (Or (Or (Or (Not (And (Not (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))))) (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))))))) (Var 'C')) (And (Or (Not (And (Not (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))))) (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))))))) (Var 'C')) (Var 'C'))) (Not (Or (Not (And (Not (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))))) (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))
 (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))))))) (Var 'C')))) (Or (Not (And (Not (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))))) (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))))))) (Var 'C'))) (Var 'C'))) (And (And (Or (Or (Or (Not (And (Not (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply
 (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))))) (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))))))) (Var 'C')) (And (Or (Not (And (Not (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))))) (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))))))) (Var 'C')) (Var 'C'))) (Not (Or (Not (And (Not (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))))) (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var
 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))))))) (Var 'C')))) (Or (Not (And (Not (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))))) (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))))))) (Var 'C'))) (Var 'C')))) (Imply (And (Or (Or (Or (Not (And (Not (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))))) (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))))))) (Var 'C')) (And (Or (Not (And (Not (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))))) (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply
 (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))))))) (Var 'C')) (Var 'C'))) (Not (Or (Not (And (Not (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))))) (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var
 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))))))) (Var 'C')))) (Or (Not (And (Not (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))))) (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var
 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))))))) (Var 'C'))) (Var 'C'))) (Imply (And (Imply (And (Or (Or (Or (Not (And (Not (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var
 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))))) (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))))))) (Var 'C')) (And (Or (Not (And (Not (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))))) (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))))))) (Var 'C')) (Var 'C'))) (Not (Or (Not (And (Not (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))))) (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))))))) (Var 'C')))) (Or (Not (And (Not (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))))) (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))))))) (Var 'C'))) (And (Imply (And (Or (Or (Or (Not (And (Not (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))))) (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))))))) (Var 'C')) (And (Or (Not (And (Not (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))))) (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))))))) (Var 'C')) (Var 'C'))) (Not (Or (Not (And (Not (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply
 (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))))) (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))))))) (Var 'C')))) (Or (Not (And (Not (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))))) (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))))))) (Var 'C'))) (And (And (Or (Or (Or (Not (And (Not (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))))) (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))))))) (Var 'C')) (And (Or (Not (And (Not (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))))) (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))))))) (Var 'C')) (Var 'C'))) (Not (Or (Not (And (Not (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))))) (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))))))) (Var 'C')))) (Or (Not (And (Not (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))))) (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))))))) (Var 'C'))) (Var 'C'))) (And (And (Or (Or (Or (Not (And (Not (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A')
 (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))))) (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))))))) (Var 'C')) (And (Or (Not (And (Not (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))))) (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))))))) (Var 'C')) (Var 'C'))) (Not
 (Or (Not (And (Not (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))))) (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))))))) (Var 'C')))) (Or (Not (And (Not (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))))) (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))))))) (Var 'C'))) (Var 'C')))) (Imply (And (Or (Or (Or (Not (And (Not (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))))) (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))))))) (Var 'C')) (And (Or (Not (And (Not (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))))) (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))))))) (Var 'C')) (Var 'C'))) (Not (Or (Not (And (Not (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))))) (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And
 (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))))))) (Var 'C')))) (Or (Not (And (Not (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))))) (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))))))) (Var 'C'))) (Var 'C'))) (And (Imply (And (Or (Or (Or (Not (And (Not (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var
 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))))) (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))))))) (Var 'C')) (And (Or (Not (And (Not (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))))) (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))))))) (Var 'C')) (Var 'C'))) (Not (Or (Not (And (Not (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))))) (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))))))) (Var 'C')))) (Or (Not (And (Not (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))))) (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))))))) (Var 'C'))) (And (Imply (And (Or (Or (Or (Not (And (Not (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))))) (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))))))) (Var 'C')) (And (Or (Not (And (Not (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))))) (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))))))) (Var 'C')) (Var 'C'))) (Not (Or (Not (And (Not (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))))) (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))))))) (Var 'C')))) (Or (Not (And (Not (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))))) (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))))))) (Var 'C'))) (And (And (Or (Or (Or (Not (And (Not (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))))) (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))))))) (Var 'C')) (And (Or (Not (And (Not (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))))) (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))))))) (Var 'C')) (Var 'C'))) (Not (Or (Not (And (Not (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))))) (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))))))) (Var 'C')))) (Or (Not (And (Not (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))))) (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A')
 (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))))))) (Var 'C'))) (Var 'C'))) (And (And (Or (Or (Or (Not (And (Not (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply
 (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))))) (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))))))) (Var 'C')) (And (Or (Not (And (Not (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))))) (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))))))) (Var 'C')) (Var 'C'))) (Not (Or (Not (And (Not (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))))) (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And
 (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))))))) (Var 'C')))) (Or (Not (And (Not (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))))) (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))))))) (Var 'C'))) (Var 'C')))) (Imply (And (Or (Or (Or (Not (And (Not (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))))) (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))))))) (Var 'C')) (And (Or (Not (And (Not (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))))) (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))))))) (Var 'C')) (Var 'C'))) (Not (Or (Not (And (Not
 (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))))) (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var
 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))))))) (Var 'C')))) (Or (Not (And (Not (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))))) (Or (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A'))))) (And (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A') (Var 'A')))) (And (Imply (Var 'A') (And (Var 'A') (Var 'A'))) (Imply (Var 'A') (And (Var 'A')
 (Var 'A')))))))) (Var 'C'))) (Var 'C'))))