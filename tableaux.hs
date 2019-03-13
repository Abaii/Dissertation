import Debug.Trace

data Formula = Var Char | Not Formula | And Formula Formula | Or Formula Formula | Imply Formula Formula deriving Eq

instance Show Formula where
    show (Var p) =  show p
    show (Not x) =  ("Not " ++ show(x))
    show (And x y) = (show(x) ++ " And " ++ show(y))
    show (Or x y) = (show(x) ++ " Or " ++ show(y))
    show (Imply x y) = (show(x) ++ " Implies " ++ show(y)) 



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


p12 ::  Formula
p12 = And (Or (Not (Or (Not (And (Var 'A') (Var 'B'))) (Var 'C'))) (Or (Not (Var 'A')) (Or (Not (Var 'B')) (Var 'C')))) (Or (Not (Or (Not (Var 'A')) (Or (Not (Var 'B')) (Var 'C')))) (Or (Not (And (Var 'A') (Var 'B'))) (Var 'C')))

invalid :: Formula 
invalid = And (Var 'A') (Not (Var 'A'))
--- Remove duplicates from a list 

rmdups :: Eq a => [a]-> [a]
rmdups [] = []
rmdups (x:xs) = x : filter (/= x) (rmdups xs)

--union 2 sets
union :: Eq a=>[a] -> [a] -> [a]
union l1 l2 = rmdups (l1++l2)

--calculate all the subformulas in a given formula 
subformulas :: Formula -> [Formula]
subformulas (Var p)= (Var p):[]
subformulas (Not p)  = (Not p):subformulas p
subformulas (And p v )= (And p v):union (subformulas p) (subformulas v)
subformulas (Imply p v) = (Imply p v):union (subformulas p) (subformulas v)

--Calculate the height of a given formula 
height :: Formula -> Int
height (Var p) = 1
height (Not p) = 1 + (height p)
height (And p q ) = 1 + (max (height p) (height q))
height (Imply p q ) = 1 +( max (height p) (height q))

-- Calculate the set of propositional variables in a formula
calcVariables :: Formula -> [Char]
calcVariables (Var p) = p:[]
calcVariables (Not p) = calcVariables p
calcVariables (And p q) = union (calcVariables p) (calcVariables q)
calcVariables (Imply p q) =  union (calcVariables p) (calcVariables q)


{-
    Functions needed 
    - negate a formula ✅
    - alpha rule ✅
    - beta rule ✅
    - double negation rule ✅
    - if implication apply alpha rule and take it as not p or q ✅
    - return tree (tree represented as a list of lists of lists?)
    - add new branch to tree (add new list)
    - Check for closed tree  ✅
    - Check for closed tableaux tree ✅
    - if tree isnt closed then apply beta and alpha rules 

-}



negateFormula :: Formula -> Formula
negateFormula formula = Not (formula )

testing :: Formula -> Char 
testing  (Not (Var a) ) = a
testing1 :: Formula -> Formula
testing1 (Imply a b)= a


---TEST TABLEAUX 
tableauxOpen :: [[Formula]]
tableauxOpen = [[Not (Var 'P'), Var 'Q'], [Not (Var 'Q'), Var 'Q']]

tableauxClosed :: [[Formula]]
tableauxClosed = [[Var 'Q', Not (Var 'Q')], [Var 'P', Not(Var 'P')]]


alphaTest :: Formula 
alphaTest = Imply (Var 'P') $ Var 'Q' 

betaTest :: Formula 
betaTest = Or (Var 'P') $ Var 'Q'

doubleNegationTest :: Formula
doubleNegationTest = Not(Not (Var 'P'))

-- expansion rules, return list of list formulas
expandFormula :: Formula -> [[Formula]]
expandFormula (Var x) = [[Var x]]
expandFormula (Not (Var x)) = [[Not (Var x)]]
expandFormula (And x y) = [[x,y]]
expandFormula (Or x y) = [[x],[y]]
expandFormula (Imply x y) = [[Not x], [y]]
expandFormula (Not(Imply x y)) = [[x, Not y]]
expandFormula (Not (Not (x))) = [[x]]

-- De morgans laws 
expandFormula (Not (Or x y)) = [[Not x, Not y]]
expandFormula (Not (And x y)) = [[Not x], [Not y]]


-- get variable 
getVar :: Formula -> Formula
getVar (Not formula) = formula
getVar formula = formula

--check for a closed tree 
treeIsClosed :: [Formula] -> Bool 
treeIsClosed [] = False 
treeIsClosed list@(x:xs)
  | var `elem` list && (Not var `elem` list) = traceShow x True
  | otherwise = traceShow list $ treeIsClosed xs
    where var = getVar x 

-- check for closed tableaux 
tableauxIsClosed :: [[Formula]] -> Bool 
tableauxIsClosed [] = True 
tableauxIsClosed (x:xs) 
  | treeIsClosed x = tableauxIsClosed xs 
  | otherwise = False



generateFirstBranch :: Formula ->[Formula]
generateFirstBranch formula =  [negateFormula formula]

isAlpha :: Formula -> Bool
isAlpha (Var _) = False
isAlpha (And _ _ ) = True
isAlpha (Not(Imply _ _)) = True
isAlpha (Not (Or _ _)) = True 
isAlpha _ = False 

isLiteral :: Formula -> Bool
isLiteral (Var _) = True
isLiteral _ = False
-- --expand entire list with alpha rules 
-- expandAlpha :: [Formula]-> [Formula]
-- expandAlpha [] = []
-- expandAlpha formula@(x:xs) = rmdups $ formula ++ e ++  expandAlpha withoutHead
--         where e = concat $ expandFormula x
--               withoutHead = filter( \y-> y /= x) e

{-
      ExpandAlpha: expands a single node using an alpha rule

-}
expandAlpha :: [Formula] -> [Formula]
expandAlpha [] = []
expandAlpha formula@(x:xs) 
  | isLiteral x = formula
  | otherwise= formula ++ expanded
      where expanded = concat $ expandFormula x

{-
      expandBeta: expands a single node using an beta rule
      
-}
expandBeta :: [Formula] -> [[Formula]]
expandBeta [] = [[]]
expandBeta formula@(x:xs) = formula:expandFormula x

{-
 removeHead: removes a the head of a list of formulas
-}
removeHead :: [Formula] -> [Formula]
removeHead [] = []
removeHead formulas@(x:xs) = filter(\y -> y /= x) formulas



expandBranch :: [[Formula]] -> [[Formula]]
expandBranch [[]] = [[]]
expandBranch formula@(x:xs) 
  | (t x) /= [] && head (t x) = traceShow( t x) rmdups $ (f formula) ++ expandBranch(f withoutHeadA)
  | otherwise = rmdups $ (expandBranch withoutHeadG)++  ( concat $ g formula)

      where f = map expandAlpha
            g = map expandBeta 
            t = map isAlpha
            rmvHead = map removeHead
            withoutHeadA = rmvHead (f formula)
            withoutHeadG = rmvHead (concat $ g formula)


-- expandBranch :: [[Formula]] -> [[Formula]]
-- expandBranch [[]] = [[]]
-- expandBranch formula 
--   | a (concat formula)!!0 = g formula
--   | otherwise = concat $ concat (traceShow (formula)$ f formula)

--                     where f = map.map $ expandFormula
--                           g = map expandAlpha
--                           a = map isAlpha
                          
-- IMPLEMENTING TABLEAUX WITH TREES 
data Tree a = Empty | Node a (Tree a) (Tree a) deriving (Show, Eq)


-- Formulas on tree nodes with an 'expanded' attribute
data LabelledFormula = LabelledFormula {
  expanded :: Bool,
  formula :: !Formula
} deriving (Show, Eq)


{-
 Given a formula create the corresponding node for a tableaux tree.
-}
createNode :: Formula -> Tree LabelledFormula
createNode formula =  Node (LabelledFormula False formula) Empty Empty

expandAlphaT :: Tree Formula -> Tree Formula 
expandAlphaT (Node (Var x) l r) = Node (Var x )l r
expandAlphaT (Node (And x y ) Empty Empty) = (Node x (Node y Empty Empty) Empty )
{-
  Expand Node: Takes a formula,f , returns the expansion of F
-}
expandNode :: Tree Formula -> Tree Formula
expandNode Empty = Empty 
expandNode (Node (Var x) l r) = Node (Var x) l r
expandNode (Node (Not (Var x)) Empty Empty) = Node (Not (Var x)) Empty Empty

expandNode (Node (And x y) l  r) =   Node (And x y) (Node x (Node y Empty Empty) Empty) Empty
expandNode (Node (Or x y) Empty Empty) = Node (Or x y) ( Node x Empty Empty) $ Node y Empty Empty

expandNode (Node (Imply x y) Empty Empty) = Node (Imply x y) (Node x (Node (Not y) Empty Empty) Empty) Empty

-- Double negation law 
expandNode (Node (Not (Not x)) Empty Empty) = Node x Empty Empty

-- De morgans laws 
expandNode (Node (Not (Or x y)) Empty Empty) = Node (Not (Or x y)) (Node (Not x) (Node(Not y) Empty Empty) Empty) Empty
expandNode (Node (Not (And x y)) Empty Empty) = Node (Not (And x y)) (Node (Not x) Empty Empty) (Node (Not y) Empty Empty)


tree :: Tree Formula 
tree = Node (Var 'P') Empty Empty
tree1 :: Tree Formula
tree1 = Node (Var 'X') (Node (Var 'Q') (Node (Var 'L') Empty Empty) Empty) Empty 
-- insert: takes node and inserts it into a tree.
insert :: Tree Formula -> Tree Formula -> Tree Formula
insert Empty tree = tree
insert node Empty = node 
insert node (Node x Empty r) = Node x node r 
insert node (Node x l Empty) = Node x l node 

{-
  insertL - Takes a node and inserts it into the next empty position on the left
  (Alpha rule)
-}
insertL :: Tree Formula -> Tree Formula -> Tree Formula 
insertL node Empty = node
insertL Empty tree = tree
insertL node (Node x l r) 
  | l == Empty = Node x node r
  | otherwise = Node x (insertL node l) r 

{-
  InsertR - Takes a node and inserts it into the next empty position on the right
-}
insertR :: Tree Formula -> Tree Formula -> Tree Formula 
insertR node Empty = node
insertR Empty tree = tree 
insertR node (Node x l r)
  | r == Empty = Node x l node 
  | otherwise = Node x l (insertR node r)

{-
  insertLR - takes a formulas and places each argument on the next 
  left and right empty sub tree in an existing tree (Beta rule)
-}
insertLR :: Tree Formula -> Tree Formula -> Tree Formula -> Tree Formula 
insertLR leftF rightF (Node x l r )
  | l == Empty && r == Empty = Node x leftF rightF
  | otherwise = Node x (insertL leftF l) (insertR rightF r)
 



-- Takes the expansion of a node and create a new tree with the expansion
createTree :: [Tree Formula] -> Tree Formula -> Tree Formula 
createTree [] tree = tree
createTree e@(x:xs) tree = createTree xs (insert x tree)

{-
  Gen tableaux - create a recursive function which expands the root node.
  Call the function on l and r subtrees. 
  GenTableaux :: Tree Formula -> Tree Formula 
-- -}
-- generateTableaux :: Tree Formula -> Tree Formula 
-- generateTableaux Empty = Empty
-- generateTableaux t@(Node x l r) = traceShow(t) generateTableaux $ expansion t t

