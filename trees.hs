import Debug.Trace

-- IMPLEMENTING TABLEAUX WITH TREES 
data Formula = Var Char | Not Formula | And Formula Formula | Or Formula Formula | Imply Formula Formula deriving Eq
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

instance Show Formula where
    show (Var p) =  show p
    show (Not x) =  ("Not " ++ show(x))
    show (And x y) = (show(x) ++ " And " ++ show(y))
    show (Or x y) = (show(x) ++ " Or " ++ show(y))
    show (Imply x y) = (show(x) ++ " Implies " ++ show(y)) 

data Tree a = Empty | Node a (Tree a) (Tree a) deriving (Show, Eq)

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

{-
 Given a formula create the corresponding node for a tableaux tree.
-}
createNode :: Formula -> Tree Lf
createNode formula =  Node (Lf formula False) Empty Empty

expandNode :: Tree Lf -> Tree Lf 
expandNode Empty = Empty 
expandNode (Node (Lf (Var x) False) _ _) = Node (Lf (Var x) True) Empty Empty 

expandNode (Node (Lf (Not (Var x)) False) _ _) = Node (Lf (Not (Var x )) True)  Empty Empty 
        
expandNode (Node (Lf (And x y) False) _ _) = Node f' xy' Empty 
       where  f' = Lf (And x y) True
              xy' = Node (Lf x False) (Node (Lf y False) Empty Empty) Empty

expandNode (Node (Lf (Or x y) False) _ _) = Node f' x' y'
  where f' = Lf (Or x y) True
        x' = Node (Lf x False) Empty Empty
        y' = Node (Lf y False) Empty Empty

expandNode (Node (Lf (Imply x y) False) _ _) = Node f' x' y'
  where f' =  Lf (Imply x y) True 
        x' = Node (Lf (Not (x)) False) Empty Empty
        y' = Node (Lf y False) Empty Empty 
        
-- Double negation law
expandNode (Node (Lf (Not (Not x)) False) _ _) =  Node f' x' Empty
  where f' = (Lf (Not (Not x)) False)  
        x' = (Node (Lf x False) Empty Empty) 
-- De morgans laws
expandNode (Node (Lf (Not (Or x y)) False) _ _) = Node f' xy' Empty
  where f' = (Lf (Not (Or x y)) True)
        xy' = Node (Lf (Not x) False) (Node (Lf y False) Empty Empty) Empty 

expandNode (Node (Lf (Not (And x y)) False) _ _) = Node f' x' y'
  where f' = (Lf (Not (And x y)) True) 
        x' = Node (Lf (Not x) False) Empty Empty
        y' = Node (Lf (Not y) False) Empty Empty


{-
  insertL - Takes a node and inserts it into the next empty position on the left
  (Alpha rule)
-}
insertL :: Tree Lf -> Tree Lf -> Tree Lf 
insertL node Empty = node
insertL Empty tree = tree
insertL node (Node x l r) 
  | l == Empty = Node x node r
  | otherwise = Node x (insertL node l) r 


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
rules :: Tree Lf -> Tree Lf -> Tree Lf 
rules Empty tree = tree 
rules node Empty = node
rules node tree =  insertLR l r tree
    where (Node a l r) = expandNode node

{-
getBranch  - gets the branch of a tree
-}
{-
compareNode = compares one formula in a tree to another and returns boolean
-}
compareNode :: Tree Lf -> Tree Lf -> Bool
compareNode Empty Empty = True
compareNode Empty _ = False
compareNode (Node (Lf f1 _) _ _) (Node (Lf f2 _) _ _) 
  | f1 == f2 = True 
  | otherwise = False

contradiction :: Tree Lf -> Tree Lf -> Bool
contradiction f g@(Node (Lf formula _) l r) 
  | compareNode f g = True 
  | contradiction f l = True
  | contradiction f r = True 
  | otherwise = False

createTableaux :: Tree Lf  -> Tree Lf
createTableaux Empty = Empty 
createTableaux f@(Node (Lf formula expanded) l r)
  | expanded =   Node (Lf formula expanded) (createTableaux l) (createTableaux r)
  | otherwise =  createTableaux $ rules f (Node (Lf formula True) (createTableaux (l)) (createTableaux(r))) 

