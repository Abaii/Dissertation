import Trees
import Tautologychecker
import Debug.Trace

-- List of formula used for testing
formulae :: [Formula]
formulae = [(And (Var 'A') (Var 'B')),    
            (Or  (Var 'A') (Var 'B')), 
            (Imply (Var 'A') (Var 'B')),
            (Not (Var 'A')),
            (Or  (Var 'A') (Not (Var 'A'))),
            (And (Var 'A') (Not (Var 'A'))),
            (Imply (And (Imply (Var 'A') (Var 'B')) (Imply (Var 'B') (Var 'C'))) (Imply (Var 'A') (Var 'C'))), -- tautology
            (Imply (And (And (Or (Var 'A') (Var 'B')) (Imply (Var 'A') (Var 'C'))) (Imply (Var 'B') (Var 'C'))) (Var 'C')), -- tautology
            (And (Var 'A') (Imply (Var 'C') (Var 'A'))),
            (Imply (Var 'P') (Not (Not (Var 'P')))),
            (Or (Var 'B') (And (Var 'A') (Var 'C'))),
            (Or (Not( And (Or (Var 'A') (Var 'B')) (Or (Not (Not (Var 'A'))) (Not (Var 'B'))))) (Var 'A')),
            (Not (And (Var 'Q') (Or (Var 'Q') (Var 'P')))),
            (Not (Imply (Var 'Q') (And (Var 'A') (Var 'B')))),
            (Imply (And (Imply (Var 'A') (Var 'B')) (Imply (Var 'B') (Var 'C'))) (Imply (Var 'A') (Var 'C'))),
            (Or (Not( And (Or (Var 'A') (Var 'B')) (Or (Not (Not (Var 'A'))) (Not (Var 'B'))))) (Var 'A')),
            (Imply (Var 'P') (Imply (Var 'S') (Imply (Var 'Q') (Var 'P')))),
            (Imply (Not (Not (Var 'P'))) (Var 'P'))

            
            
            

        
            
            
            
            
            


           ]
example :: Formula 
example = (Imply (And (Imply (Var 'A') (Var 'B')) (Imply (Var 'B') (Var 'C'))) (Imply (Var 'A') (Var 'C')))
            
applyCheckers :: [Formula] -> [(Bool, Bool)]
applyCheckers [] = []
applyCheckers (x:xs) = (a,b):applyCheckers xs
  where a = isTautology x 
        b = isTaut x

-- compareResults: calculate how many of the results are the same
compareResults :: [(Bool, Bool)] -> Int -> Int
compareResults [] counter = counter
compareResults (x:xs) counter 
  | a == b = compareResults xs (counter + 1)
  | otherwise = compareResults xs counter
    where (a,b) = x

calcPercentage :: [(Bool, Bool)] -> Float 
calcPercentage results = (correct / total) * 100
  where correct = fromIntegral $ compareResults results 0
        total = fromIntegral $ length(results)

showPercentage :: Float 
showPercentage = calcPercentage $ applyCheckers formulae

