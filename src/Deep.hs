{-@ LIQUID "--reflection" @-}
module Deep where 

import Prelude hiding ((++), reverse)
import Language.Haskell.Liquid.ProofCombinators  
{-@ infixr ++ @-}
{-@ reflect ++ @-}


{-@ rightId :: xs:[a] -> { xs ++ [] = xs } @-}
rightId :: [a] -> () 
rightId  = undefined 








{- LIQUID "--ple" @-}
















{-@ assoc :: xs:[a] -> ys:[a] -> zs:[a] 
          -> { xs ++ (ys ++ zs) == (xs ++ ys) ++ zs } @-}
assoc :: [a] -> [a] -> [a] -> ()
assoc = undefined 


 












distributivity :: [a] -> [a] -> () 
{-@ distributivity :: xs:[a] -> ys:[a] 
                   -> { reverse (xs ++ ys) == reverse ys ++ reverse xs }  @-}
distributivity = undefined 








{- rewriteWith distributivity [assoc, rightId] @-}

















---------------------------
-- Reflected Definitions --
---------------------------

(++) :: [a] -> [a] -> [a]
[]     ++ ys = ys 
(x:xs) ++ ys = x:(xs++ys)

{-@ reflect reverse @-}
reverse :: [a] -> [a]
reverse [] = [] 
reverse (x:xs) = reverse xs ++ [x]
