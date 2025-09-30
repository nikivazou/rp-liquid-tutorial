{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
module Solved.Deep where 

import Prelude hiding ((++), reverse)
import ProofCombinators
{-@ infixr ++ @-}

{-@ rightId :: xs:[a] -> { xs ++ [] = xs } @-}
rightId :: [a] -> () 
rightId [] = ()
rightId (_:xs) = rightId xs  









{-@ assoc :: xs:[a] -> ys:[a] -> zs:[a] 
          -> { xs ++ (ys ++ zs) == (xs ++ ys) ++ zs } @-}
assoc :: [a] -> [a] -> [a] -> ()
assoc [] _ _ = ()
assoc (_:xs) ys zs = assoc xs ys zs    








{-@ rewriteWith distributivityRW [assoc, rightId] @-}
distributivityRW :: [a] -> [a] -> () 
{-@ distributivityRW :: xs:[a] -> ys:[a] 
                   -> { v:() | reverse (xs ++ ys) == reverse ys ++ reverse xs }  @-}
distributivityRW [] ys = () 
distributivityRW (x:xs) ys = distributivityRW xs ys

distributivity :: [a] -> [a] -> () 
{-@ distributivity :: xs:[a] -> ys:[a] 
                   -> { reverse (xs ++ ys) == reverse ys ++ reverse xs }  @-}
distributivity [] ys
    =   reverse ([] ++ ys)
    === reverse ys
        ? rightId (reverse ys)
    === reverse ys ++ [] 
    === reverse ys ++ reverse []
    *** QED 


distributivity (x:xs) ys 
  =   reverse ((x:xs) ++ ys) 
  === reverse (x:(xs ++ ys))
  === reverse (xs ++ ys) ++ [x]
        ? distributivity xs ys
  === reverse ys ++ reverse xs ++ [x]
     ? assoc (reverse ys) (reverse xs) [x]
  === reverse ys ++ reverse (x:xs)
  *** QED 









---------------------------
-- Reflected Definitions --
---------------------------

{-@ reflect ++ @-}
(++) :: [a] -> [a] -> [a]
[]     ++ ys = ys 
(x:xs) ++ ys = x:(xs++ys)

{-@ reflect reverse @-}
reverse :: [a] -> [a]
reverse [] = [] 
reverse (x:xs) = reverse xs ++ [x]
