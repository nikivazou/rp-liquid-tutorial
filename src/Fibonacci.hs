{-@ LIQUID "--reflection"     @-}

module Fibonacci where

import ProofCombinators

------------------------------------------------------------------------------------------
-- OUTLINE OF THE TUTORIAL
------------------------------------------------------------------------------------------
-- | Let's define the Fibonacci function and prove some properties about it.
-- | 0. Define fibonacci and prove it terminates. 
-- | 1. Light Verification 
-- | 2. Deep Verification
-- | 3. Reachability
------------------------------------------------------------------------------------------



------------------------------------------------------------------------------------------
-- | 0. Definition and Termination
------------------------------------------------------------------------------------------

{-@ LIQUID "--no-termination" @-}
fib :: Int -> Int
fib i | i == 0     = 1 
      | i == 1     = 1 
      | otherwise  = fib (i-1) + fib (i-2)


------------------------------------------------------------------------------------------
-- | 1   Light Verification
------------------------------------------------------------------------------------------
-- | 1.1 The result is always >= the input
-- {-@ fib :: i:Nat -> {v:Nat | i <= v }  @-}


-- | 1.2 The parity of the result follows a pattern based on i mod 3
-- {-@ fib :: i:Nat -> {v:Nat | fibMod3 i v }  @-}
------------------------------------------------------------------------------------------

{-@ inline fibMod3 @-}
fibMod3 :: Int -> Int -> Bool
fibMod3 i v = if i `mod` 3 == 0 || i `mod` 3 == 1 then v `mod` 2 == 1 else v `mod` 2 == 0


------------------------------------------------------------------------------------------
-- | 2   Deep Verification
-- | 2.1 What is fib 0, 1, 3, and 16?
-- | 2.2 Fibonacci is increasing 
-- | 2.3 Fibonacci is monotonic
------------------------------------------------------------------------------------------

------------------------------------------------------------------------------------------
-- | 2.1 What is fib 0, 1, 3, and 16?
------------------------------------------------------------------------------------------

-- | To express properties about fib, **extrinsically**, ie outside of its type signature, 
-- | we simply use the unit type `()` refined with the property we want to prove.

{-@ fib0 :: () -> {v:() |  fib 0 == 1 } @-}
fib0 :: () -> ()
fib0 _ = undefined  

-- | But, the Haskell functions, like fib, are not allows by default in the refinement logic.

-- | The reflection flag allows us to use fib in specifications.
-- | After reflection, each call of fib is unfolded exactly once in the SMT solver.
-- | This is sufficient to prove fib facts up to fib 2 automatically.

{-@ reflect fib @-}


{-@ fib1 :: () -> { fib 1 == 1 } @-}
fib1 :: () -> ()
fib1 _ = undefined 


{-@ fib3 :: () -> { fib 3 == 3 } @-}
fib3 :: () -> ()
fib3 _ = undefined

-- | To automate such kind of standard evaluation steps, we can use the PLE flag.

{-@ LIQUID "--ple" @-}

fib3ple :: () -> ()
{-@ fib3ple :: () -> { fib 3 == 3 } @-}
fib3ple _ = ()


{-@ fib16 :: { fib 16 == 1597 } @-}
fib16 :: () -> ()
fib16 _ = ()


------------------------------------------------------------------------------------------
-- | 2.2 Fibonacci is increasing 
------------------------------------------------------------------------------------------
-- | To prove that fib is increasing, we need to prove a lemma first:
-- | fib i <= fib (i+1)

{-@ fibIncr :: i:Nat -> { fib i <= fib (i+1) } @-}
fibIncr :: Int -> ()
fibIncr = undefined 


-- | Note that Liquid Haskell checks that the proof is terminating and that all cases are covered.
-- | It is a _mathematical_ proof! 


------------------------------------------------------------------------------------------
-- | 2.3 Fibonacci is monotonic
------------------------------------------------------------------------------------------


{-@ fibMono :: i:Nat -> j:{Nat | i < j} -> { fib i <= fib j } @-}
fibMono :: Int -> Int -> ()
fibMono i j  = undefined 

-- Interestingly, the proof requires the `fibIncr` lemma, but not the definition of `fib` itself!
-- So, we can abstract away the definition of `fib` and state that 
-- each increasing function is monotonic! 




-- | With that, monotonicity of Fibonacci can be proved as:




------------------------------------------------------------------------------------------
-- | 3   Reachability
------------------------------------------------------------------------------------------

-- As a final exercise, and to state on topic, let's use Liquid Haskell to
-- determine which values can fib reach. 

-- n can be reached by fib iff 
-- there exists an x such that fib x = n
-- equivalently
-- (x:Nat, {fib x = n})

{- 
   As a final exercise, and to state on topic, let's use Liquid Haskell to
   determine which values can fib reach. 

  n can be reached by fib iff 
    there exists an x such that fib x = n
      _equivalently_
    (x:Nat, {fib x = n})

  _ie,_ existentials are encoded as dependent pairs
        with the first component being the witness.
-}


------------------------------------------------------------------------------------------
-- | 3.1 Is 8 reachable by fib?
------------------------------------------------------------------------------------------

{-@ reachable8 :: () -> (x::Nat, { v:() | fib x == 8}) @-}
reachable8 :: () -> (Int, ())
reachable8 _ = undefined 


------------------------------------------------------------------------------------------
-- | 3.2 Is 7 reachable by fib?
------------------------------------------------------------------------------------------

{-
To show non reachability, we need to negate the existential. 
      not (exists x. fib x = 7)
     equivalently
      (exists x. fib x = 7) -> False

      _ie_, negation is encoded as an implication to False.
-}

{-@ unreachable7 :: () -> ((x::Nat, { v:() | fib x == 7}) -> ({v:() |  False})) @-}
unreachable7 :: () -> ((Int, ()) -> ())
unreachable7 _ = undefined 
