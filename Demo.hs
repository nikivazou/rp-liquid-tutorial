{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--no-termination" @-}
module Demo where 

data L a = Nil | Cons a (L a)

{-@ reflect listSum @-}
{-@ listSum :: L Nat -> Nat @-}
listSum :: L Int -> Int
listSum Nil = 0
listSum (Cons h t) = h + listSum t


{-@ reflect ones @-}
{- lazy ones @-}
{-@ ones :: {l:L Nat | listSum l < 5} @-}
ones :: L Int
ones = Cons 1 ones