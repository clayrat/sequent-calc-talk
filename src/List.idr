module List

import Data.List

%access public export
%default total

{-
data List : Type -> Type where
  Nil  :                List a  -- aka []
  (::) : a -> List a -> List a

data Elem : a -> List a -> Type where
  Here  :              Elem x (x :: xs)
  There : Elem x xs -> Elem x (y :: xs)

data Nat : Type where
  Z :        Nat
  S : Nat -> Nat
-}  

Subset : List a -> List a -> Type
Subset {a} xs ys = {x : a} -> Elem x xs -> Elem x ys

s12 : Subset [1] [2,1]
s12  Here      = There Here
s12 (There el) = absurd el

data IsSubset : List a -> List a -> Type where 
  Id    :                 IsSubset           l            l    
  Cons2 : IsSubset l m -> IsSubset (      a::l) (      a::m) 

  ConsR : IsSubset l m -> IsSubset           l  (      a::m) 
  Swap  : IsSubset l m -> IsSubset (   a::b::l) (   b::a::m)
  Rot   : IsSubset l m -> IsSubset (a::b::c::l) (c::a::b::m)  

shift : IsSubset l m -> Subset l m  
shift  Id        el                        = el
shift (Cons2 s)  Here                      = Here
shift (Cons2 s) (There  el)                = There $ shift s el

shift (ConsR s)  el                        = There $ shift s el
shift (Swap s)   Here                      = There Here
shift (Swap s)  (There  Here)              = Here
shift (Swap s)  (There (There el))         = There $ There $ shift s el
shift (Rot s)    Here                      = There Here
shift (Rot s)   (There  Here)              = There $ There Here
shift (Rot s)   (There (There  Here))      = Here
shift (Rot s)   (There (There (There el))) = There $ There $ There $ shift s el
