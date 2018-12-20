module LKConn

import Data.List
import List

%access public export
%default total

data Ty = A | Imp Ty Ty | Prod Ty Ty | Sum Ty Ty

infix 5 ~>
(~>) : Ty -> Ty -> Ty
(~>) = Imp

infix 5 :*:
(:*:) : Ty -> Ty -> Ty
(:*:) = Prod

infix 5 :+:
(:+:) : Ty -> Ty -> Ty
(:+:) = Sum

mutual 
  data Cmd : List Ty -> List Ty -> Type where 
    C : Term g a d -> CoTerm g a d -> Cmd g d

  data Term : List Ty -> Ty -> List Ty -> Type where
    Var  : Elem a g -> Term g a d
    Mu   : Cmd g (a::d) -> Term g a d
    Lam  : Term (a::g) b d -> Term g (a~>b) d
    Pair : Term g a d -> Term g b d -> Term g (a:*:b) d
    Inl  : Term g a d -> Term g (a:+:b) d
    Inr  : Term g b d -> Term g (a:+:b) d

  data CoTerm : List Ty -> Ty -> List Ty -> Type where
    CoVar   : Elem a d -> CoTerm g a d
    Mut     : Cmd (a::g) d -> CoTerm g a d
    AppCon  : Term g a d -> CoTerm g b d -> CoTerm g (a~>b) d
    MatProd : Cmd (a::b::g) d -> CoTerm g (a:*:b) d
    MatSum  : Cmd (a::g) d -> Cmd (b::g) d -> CoTerm g (a:+:b) d
