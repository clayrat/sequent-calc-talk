module LKConn

import List

%access public export
%default total

data Ty = A | Imp Ty Ty | Prod Ty Ty | Sum Ty Ty

mutual 
  data Cmd : List Ty -> List Ty -> Type where 
    C : Term g a d -> CoTerm g a d -> Cmd g d

  data Term : List Ty -> Ty -> List Ty -> Type where
    Var  : Elem a g -> Term g a d
    Mu   : Cmd g (a::d) -> Term g a d
    Lam  : Term (a::g) b d -> Term g (Imp a b) d
    Pair : Term g a d -> Term g b d -> Term g (Prod a b) d
    Inl  : Term g a d -> Term g (Sum a b) d
    Inr  : Term g b d -> Term g (Sum a b) d

  data CoTerm : List Ty -> Ty -> List Ty -> Type where
    CoVar : Elem a d -> CoTerm g a d
    Mut   : Cmd (a::g) d -> CoTerm g a d
    AppC  : Term g a d -> CoTerm g b d -> CoTerm g (Imp a b) d
    MatP  : Cmd (a::b::g) d -> CoTerm g (Prod a b) d
    MatS  : Cmd (a::g) d -> Cmd (b::g) d -> CoTerm g (Sum a b) d
