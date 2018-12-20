module LKLamApp

import Data.List
import List
import STLC

%access public export
%default total

mutual 
  data Cmd : List Ty -> List Ty -> Type where 
    C : Term g a d -> CoTerm g a d -> Cmd g d

  data Term : List Ty -> Ty -> List Ty -> Type where
    Var  : Elem a g -> Term g a d
    Mu   : Cmd g (a::d) -> Term g a d
    MatC : Cmd (a::g) (b::d) -> Term g (a~>b) d

  data CoTerm : List Ty -> Ty -> List Ty -> Type where
    CoVar : Elem a d -> CoTerm g a d
    Mut   : Cmd (a::g) d -> CoTerm g a d
    AppC  : Term g a d -> CoTerm g b d -> CoTerm g (a~>b) d

mutual    
  shiftCmd : {auto is1 : IsSubset g g1} -> {auto is2 : IsSubset d d1} -> Cmd g d -> Cmd g1 d1    
  shiftCmd (C t e) = C (shiftTerm t) (shiftCoTerm e)

  shiftTerm : {auto is1 : IsSubset g g1} -> {auto is2 : IsSubset d d1} -> Term g a d -> Term g1 a d1    
  shiftTerm {is1}       (Var el) = Var $ shift is1 el
  shiftTerm       {is2} (Mu c)   = Mu $ shiftCmd {is2=Cons2 is2} c
  shiftTerm {is1} {is2} (MatC c) = MatC $ shiftCmd {is1=Cons2 is1} {is2=Cons2 is2} c

  shiftCoTerm : {auto is1 : IsSubset g g1} -> {auto is2 : IsSubset d d1} -> CoTerm g a d -> CoTerm g1 a d1    
  shiftCoTerm       {is2} (CoVar el)   = CoVar $ shift is2 el
  shiftCoTerm {is1}       (Mut c)      = Mut $ shiftCmd {is1=Cons2 is1} c
  shiftCoTerm             (AppC t e)   = AppC (shiftTerm t) (shiftCoTerm e)

lam : Term (a::g) b d -> Term g (Imp a b) d
lam t = 
  MatC $ C (shiftTerm t) (CoVar Here)

app : Term g (Imp a b) d -> Term g a d -> Term g b d
app t u = 
  Mu $ C (shiftTerm t) 
         (AppC (shiftTerm u) (CoVar Here))

let_ : Term g a d -> Term (a::g) b d -> Term g b d    
let_ t u = Mu $ C (shiftTerm t) 
                  (Mut $ C (shiftTerm u) (CoVar Here))

callcc : Term g (Imp (Imp a b) a) (a::d) -> Term g a d
callcc f = 
  Mu $ C f
         (AppC 
           (MatC $ C (Var Here) (CoVar $ There Here))
           (CoVar Here))                  
