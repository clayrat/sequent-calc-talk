module LK

import Data.List
import List
import STLC

%access public export
%default total

mutual 
  data Cmd : List Ty -> List Ty -> Type where 
    C : Term g a d -> CoTerm g a d -> Cmd g d

  data Term : List Ty -> Ty -> List Ty -> Type where
    Var : Elem a g -> Term g a d
    Mu  : Cmd g (a::d) -> Term g a d

  data CoTerm : List Ty -> Ty -> List Ty -> Type where
    CoVar : Elem a d -> CoTerm g a d
    Mut   : Cmd (a::g) d -> CoTerm g a d

mutual    
  shiftCmd : IsSubset g g1 -> IsSubset d d1 -> Cmd g d -> Cmd g1 d1    
  shiftCmd is1 is2 (C t e) = C (shiftTerm is1 is2 t) (shiftCoTerm is1 is2 e)

  shiftTerm : IsSubset g g1 -> IsSubset d d1 -> Term g a d -> Term g1 a d1    
  shiftTerm is1 is2 (Var el) = Var $ ?wat
  shiftTerm is1 is2 (Mu c)   = Mu $ ?wat2

  shiftCoTerm : IsSubset g g1 -> IsSubset d d1 -> CoTerm g a d -> CoTerm g1 a d1    
  shiftCoTerm is1 is2 (CoVar el) = CoVar $ ?wat3
  shiftCoTerm is1 is2 (Mut c)    = Mut $ ?wat4

{-    
mutual    
  shiftCmd : {auto is1 : IsSubset g g1} -> {auto is2 : IsSubset d d1} -> Cmd g d -> Cmd g1 d1    
  shiftCmd (C t e) = C (shiftTerm t) (shiftCoTerm e)

  shiftTerm : {auto is1 : IsSubset g g1} -> {auto is2 : IsSubset d d1} -> Term g a d -> Term g1 a d1    
  shiftTerm {is1}       (Var el) = Var $ shift is1 el
  shiftTerm       {is2} (Mu c)   = Mu $ shiftCmd {is2=Cons2 is2} c

  shiftCoTerm : {auto is1 : IsSubset g g1} -> {auto is2 : IsSubset d d1} -> CoTerm g a d -> CoTerm g1 a d1    
  shiftCoTerm       {is2} (CoVar el) = CoVar $ shift is2 el
  shiftCoTerm {is1}       (Mut c)    = Mut $ shiftCmd {is1=Cons2 is1} c
  -}
