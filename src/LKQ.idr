module LKQ

import Data.List
import List
import STLC

%access public export
%default total
%hide Language.Reflection.Var

mutual 
  data Cmd : List Ty -> List Ty -> Type where 
    C : Term g a d -> CoTerm g a d -> Cmd g d

  data Term : List Ty -> Ty -> List Ty -> Type where
    Val  : Value g a d -> Term g a d
    Mu   : Cmd g (a::d) -> Term g a d

  data Value : List Ty -> Ty -> List Ty -> Type where
    Var  : Elem a g -> Value g a d
    MatC : Cmd (a::g) (b::d) -> Value g (a~>b) d

  data CoTerm : List Ty -> Ty -> List Ty -> Type where
    CoVar : Elem a d -> CoTerm g a d
    Empty : CoTerm g a d
    Mut   : Cmd (a::g) d -> CoTerm g a d
    AppC  : Value g a d -> CoTerm g b d -> CoTerm g (a~>b) d

mutual    
  shiftCmd : {auto is1 : IsSubset g g1} -> {auto is2 : IsSubset d d1} -> Cmd g d -> Cmd g1 d1    
  shiftCmd (C t e) = C (shiftTerm t) (shiftCoTerm e)

  shiftTerm : {auto is1 : IsSubset g g1} -> {auto is2 : IsSubset d d1} -> Term g a d -> Term g1 a d1    
  shiftTerm       (Val v) = Val $ shiftValue v
  shiftTerm {is2} (Mu c)  = Mu $ shiftCmd {is2=Cons2 is2} c

  shiftValue : {auto is1 : IsSubset g g1} -> {auto is2 : IsSubset d d1} -> Value g a d -> Value g1 a d1    
  shiftValue {is1}       (Var el) = Var $ shift is1 el
  shiftValue {is1} {is2} (MatC c) = MatC $ shiftCmd {is1=Cons2 is1} {is2=Cons2 is2} c

  shiftCoTerm : {auto is1 : IsSubset g g1} -> {auto is2 : IsSubset d d1} -> CoTerm g a d -> CoTerm g1 a d1    
  shiftCoTerm       {is2} (CoVar el) = CoVar $ shift is2 el
  shiftCoTerm              Empty     = Empty
  shiftCoTerm {is1}       (Mut c)    = Mut $ shiftCmd {is1=Cons2 is1} c
  shiftCoTerm             (AppC t e) = AppC (shiftValue t) (shiftCoTerm e)

mutual
  subst : Cmd (a::g) d -> Value g a d -> Cmd g d
  subst (C t e) va = C (assert_total $ substTerm t va) (assert_total $ substCoTerm e va)

  substTerm : Term (a::g) c d -> Value g a d -> Term g c d
  substTerm (Val v)  va = Val $ substValue v va
  substTerm (Mu cmd) va = Mu $ subst (shiftCmd cmd) (shiftValue va)
  
  substValue : Value (a::g) c d -> Value g a d -> Value g c d
  substValue (Var  Here)      va = va
  substValue (Var (There el)) _  = Var el
  substValue (MatC cmd)       va = MatC $ subst (shiftCmd cmd) (shiftValue va)

  substCoTerm : CoTerm (a::g) c d -> Value g a d -> CoTerm g c d
  substCoTerm (CoVar el) va = CoVar el
  substCoTerm  Empty     va = Empty
  substCoTerm (Mut cmd)  va = Mut $ subst (shiftCmd cmd) (shiftValue va) 
  substCoTerm (AppC t e) va = AppC (substValue t va) (substCoTerm e va)

mutual
  cosubst : Cmd g (a::d) -> CoTerm g a d -> Cmd g d
  cosubst (C t e) ct = C (assert_total $ cosubstTerm t ct) (assert_total $ cosubstCoTerm e ct)

  cosubstTerm : Term g c (a::d) -> CoTerm g a d -> Term g c d
  cosubstTerm (Val v)    ct = Val $ cosubstValue v ct
  cosubstTerm (Mu cmd)   ct = Mu $ cosubst (shiftCmd cmd) (shiftCoTerm ct)

  cosubstValue : Value g c (a::d) -> CoTerm g a d -> Value g c d
  cosubstValue (Var el)     _  = Var el
  cosubstValue (MatC cmd)   ct = MatC $ cosubst (shiftCmd cmd) (shiftCoTerm ct)

  cosubstCoTerm : CoTerm g c (a::d) -> CoTerm g a d -> CoTerm g c d
  cosubstCoTerm (CoVar Here)       ct = ct
  cosubstCoTerm (CoVar (There el)) _  = CoVar el
  cosubstCoTerm  Empty _              = Empty
  cosubstCoTerm (Mut cmd)          ct = Mut $ cosubst cmd (shiftCoTerm ct)
  cosubstCoTerm (AppC t e)         ct = AppC (cosubstValue t ct) (cosubstCoTerm e ct)

reduce : Cmd g d -> Maybe (Cmd g d)
reduce (C (Mu c)          e        ) = Just $ cosubst c e
reduce (C (Val  v)       (Mut c)   ) = Just $ subst c v
reduce (C (Val (MatC c)) (AppC t e)) = Just $ cosubst (subst c (shiftValue t)) (shiftCoTerm e)
reduce  _                            = Nothing

reduceIter : Cmd g d -> (Nat, Maybe (Cmd g d))
reduceIter c = loop Z c 
  where
  loop : Nat -> Cmd g d -> (Nat, Maybe (Cmd g d))  
  loop n c1 = case reduce c1 of
    Nothing => (n, Just c1)
    Just c2 => assert_total $ loop (S n) c2

embedTm : STLC.Term g a -> Term g a []
embedTm (Var el)  = Val $ Var el
embedTm (Lam t)   = Val $ MatC $ C (shiftTerm $ embedTm t) (CoVar Here)
embedTm (App t u) = 
  Mu $ C (shiftTerm $ embedTm t) $ case embedTm u of
   Val v => AppC (shiftValue v) (CoVar Here)
   Mu c => Mut $ C (shiftTerm $ Mu c) (Mut $ C (Val $ Var $ There Here) (AppC (Var Here) (CoVar Here)))

extractTerm : Cmd g d -> (a ** Term g a d)
extractTerm (C {a} t _) = (a ** t)

runLKQ : STLC.Term g a -> (Nat, Maybe (b ** Term g b []))
runLKQ t = 
  let (n,r) = reduceIter $ C (embedTm t) Empty in
  (n, extractTerm <$> r)

test : runLKQ Term2 = (4, Just (TestTy ** embedTm Result))
test = Refl

test2 : runLKQ Term3 = (6, Just (TestTy ** embedTm Result))
test2 = Refl
