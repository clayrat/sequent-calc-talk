module KAM

import Data.List
import Lambda

%access public export
%default total

mutual
  Env : Type 
  Env = List Clos

  data Clos = Cl Term Env

data Frame = Fun Term Env | Arg Clos

Stack : Type
Stack = List Frame

data State = L Term Env Stack | R Clos Stack

step : State -> Maybe State
step (L (Var  Z)    (v::_)            s ) = Just $ R  v                                  s
step (L (Var (S n)) (_::e)            s ) = Just $ L (Var n)     e                       s
step (L (Lam t)         e             s ) = Just $ R (Cl (Lam t) e)                      s
step (L (App t u)       e             s ) = Just $ L u           e             (Fun t e::s)
step (R (Cl (Lam t)    e) (Fun t1 e1::s)) = Just $ L t1          e1 (Arg (Cl (Lam t) e)::s)
step (R (Cl (Lam t)    e) (    Arg v::s)) = Just $ L t       (v::e)                      s
step _ = Nothing

stepIter : State -> (Nat, Maybe State)
stepIter s = loop Z s
  where
  loop : Nat -> State -> (Nat, Maybe State)
  loop n s1 = case step s1 of
    Nothing => (n, Just s1)
    Just s2 => assert_total $ loop (S n) s2

run : Term -> (Nat, Maybe State)
run t = stepIter $ L t [] []

test00 : run Term0 = (11, Just $ R (Cl Result []) [])
test00 = Refl

test01 : run Term1 = (11, Just $ R (Cl Result []) [])
test01 = Refl

test02 : run Term2 = (11, Just $ R (Cl Result []) [])
test02 = Refl