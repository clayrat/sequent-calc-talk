module KAM

import Data.List
import Lambda

%access public export
%default total

mutual
  Env : Type 
  Env = List Clos

  data Clos = Cl Term Env

Stack : Type
Stack = List Clos

State : Type
State = (Term, Env, Stack)

step : State -> Maybe State
step (Var  Z   , Cl t e::_,    s) = Just (    t,    e,         s)
step (Var (S n),      _::e,    s) = Just (Var n,    e,         s)
step (Lam t    ,         e, c::s) = Just (    t, c::e,         s)
step (App t u  ,         e,    s) = Just (    t,    e, Cl u e::s)
step  _                           = Nothing

stepIter : State -> (Nat, Maybe State)
stepIter s = loop Z s
  where
  loop : Nat -> State -> (Nat, Maybe State)
  loop n s1 = case step s1 of
    Nothing => (n, Just s1)
    Just s2 => assert_total $ loop (S n) s2

run : Term -> (Nat, Maybe State)
run t = stepIter (t, [], [])

test00 : run Term0 = (7, Just (Result, [], []))
test00 = Refl

test01 : run Term1 = (6, Just (Result, [], []))
test01 = Refl

test02 : run Term2 = (6, Just (Result, [], []))
test02 = Refl
