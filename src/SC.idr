module SC

import Data.List
import List
import STLC

%access public export
%default total

data SC : List Ty -> Ty -> Type where
  VarS : Elem a g -> SC g a
  Cut  : SC g a -> SC (a::g) b -> SC g b
  ImpL : SC g a -> SC (b::g) c -> SC ((a~>b)::g) c
  ImpR : SC (a::g) b -> SC g (a~>b)

data LJ : List Ty -> Ty -> Type where
  AxJ   : LJ [a] a
  CutJ  : LJ g a -> LJ (a::g) b -> LJ g b
  ImpLJ : LJ g a -> LJ (b::g) c -> LJ ((a~>b)::g) c
  ImpRJ : LJ (a::g) b -> LJ g (a~>b)
  WSJ   : LJ g b -> LJ (a::g) b
  CSJ   : LJ (a::a::g) b -> LJ (a::g) b
  PSJ   : LJ (g ++ a::b::d) c -> LJ (g ++ b::a::d) c