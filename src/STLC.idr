module STLC

import Data.List

%access public export
%default total

data Ty = A | Imp Ty Ty
infix 5 ~>
(~>) : Ty -> Ty -> Ty
(~>) = Imp

data Term : List Ty -> Ty -> Type where
  Var : Elem a g                  -> Term g a 
  Lam : Term (a::g) b             -> Term g (a~>b)
  App : Term g (a~>b) -> Term g a -> Term g b
    
TestTy : Ty
TestTy = A ~> A

-- Term1 not typeable!
  
Term2 : Term [] TestTy
Term2 = App (App (Lam $ Var Here) (Lam $ Var Here)) (Lam $ Var Here)
  
Term3 : Term [] TestTy
Term3 = App (Lam $ Var Here) (App (Lam $ Var Here) (Lam $ Var Here))
  
Result : Term [] TestTy
Result = Lam $ Var Here  