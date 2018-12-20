module Lambda

%access public export
%default total

data Term = Var Nat 
          | Lam Term
          | App Term Term

Term0 : Term
Term0 = App (Lam $ App (Var Z) (Var Z)) (Lam $ Var Z)

Term1 : Term
Term1 = App (App (Lam $ Var Z) (Lam $ Var Z)) (Lam $ Var Z)

Term2 : Term
Term2 = App (Lam $ Var Z) (App (Lam $ Var Z) (Lam $ Var Z))

Result : Term
Result = Lam $ Var Z