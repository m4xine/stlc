module Expr
  ( ExprF(..)
  , Expr 
  , prettyExpr
  ) where

import  Control.Comonad.Cofree  (Cofree ((:<)))
import  Data.List.Unicode       ((⧺))
import  Text.Show.Deriving      (deriveShow1)

data ExprF α
  = EAbs String α
  | EApp α α
  | EVar String
  deriving Functor

deriveShow1 ''ExprF

type Expr = Cofree ExprF

prettyExpr ∷ Expr α → String  
prettyExpr (_ :< e) = case e of
  EAbs x e → "\\" ⧺ x ⧺ "." ⧺ prettyExpr e
  EApp f@(_ :< EAbs _ _) x → "(" ⧺ prettyExpr f ⧺ ") " ⧺ prettyExpr x 
  EApp f x → prettyExpr f ⧺ " " ⧺ prettyExpr x
  EVar x → x