module Type 
  ( Type(..)
  , prettyType 
  ) where
  
import Data.List.Unicode ((⧺))

data Type
  = TFun Type Type
  | TVar String
  deriving (Show, Eq)

prettyType ∷ Type -> String
prettyType (TFun c@(TFun _ _) d) = 
  "(" ⧺ prettyType c ⧺ ")" ⧺ " -> " ⧺ prettyType d 
prettyType (TFun c d) = prettyType c ⧺ " -> " ⧺ prettyType d 
prettyType (TVar v) = v 