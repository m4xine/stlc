module Utility 
  ( (<<$>>)
  ) where

(<<$>>) ∷ (Functor f, Functor g) ⇒ (α → β) → f (g α) → f (g β)
(<<$>>) = fmap . fmap
infixl 4 <<$>>