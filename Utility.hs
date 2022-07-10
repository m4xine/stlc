module Utility where

(<<$>>) ∷ (Functor f, Functor g) ⇒ (α → β) → f (g α) → f (g β)
(<<$>>) = (<$>) . (<$>)
infixl 4 <<$>>