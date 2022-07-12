module Infer
  ( infer
  ) where

import            Control.Monad.Except            (ExceptT, runExceptT, MonadError (..))
import            Control.Monad.State.Lazy        (State, evalState, modify, MonadState (..))
import            Control.Comonad.Cofree          (Cofree ((:<)))
import            Data.Char                       (digitToInt)
import            Data.Maybe                      (fromMaybe)
import            Data.Monoid.Unicode             ((⊕), (∅))
import            Data.List.Unicode               ((‼), (⧺), 𝜀)
import            Data.Eq.Unicode                 ((≡))
import            Control.Category.Unicode        ((∘))
import qualified  Data.Set                  as S
import qualified  Data.Map                  as M
import            Utility                         ((<<$>>))
import            Type                            (Type(..))
import            Expr                            (ExprF(..), Expr)

newtype Subst = MkSubst { unSubst ∷ M.Map String Type }

(??) ∷ Subst → String → Maybe Type
(??) = flip M.lookup ∘ unSubst

instance Semigroup Subst where
  a@(MkSubst a') <> (MkSubst b) =
    MkSubst $ M.union (M.map (apply a) b) a'

instance Monoid Subst where
  mempty = MkSubst mempty

class Substitutable α where
  apply ∷ Subst → α → α
  ftv   ∷ α → S.Set String

instance Substitutable Type where
  apply s = \case
    TFun c d  → TFun (apply s c) (apply s d)
    TVar a    → fromMaybe (TVar a) (s ?? a)
  ftv = \case
    TVar v    → S.singleton v
    TFun c d  → S.union (ftv c) (ftv d)

data Scheme = Forall [String] Type

instance Substitutable Scheme where
  apply (MkSubst s) (Forall as t) =
    Forall as $ apply (MkSubst $ foldr M.delete s as) t
  ftv (Forall as t) = S.difference (ftv t) (S.fromList as)

type TC = ExceptT String (State Int)

runTC ∷ TC α → Either String α
runTC tc = evalState (runExceptT tc) 0

newTVar ∷ TC Type
newTVar =
    TVar ∘ (names ‼) <$> get <* modify succ
  where
    names = ["t" ⧺ show i | i <- [0..]]

bind ∷ String → Type → TC Subst
bind v t
  | t ≡ TVar v          = pure (∅)
  | S.member v (ftv t)  = throwError "Infinite type"
  | otherwise           = pure ∘ MkSubst $ M.singleton v t

unify ∷ Type → Type → TC Subst
unify (TFun c₀ d₀) (TFun c₁ d₁) = do
  s₀  ← unify c₀ c₁
  s₁  ← unify (apply s₀ d₀) (apply s₀ d₁)
  pure $ s₁ ⊕ s₀
unify (TVar v) t = bind v t
unify t (TVar v) = bind v t
-- unify t₀ t₁ = throwError $ mconcat [show t₀, " doesn't unify with ", show t₁] 

type Γ = M.Map String Scheme

instance Substitutable Γ where
  apply = M.map ∘ apply
  ftv = foldMap ftv ∘ M.elems

generalize ∷ Γ → Type → Scheme
generalize γ t =
  Forall (S.toList $ S.difference (ftv t) (ftv γ)) t

instantiate ∷ Scheme → TC Type
instantiate (Forall as t) = do
  tvs ← traverse (const newTVar) as
  pure $ apply (MkSubst ∘ M.fromList $ zip as tvs) t

infer' ∷ Γ → Expr α → TC (Expr (Subst, Type))
infer' γ (_ :< e) = case e of
  EVar v → case M.lookup v γ of
    Nothing → throwError $ "Unknown variable: " ⧺ v
    Just s  → (:< EVar v) ∘ ((∅),) <$> instantiate s
  EApp f e' → do
    t₀                  ← newTVar
    f'@((s₁, t₁) :< _)  ← infer' γ f
    e''@((s₂, t₂) :< _) ← infer' (apply s₁ γ) e'
    s₃                  ← unify (apply s₂ t₁) (TFun t₂ t₀)
    pure $ (s₃ ⊕ s₂ ⊕ s₁, apply s₃ t₀) :< EApp f' e''
  EAbs x e' → do
    t₀                  ← newTVar
    e''@((s₁, t₁) :< _) ← infer' (M.insert x (Forall 𝜀 t₀) γ) e'
    pure $ (s₁, TFun (apply s₁ t₀) t₁) :< EAbs x e''

infer ∷ Expr a → Either String (Expr Type)
infer e = uncurry apply <<$>> runTC (infer' (∅) e)