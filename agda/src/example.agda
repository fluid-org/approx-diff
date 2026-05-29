{-# OPTIONS --prop --postfix-projections --safe #-}

module example where

open import Level using (0ℓ; lift)
open import Data.List using (List; []; _∷_)
open import every using (Every; []; _∷_)
open import signature
import language-syntax
import label

open import example-signature

module L = language-syntax Sig

-- example query. Given `List (label [×] nat)`, add up all the
-- elements labelled with a specific label:
--
--   sum [ snd e | e <- xs, equal-label 'a' (fst e) ]
--
--   sum (concatMap x (e. if equal-label 'a' (fst e) then return (snd e) else nil))
--
--   sum = fold zero (add (var zero) (var (succ zero)))

module ex where
  open L
  open SynMonad

  -- Writer monad over the approximation sort: pairs values with an
  -- approximation tag. Tag-bind multiplies the two tags via approx-mult.
  Tag : type → type
  Tag τ = base approx [×] τ

  Tag-pure : ∀ {Γ τ} → Γ ⊢ τ [→] Tag τ
  Tag-pure = lam (pair (bop approx-unit []) (var zero))

  Tag-bind : ∀ {Γ σ τ} → Γ ⊢ Tag σ [→] (σ [→] Tag τ) [→] Tag τ
  Tag-bind =
    lam (lam (pair (bop approx-mult (fst (var (succ zero)) ∷ fst (app (var zero) (snd (var (succ zero)))) ∷ []))
                   (snd (app (var zero) (snd (var (succ zero)))))))

  Tag-monad : SynMonad
  Tag-monad .Mon = Tag
  Tag-monad .pure = Tag-pure
  Tag-monad .bind = Tag-bind

  `_ : ∀ {Γ} → label.label → Γ ⊢ base label
  ` l = bop (lbl l) []

  _≟_ : ∀ {Γ} → Γ ⊢ base label → Γ ⊢ base label → Γ ⊢ bool
  M ≟ N = brel equal-label (M ∷ N ∷ [])

  -- Summation function, μ-types version (uses list).
  sum : ∀ {Γ} → Γ ⊢ list (base number) [→] base number
  sum = lam (fold (bop zero []) (bop add (var zero ∷ var (succ zero) ∷ [])) (var zero))

  -- Whether some element of the list equals the given label. CBV semantics evaluates the predicate at every
  -- element, but backward demand "short- circuits": at the first matching element, the remaining list becomes
  -- ⊥-demanded. (Currently unused though.)
  some-eq : ∀ {Γ} → Γ ⊢ base label [→] list (base label) [→] bool
  some-eq = lam (lam
    (fold false
      (if (brel equal-label (var (succ zero) ∷ var (succ (succ (succ zero))) ∷ []))
       then true else (var zero))
      (var zero)))

  query : label.label → emp , list (base label [×] base number) ⊢ base number
  query l =
    app sum
      (from var zero collect
      when fst (var zero) ≟ (` l) ；
      return (snd (var zero)))
