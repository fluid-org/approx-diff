{-# OPTIONS --prop --postfix-projections --safe #-}

module empty-diagram where

open import Level using (0ℓ)
open import prop-setoid using (IsEquivalence; module ≈-Reasoning)
open import categories using (Category; IsTerminal; HasTerminal)
open import functor using (Functor; NatTrans; NatIso; IsLimit; ≃-NatTrans; constFmor; HasLimitCones; Limit)

open IsEquivalence

data Obj : Set where

cat : Category 0ℓ 0ℓ 0ℓ
cat .Category.obj = Obj

module _ {o m e} (𝒞 : Category o m e) where

  private
    module 𝒞 = Category 𝒞

  initial-functor : Functor cat 𝒞
  initial-functor .Functor.fobj ()

  open Category.IsIso
  open NatTrans
  open NatIso
  open IsTerminal
  open IsLimit
  open ≃-NatTrans

  initial-functor-unique : ∀ {F G : Functor cat 𝒞} → NatIso F G
  initial-functor-unique .transform .transf ()
  initial-functor-unique .transf-iso ()

  IsLimit→IsTerminal : ∀ {F : Functor cat 𝒞} {t} {cone} → IsLimit F t cone → IsTerminal 𝒞 t
  IsLimit→IsTerminal is-limit .to-terminal = is-limit .lambda _ (initial-functor-unique .transform)
  IsLimit→IsTerminal {F} {t} {cone} is-limit .to-terminal-ext {x} f = begin
      is-limit .lambda x (initial-functor-unique .transform)
    ≈⟨ is-limit .lambda-cong (record { transf-eq = λ () }) ⟩
      is-limit .lambda x (cone functor.∘ constFmor f)
    ≈⟨ is-limit .lambda-ext f ⟩
      f
    ∎
    where open ≈-Reasoning 𝒞.isEquiv

  limit→terminal : ∀ (F : Functor cat 𝒞) → Limit F → HasTerminal 𝒞
  limit→terminal F limit .HasTerminal.witness = limit .Limit.apex
  limit→terminal F limit .HasTerminal.is-terminal = IsLimit→IsTerminal (limit .Limit.isLimit)

  limits→terminal : HasLimitCones cat 𝒞 → HasTerminal 𝒞
  limits→terminal limits = limit→terminal initial-functor (limits initial-functor)

  terminal→limit : ∀ {t} → IsTerminal 𝒞 t → IsLimit initial-functor t (initial-functor-unique .transform)
  terminal→limit is-terminal .lambda x _ = is-terminal .to-terminal
  terminal→limit is-terminal .lambda-cong α≈β = 𝒞.≈-refl
  terminal→limit is-terminal .lambda-eval α .transf-eq ()
  terminal→limit is-terminal .lambda-ext = is-terminal .to-terminal-ext
