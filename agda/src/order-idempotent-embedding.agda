{-# OPTIONS --prop --postfix-projections --safe #-}

open import Level using (0ℓ)
open import prop-setoid using (Setoid; module ≈-Reasoning)
open import commutative-semiring using (CommutativeSemiring)
open import categories using (Category; Splitting; HasTerminal; IsTerminal)
open import cmon-enriched using (CMonEnriched; Biproduct; biproducts→products; biproduct-iso)
open import commutative-monoid using (CommutativeMonoid)
open import functor using (Functor)
open import finite-product-functor using (preserve-chosen-terminal; preserve-chosen-products)
import matrix
import order-idempotent

-- Realise the order-idempotent category over a realisation 𝓖 of Mat(S): each order matrix becomes
-- an idempotent endomorphism of the realised object, and a chosen splitting of that idempotent
-- interprets the position order. Morphisms route through the splittings, so the functor laws are
-- absorption. Mirrors matrix-embedding, which realises Mat(S) itself.
module order-idempotent-embedding
  {A : Setoid 0ℓ 0ℓ} (S : CommutativeSemiring A)
  (let open CommutativeSemiring S hiding (_≈_; trans; sym; refl); open Setoid A)
  (∨-idem    : ∀ {x} → x + x ≈ x)
  (∧-idem    : ∀ {x} → x · x ≈ x)
  (⊤-add-top : ∀ {x} → ι + x ≈ ι)
  where

module OI = order-idempotent S ∨-idem ∧-idem ⊤-add-top
module MatS = matrix.Mat S

open OI using (Pos; dim; ord; mat; absorbed; absorb-left)
open Functor
open Splitting

module Embed
  {o m e} {𝒞 : Category o m e}
  (𝓖 : Functor MatS.cat 𝒞)
  (split : ∀ (P : Pos) → Splitting 𝒞 (𝓖 .fmor (P .ord)))
  where

  open Category 𝒞

  private module 𝒞 = Category 𝒞

  𝓚 : Functor OI.cat 𝒞
  𝓚 .fobj P = split P .witness
  𝓚 .fmor {P} {Q} f = split Q .retr ∘ (𝓖 .fmor (f .mat) ∘ split P .sect)
  𝓚 .fmor-cong f₁≈f₂ = ∘-cong ≈-refl (∘-cong (𝓖 .fmor-cong f₁≈f₂) ≈-refl)
  𝓚 .fmor-id {P} =
    begin
      split P .retr ∘ (𝓖 .fmor (P .ord) ∘ split P .sect)
    ≈˘⟨ ∘-cong ≈-refl (∘-cong (split P .sect-retr) ≈-refl) ⟩
      split P .retr ∘ ((split P .sect ∘ split P .retr) ∘ split P .sect)
    ≈⟨ ∘-cong ≈-refl (assoc _ _ _) ⟩
      split P .retr ∘ (split P .sect ∘ (split P .retr ∘ split P .sect))
    ≈⟨ ∘-cong ≈-refl (∘-cong ≈-refl (split P .retr-sect)) ⟩
      split P .retr ∘ (split P .sect ∘ id _)
    ≈⟨ ∘-cong ≈-refl id-right ⟩
      split P .retr ∘ split P .sect
    ≈⟨ split P .retr-sect ⟩
      id _
    ∎ where open ≈-Reasoning isEquiv
  𝓚 .fmor-comp {P} {Q} {R} g f =
    begin
      split R .retr ∘ (𝓖 .fmor (g .mat MatS.∘ f .mat) ∘ split P .sect)
    ≈˘⟨ ∘-cong ≈-refl (∘-cong (𝓖 .fmor-cong (MatS.∘-cong (OI.≈ₘ-refl {M = g .mat}) (absorb-left f))) ≈-refl) ⟩
      split R .retr ∘ (𝓖 .fmor (g .mat MatS.∘ (Q .ord MatS.∘ f .mat)) ∘ split P .sect)
    ≈⟨ ∘-cong ≈-refl (∘-cong (𝓖 .fmor-comp (g .mat) (Q .ord MatS.∘ f .mat)) ≈-refl) ⟩
      split R .retr ∘ ((𝓖 .fmor (g .mat) ∘ 𝓖 .fmor (Q .ord MatS.∘ f .mat)) ∘ split P .sect)
    ≈⟨ ∘-cong ≈-refl (∘-cong (∘-cong ≈-refl (𝓖 .fmor-comp (Q .ord) (f .mat))) ≈-refl) ⟩
      split R .retr ∘ ((𝓖 .fmor (g .mat) ∘ (𝓖 .fmor (Q .ord) ∘ 𝓖 .fmor (f .mat))) ∘ split P .sect)
    ≈˘⟨ ∘-cong ≈-refl (∘-cong (∘-cong ≈-refl (∘-cong (split Q .sect-retr) ≈-refl)) ≈-refl) ⟩
      split R .retr ∘ ((𝓖 .fmor (g .mat) ∘ ((split Q .sect ∘ split Q .retr) ∘ 𝓖 .fmor (f .mat))) ∘ split P .sect)
    ≈⟨ ∘-cong ≈-refl (∘-cong (∘-cong ≈-refl (assoc _ _ _)) ≈-refl) ⟩
      split R .retr ∘ ((𝓖 .fmor (g .mat) ∘ (split Q .sect ∘ (split Q .retr ∘ 𝓖 .fmor (f .mat)))) ∘ split P .sect)
    ≈˘⟨ ∘-cong ≈-refl (∘-cong (assoc _ _ _) ≈-refl) ⟩
      split R .retr ∘ (((𝓖 .fmor (g .mat) ∘ split Q .sect) ∘ (split Q .retr ∘ 𝓖 .fmor (f .mat))) ∘ split P .sect)
    ≈⟨ ∘-cong ≈-refl (assoc _ _ _) ⟩
      split R .retr ∘ ((𝓖 .fmor (g .mat) ∘ split Q .sect) ∘ ((split Q .retr ∘ 𝓖 .fmor (f .mat)) ∘ split P .sect))
    ≈˘⟨ assoc _ _ _ ⟩
      (split R .retr ∘ (𝓖 .fmor (g .mat) ∘ split Q .sect)) ∘ ((split Q .retr ∘ 𝓖 .fmor (f .mat)) ∘ split P .sect)
    ≈⟨ ∘-cong ≈-refl (assoc _ _ _) ⟩
      (split R .retr ∘ (𝓖 .fmor (g .mat) ∘ split Q .sect)) ∘ (split Q .retr ∘ (𝓖 .fmor (f .mat) ∘ split P .sect))
    ∎ where open ≈-Reasoning isEquiv

  -- Sandwiching between the section and retraction recovers the realised matrix, by absorption.
  sandwich : ∀ {P Q} (f : OI._⇒_ P Q) →
             (split Q .sect ∘ (𝓚 .fmor f ∘ split P .retr)) 𝒞.≈ 𝓖 .fmor (f .mat)
  sandwich {P} {Q} f =
    begin
      split Q .sect ∘ (𝓚 .fmor f ∘ split P .retr)
    ≈˘⟨ assoc _ _ _ ⟩
      (split Q .sect ∘ 𝓚 .fmor f) ∘ split P .retr
    ≈˘⟨ ∘-cong (assoc _ _ _) ≈-refl ⟩
      ((split Q .sect ∘ split Q .retr) ∘ (𝓖 .fmor (f .mat) ∘ split P .sect)) ∘ split P .retr
    ≈⟨ ∘-cong (∘-cong (split Q .sect-retr) ≈-refl) ≈-refl ⟩
      (𝓖 .fmor (Q .ord) ∘ (𝓖 .fmor (f .mat) ∘ split P .sect)) ∘ split P .retr
    ≈˘⟨ ∘-cong (assoc _ _ _) ≈-refl ⟩
      ((𝓖 .fmor (Q .ord) ∘ 𝓖 .fmor (f .mat)) ∘ split P .sect) ∘ split P .retr
    ≈⟨ assoc _ _ _ ⟩
      (𝓖 .fmor (Q .ord) ∘ 𝓖 .fmor (f .mat)) ∘ (split P .sect ∘ split P .retr)
    ≈⟨ ∘-cong ≈-refl (split P .sect-retr) ⟩
      (𝓖 .fmor (Q .ord) ∘ 𝓖 .fmor (f .mat)) ∘ 𝓖 .fmor (P .ord)
    ≈˘⟨ ∘-cong (𝓖 .fmor-comp (Q .ord) (f .mat)) ≈-refl ⟩
      𝓖 .fmor (Q .ord MatS.∘ f .mat) ∘ 𝓖 .fmor (P .ord)
    ≈˘⟨ 𝓖 .fmor-comp (Q .ord MatS.∘ f .mat) (P .ord) ⟩
      𝓖 .fmor ((Q .ord MatS.∘ f .mat) MatS.∘ P .ord)
    ≈⟨ 𝓖 .fmor-cong (f .absorbed) ⟩
      𝓖 .fmor (f .mat)
    ∎ where open ≈-Reasoning isEquiv

  -- 𝓚 inherits faithfulness from 𝓖.
  module Faithful
    (𝓖-faithful : ∀ {m n} {M N : MatS.Matrix n m} →
                  𝓖 .fmor M 𝒞.≈ 𝓖 .fmor N → M MatS.≈ₘ N)
    where

    𝓚-faithful : ∀ {P Q} {f g : OI._⇒_ P Q} → 𝓚 .fmor f 𝒞.≈ 𝓚 .fmor g → OI._≈p_ f g
    𝓚-faithful {P} {Q} {f} {g} h =
      𝓖-faithful (≈-trans (≈-sym (sandwich f))
                 (≈-trans (∘-cong ≈-refl (∘-cong h ≈-refl)) (sandwich g)))

  -- With 𝒞 CMon-enriched and 𝓖 additive, the images of the block-order biproduct assemble a
  -- biproduct on the split objects, and a terminal realisation of dimension zero splits to a
  -- terminal object; 𝓚 then preserves the chosen terminal and products.
  module Preserve
    (CM : CMonEnriched 𝒞)
    (let open CMonEnriched CM)
    (BP : ∀ x y → Biproduct CM x y)
    (𝓖-εₘ : ∀ {m n} → 𝓖 .fmor (MatS.εₘ {m} {n}) 𝒞.≈ εm)
    (𝓖-+ₘ : ∀ {m n} (M N : MatS.Matrix m n) →
            𝓖 .fmor (M MatS.+ₘ N) 𝒞.≈ (𝓖 .fmor M +m 𝓖 .fmor N))
    (T : HasTerminal 𝒞)
    (𝓖-𝟘-terminal : IsTerminal 𝒞 (𝓖 .fobj 0))
    where

    open Category.IsIso

    𝓚-εp : ∀ {P Q} → 𝓚 .fmor (OI.εp {P} {Q}) 𝒞.≈ εm
    𝓚-εp {P} {Q} =
      begin
        split Q .retr ∘ (𝓖 .fmor (MatS.εₘ {Q .dim} {P .dim}) ∘ split P .sect)
      ≈⟨ ∘-cong ≈-refl (∘-cong (𝓖-εₘ {Q .dim} {P .dim}) ≈-refl) ⟩
        split Q .retr ∘ (εm ∘ split P .sect)
      ≈⟨ ∘-cong ≈-refl (comp-bilinear-ε₁ (split P .sect)) ⟩
        split Q .retr ∘ εm
      ≈⟨ comp-bilinear-ε₂ (split Q .retr) ⟩
        εm
      ∎ where open ≈-Reasoning isEquiv

    𝓚-+p : ∀ {P Q} (f g : OI._⇒_ P Q) → 𝓚 .fmor (OI._+p_ f g) 𝒞.≈ (𝓚 .fmor f +m 𝓚 .fmor g)
    𝓚-+p {P} {Q} f g =
      begin
        split Q .retr ∘ (𝓖 .fmor (f .mat MatS.+ₘ g .mat) ∘ split P .sect)
      ≈⟨ ∘-cong ≈-refl (∘-cong (𝓖-+ₘ (f .mat) (g .mat)) ≈-refl) ⟩
        split Q .retr ∘ ((𝓖 .fmor (f .mat) +m 𝓖 .fmor (g .mat)) ∘ split P .sect)
      ≈⟨ ∘-cong ≈-refl (comp-bilinear₁ _ _ _) ⟩
        split Q .retr ∘ ((𝓖 .fmor (f .mat) ∘ split P .sect) +m (𝓖 .fmor (g .mat) ∘ split P .sect))
      ≈⟨ comp-bilinear₂ _ _ _ ⟩
        (split Q .retr ∘ (𝓖 .fmor (f .mat) ∘ split P .sect)) +m (split Q .retr ∘ (𝓖 .fmor (g .mat) ∘ split P .sect))
      ∎ where open ≈-Reasoning isEquiv

    -- The five biproduct laws are the 𝓚-images of the laws in the order-idempotent category.
    biproduct𝓚 : ∀ P Q → Biproduct CM (𝓚 .fobj P) (𝓚 .fobj Q)
    biproduct𝓚 P Q .Biproduct.prod = 𝓚 .fobj (OI._⊕_ P Q)
    biproduct𝓚 P Q .Biproduct.p₁ = 𝓚 .fmor (OI.π₁ P Q)
    biproduct𝓚 P Q .Biproduct.p₂ = 𝓚 .fmor (OI.π₂ P Q)
    biproduct𝓚 P Q .Biproduct.in₁ = 𝓚 .fmor (OI.ι₁ P Q)
    biproduct𝓚 P Q .Biproduct.in₂ = 𝓚 .fmor (OI.ι₂ P Q)
    biproduct𝓚 P Q .Biproduct.id-1 =
      ≈-trans (≈-sym (𝓚 .fmor-comp (OI.π₁ P Q) (OI.ι₁ P Q)))
      (≈-trans (𝓚 .fmor-cong {f₁ = OI._∘_ (OI.π₁ P Q) (OI.ι₁ P Q)} {f₂ = OI.id P} (OI.biproduct P Q .Biproduct.id-1)) (𝓚 .fmor-id {P}))
    biproduct𝓚 P Q .Biproduct.id-2 =
      ≈-trans (≈-sym (𝓚 .fmor-comp (OI.π₂ P Q) (OI.ι₂ P Q)))
      (≈-trans (𝓚 .fmor-cong {f₁ = OI._∘_ (OI.π₂ P Q) (OI.ι₂ P Q)} {f₂ = OI.id Q} (OI.biproduct P Q .Biproduct.id-2)) (𝓚 .fmor-id {Q}))
    biproduct𝓚 P Q .Biproduct.zero-1 =
      ≈-trans (≈-sym (𝓚 .fmor-comp (OI.π₁ P Q) (OI.ι₂ P Q)))
      (≈-trans (𝓚 .fmor-cong {f₁ = OI._∘_ (OI.π₁ P Q) (OI.ι₂ P Q)} {f₂ = OI.εp {Q} {P}} (OI.biproduct P Q .Biproduct.zero-1)) (𝓚-εp {Q} {P}))
    biproduct𝓚 P Q .Biproduct.zero-2 =
      ≈-trans (≈-sym (𝓚 .fmor-comp (OI.π₂ P Q) (OI.ι₁ P Q)))
      (≈-trans (𝓚 .fmor-cong {f₁ = OI._∘_ (OI.π₂ P Q) (OI.ι₁ P Q)} {f₂ = OI.εp {P} {Q}} (OI.biproduct P Q .Biproduct.zero-2)) (𝓚-εp {P} {Q}))
    biproduct𝓚 P Q .Biproduct.id-+ =
      ≈-trans (CommutativeMonoid.+-cong (homCM _ _)
                 (≈-sym (𝓚 .fmor-comp (OI.ι₁ P Q) (OI.π₁ P Q)))
                 (≈-sym (𝓚 .fmor-comp (OI.ι₂ P Q) (OI.π₂ P Q))))
      (≈-trans (≈-sym (𝓚-+p (OI._∘_ (OI.ι₁ P Q) (OI.π₁ P Q)) (OI._∘_ (OI.ι₂ P Q) (OI.π₂ P Q))))
      (≈-trans (𝓚 .fmor-cong {f₁ = OI._+p_ (OI._∘_ (OI.ι₁ P Q) (OI.π₁ P Q)) (OI._∘_ (OI.ι₂ P Q) (OI.π₂ P Q))} {f₂ = OI.id (OI._⊕_ P Q)} (OI.biproduct P Q .Biproduct.id-+)) (𝓚 .fmor-id {OI._⊕_ P Q})))

    -- A retract of a terminal object is terminal.
    𝓚𝟘-terminal : IsTerminal 𝒞 (𝓚 .fobj OI.𝟘p)
    𝓚𝟘-terminal .IsTerminal.to-terminal =
      split OI.𝟘p .retr ∘ IsTerminal.to-terminal 𝓖-𝟘-terminal
    𝓚𝟘-terminal .IsTerminal.to-terminal-ext f =
      begin
        split OI.𝟘p .retr ∘ IsTerminal.to-terminal 𝓖-𝟘-terminal
      ≈⟨ ∘-cong ≈-refl (IsTerminal.to-terminal-ext 𝓖-𝟘-terminal (split OI.𝟘p .sect ∘ f)) ⟩
        split OI.𝟘p .retr ∘ (split OI.𝟘p .sect ∘ f)
      ≈˘⟨ assoc _ _ _ ⟩
        (split OI.𝟘p .retr ∘ split OI.𝟘p .sect) ∘ f
      ≈⟨ ∘-cong (split OI.𝟘p .retr-sect) ≈-refl ⟩
        id _ ∘ f
      ≈⟨ id-left ⟩
        f
      ∎ where open ≈-Reasoning isEquiv

    𝓚-preserve-terminal : preserve-chosen-terminal 𝓚 OI.terminal T
    𝓚-preserve-terminal .inverse = IsTerminal.to-terminal 𝓚𝟘-terminal
    𝓚-preserve-terminal .f∘inverse≈id = HasTerminal.to-terminal-unique T _ _
    𝓚-preserve-terminal .inverse∘f≈id = IsTerminal.to-terminal-unique 𝓚𝟘-terminal _ _

    𝓚-preserve-products :
      preserve-chosen-products 𝓚 (biproducts→products OI.cmon OI.biproduct) (biproducts→products CM BP)
    𝓚-preserve-products {P} {Q} = biproduct-iso CM (biproduct𝓚 P Q) (BP (𝓚 .fobj P) (𝓚 .fobj Q))
