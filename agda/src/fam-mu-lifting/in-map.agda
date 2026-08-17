{-# OPTIONS --prop --postfix-projections --safe #-}

------------------------------------------------------------------------------
-- inMap, the canonical iso between the categorical one-step unfolding
-- fobj P (δ, μ P δ) and the concrete carrier, via the embed/unembed bridges;
-- packaged with the fold as the HasMu instance.
------------------------------------------------------------------------------

open import Level using (Level; _⊔_; lift) renaming (suc to lsuc)
open import Data.Nat using (suc)
import Data.Fin as Fin
open Fin using (Fin)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import Data.Unit using (tt)
open import prop using (_,_)
open import categories using (Category; HasTerminal; HasProducts; HasCoproducts; HasStrongCoproducts)
open import cmon-enriched using (CMonEnriched; Biproduct)
open import prop-setoid as PS using ()
open import indexed-family using (_⇒f_)
import fam-mu-lifting.fold

module fam-mu-lifting.in-map {o m e} (os es : Level) {𝒞 : Category o m e}
    (CM : CMonEnriched 𝒞) (BP : ∀ x y → Biproduct CM x y)
    (𝟙c : Category.obj 𝒞) where

open fam-mu-lifting.fold os es CM BP 𝟙c public

-- α's reconstruction machinery.
module InMapDef {n} (P : Poly (suc n)) (δ : Fin n → Obj) where
    δ' = extend δ (μ-fam P δ)
    module Tδ = Tree δ
    module TX = Tree δ'
    module R  = Reindex δ' δ

    -- Bridge `fobj`'s native structure to our `⟦_⟧shape` (identity at leaves and μ).
    embed-idx : (Q : Poly (suc n)) → fobj μ-fam Q δ' .idx .Carrier → TX.⟦ ∣ Q ∣ ⟧shape (λ v → inj₁ v)
    embed-idx (const A) a = a
    embed-idx (var v)   a = a
    embed-idx (Q₁ + Q₂) (inj₁ x) = inj₁ (embed-idx Q₁ x)
    embed-idx (Q₁ + Q₂) (inj₂ y) = inj₂ (embed-idx Q₂ y)
    embed-idx (Q₁ × Q₂) (x , y) = embed-idx Q₁ x , embed-idx Q₂ y
    embed-idx (μ Q')    t = t
    embed-idx-resp : (Q : Poly (suc n)) {x y : fobj μ-fam Q δ' .idx .Carrier} →
                     _≈s_ (fobj μ-fam Q δ' .idx) x y → TX.shape≈ ∣ Q ∣ (λ v → inj₁ v) (embed-idx Q x) (embed-idx Q y)
    embed-idx-resp (const A) p = p
    embed-idx-resp (var v)   p = p
    embed-idx-resp (Q₁ + Q₂) {inj₁ _} {inj₁ _} p = embed-idx-resp Q₁ p
    embed-idx-resp (Q₁ + Q₂) {inj₂ _} {inj₂ _} p = embed-idx-resp Q₂ p
    embed-idx-resp (Q₁ × Q₂) {_ , _} {_ , _} (p₁ , p₂) = embed-idx-resp Q₁ p₁ , embed-idx-resp Q₂ p₂
    embed-idx-resp (μ Q')    p = p
    -- Inverse bridge: `⟦_⟧shape` over the fresh context back to `fobj`'s native
    -- structure (identity at leaves and μ, like `embed-idx`).
    unembed-idx : (Q : Poly (suc n)) → TX.⟦ ∣ Q ∣ ⟧shape (λ v → inj₁ v) → fobj μ-fam Q δ' .idx .Carrier
    unembed-idx (const A) a = a
    unembed-idx (var v)   a = a
    unembed-idx (Q₁ + Q₂) (inj₁ x) = inj₁ (unembed-idx Q₁ x)
    unembed-idx (Q₁ + Q₂) (inj₂ y) = inj₂ (unembed-idx Q₂ y)
    unembed-idx (Q₁ × Q₂) (x , y) = unembed-idx Q₁ x , unembed-idx Q₂ y
    unembed-idx (μ Q')    t = t

    unembed-idx-resp : (Q : Poly (suc n)) {x y : TX.⟦ ∣ Q ∣ ⟧shape (λ v → inj₁ v)} →
                       TX.shape≈ ∣ Q ∣ (λ v → inj₁ v) x y →
                       _≈s_ (fobj μ-fam Q δ' .idx) (unembed-idx Q x) (unembed-idx Q y)
    unembed-idx-resp (const A) p = p
    unembed-idx-resp (var v)   p = p
    unembed-idx-resp (Q₁ + Q₂) {inj₁ _} {inj₁ _} p = unembed-idx-resp Q₁ p
    unembed-idx-resp (Q₁ + Q₂) {inj₂ _} {inj₂ _} p = unembed-idx-resp Q₂ p
    unembed-idx-resp (Q₁ × Q₂) {_ , _} {_ , _} (p₁ , p₂) = unembed-idx-resp Q₁ p₁ , unembed-idx-resp Q₂ p₂
    unembed-idx-resp (μ Q')    p = p

    -- Embedding after unembedding is the identity.
    embed-unembed : (Q : Poly (suc n)) (x : TX.⟦ ∣ Q ∣ ⟧shape (λ v → inj₁ v)) →
                    TX.shape≈ ∣ Q ∣ (λ v → inj₁ v) (embed-idx Q (unembed-idx Q x)) x
    embed-unembed (const A) a = A .idx .isEquivalence .refl
    embed-unembed (var v)   a = TX.elEq-refl (inj₁ v) a
    embed-unembed (Q₁ + Q₂) (inj₁ x) = embed-unembed Q₁ x
    embed-unembed (Q₁ + Q₂) (inj₂ y) = embed-unembed Q₂ y
    embed-unembed (Q₁ × Q₂) (x , y) = embed-unembed Q₁ x , embed-unembed Q₂ y
    embed-unembed (μ Q')    t = TX.W-≈-refl t

    m₀ : ∀ v → TX.El (inj₁ v) → Tδ.El (Srt.η₀ ∣ P ∣ v)
    m₀ Fin.zero    a = a
    m₀ (Fin.suc i) a = a
    m₀-resp : ∀ v {a a'} → TX.elEq (inj₁ v) a a' → Tδ.elEq (Srt.η₀ ∣ P ∣ v) (m₀ v a) (m₀ v a')
    m₀-resp Fin.zero    p = p
    m₀-resp (Fin.suc i) p = p
    m₀-fam : ∀ v (a : TX.El (inj₁ v)) →
             TX.fib-el (inj₁ v) (lift tt) a ⇒ Tδ.fib-el (Srt.η₀ ∣ P ∣ v) (Tδ.deco-ext P (λ i → lift tt) v) (m₀ v a)
    m₀-fam Fin.zero    a = id _
    m₀-fam (Fin.suc i) a = id _
    m₀-fam-natural : ∀ v {a a'} (p : TX.elEq (inj₁ v) a a') →
                 (m₀-fam v a' ∘ TX.fib-el-subst (inj₁ v) (lift tt) p)
                   ≈ (Tδ.fib-el-subst (Srt.η₀ ∣ P ∣ v) (Tδ.deco-ext P (λ i → lift tt) v) (m₀-resp v p) ∘ m₀-fam v a)
    m₀-fam-natural Fin.zero    p = ≈-trans id-left (≈-sym id-right)
    m₀-fam-natural (Fin.suc i) p = ≈-trans id-left (≈-sym id-right)
    mor₀ : R.MorD (λ v → inj₁ v) (Srt.η₀ ∣ P ∣) (λ v → lift tt) (Tδ.deco-ext P (λ i → lift tt))
    mor₀ = R.base m₀ m₀-resp m₀-fam m₀-fam-natural
    -- Fibre bridge: `fobj`'s fibre to our `fib-shape` (identity at leaves, products at ×).
    embed-fam : (Q : Poly (suc n)) (x : fobj μ-fam Q δ' .idx .Carrier) →
                fobj μ-fam Q δ' .fam .fm x ⇒ TX.fib-shape Q (λ v → lift tt) (embed-idx Q x)
    embed-fam (const A) a = id _
    embed-fam (var v)   a = id _
    embed-fam (Q₁ + Q₂) (inj₁ x) = Lmap (embed-fam Q₁ x)
    embed-fam (Q₁ + Q₂) (inj₂ y) = Lmap (embed-fam Q₂ y)
    embed-fam (Q₁ × Q₂) (x , y) = Lmap (prod-m (embed-fam Q₁ x) (embed-fam Q₂ y))
    embed-fam (μ Q')    t = id _
    embed-fam-natural : (Q : Poly (suc n)) {x y : fobj μ-fam Q δ' .idx .Carrier} (e : _≈s_ (fobj μ-fam Q δ' .idx) x y) →
                        (embed-fam Q y ∘ fobj μ-fam Q δ' .fam .subst e)
                          ≈ (TX.fib-shape-subst Q (λ v → lift tt) (embed-idx-resp Q e) ∘ embed-fam Q x)
    embed-fam-natural (const A) e = ≈-trans id-left (≈-sym id-right)
    embed-fam-natural (var v)   e = ≈-trans id-left (≈-sym id-right)
    embed-fam-natural (Q₁ + Q₂) {inj₁ _} {inj₁ _} e =
      ≈-trans (≈-sym (Lmap-comp _ _))
      (≈-trans (Lmap-cong (embed-fam-natural Q₁ e)) (Lmap-comp _ _))
    embed-fam-natural (Q₁ + Q₂) {inj₂ _} {inj₂ _} e =
      ≈-trans (≈-sym (Lmap-comp _ _))
      (≈-trans (Lmap-cong (embed-fam-natural Q₂ e)) (Lmap-comp _ _))
    embed-fam-natural (Q₁ × Q₂) {_ , _} {_ , _} (e₁ , e₂) =
      ≈-trans (≈-sym (Lmap-comp _ _))
      (≈-trans (Lmap-cong
                 (≈-trans (≈-sym (prod-m-comp _ _ _ _))
                  (≈-trans (prod-m-cong (embed-fam-natural Q₁ e₁) (embed-fam-natural Q₂ e₂))
                           (prod-m-comp _ _ _ _))))
               (Lmap-comp _ _))
    embed-fam-natural (μ Q')    e = ≈-trans id-left (≈-sym id-right)

    -- Fibre half of the inverse bridge.
    unembed-fam : (Q : Poly (suc n)) (y : TX.⟦ ∣ Q ∣ ⟧shape (λ v → inj₁ v)) →
                  TX.fib-shape Q (λ v → lift tt) y ⇒ fobj μ-fam Q δ' .fam .fm (unembed-idx Q y)
    unembed-fam (const A) a = id _
    unembed-fam (var v)   a = id _
    unembed-fam (Q₁ + Q₂) (inj₁ x) = Lmap (unembed-fam Q₁ x)
    unembed-fam (Q₁ + Q₂) (inj₂ y) = Lmap (unembed-fam Q₂ y)
    unembed-fam (Q₁ × Q₂) (x , y) = Lmap (prod-m (unembed-fam Q₁ x) (unembed-fam Q₂ y))
    unembed-fam (μ Q')    t = id _

    unembed-fam-natural : (Q : Poly (suc n)) {x y : TX.⟦ ∣ Q ∣ ⟧shape (λ v → inj₁ v)}
                          (e : TX.shape≈ ∣ Q ∣ (λ v → inj₁ v) x y) →
                          (unembed-fam Q y ∘ TX.fib-shape-subst Q (λ v → lift tt) e)
                            ≈ (fobj μ-fam Q δ' .fam .subst (unembed-idx-resp Q e) ∘ unembed-fam Q x)
    unembed-fam-natural (const A) e = ≈-trans id-left (≈-sym id-right)
    unembed-fam-natural (var v)   e = ≈-trans id-left (≈-sym id-right)
    unembed-fam-natural (Q₁ + Q₂) {inj₁ _} {inj₁ _} e =
      ≈-trans (≈-sym (Lmap-comp _ _))
      (≈-trans (Lmap-cong (unembed-fam-natural Q₁ e)) (Lmap-comp _ _))
    unembed-fam-natural (Q₁ + Q₂) {inj₂ _} {inj₂ _} e =
      ≈-trans (≈-sym (Lmap-comp _ _))
      (≈-trans (Lmap-cong (unembed-fam-natural Q₂ e)) (Lmap-comp _ _))
    unembed-fam-natural (Q₁ × Q₂) {_ , _} {_ , _} (e₁ , e₂) =
      ≈-trans (≈-sym (Lmap-comp _ _))
      (≈-trans (Lmap-cong
                 (≈-trans (≈-sym (prod-m-comp _ _ _ _))
                  (≈-trans (prod-m-cong (unembed-fam-natural Q₁ e₁) (unembed-fam-natural Q₂ e₂))
                           (prod-m-comp _ _ _ _))))
               (Lmap-comp _ _))
    unembed-fam-natural (μ Q')    e = ≈-trans id-left (≈-sym id-right)

    -- Embedding after unembedding is the identity on fibres too.
    embed-unembed-fam : (Q : Poly (suc n)) (y : TX.⟦ ∣ Q ∣ ⟧shape (λ v → inj₁ v)) →
                        (TX.fib-shape-subst Q (λ v → lift tt) (embed-unembed Q y)
                         ∘ (embed-fam Q (unembed-idx Q y) ∘ unembed-fam Q y))
                        ≈ id _
    embed-unembed-fam (const A) a =
      ≈-trans (∘-cong (A .fam .refl*) ≈-refl) (≈-trans id-left id-left)
    embed-unembed-fam (var v) a =
      ≈-trans (∘-cong (TX.fib-el-refl* (inj₁ v) (lift tt) a) ≈-refl) (≈-trans id-left id-left)
    embed-unembed-fam (Q₁ + Q₂) (inj₁ x) =
      ≈-trans (∘-cong ≈-refl (≈-sym (Lmap-comp _ _)))
      (≈-trans (≈-sym (Lmap-comp _ _))
        (≈-trans (Lmap-cong (embed-unembed-fam Q₁ x)) Lmap-id))
    embed-unembed-fam (Q₁ + Q₂) (inj₂ y) =
      ≈-trans (∘-cong ≈-refl (≈-sym (Lmap-comp _ _)))
      (≈-trans (≈-sym (Lmap-comp _ _))
        (≈-trans (Lmap-cong (embed-unembed-fam Q₂ y)) Lmap-id))
    embed-unembed-fam (Q₁ × Q₂) (x , y) =
      ≈-trans (∘-cong ≈-refl (≈-sym (Lmap-comp _ _)))
      (≈-trans (≈-sym (Lmap-comp _ _))
        (≈-trans (Lmap-cong
                   (≈-trans (∘-cong ≈-refl (≈-sym (prod-m-comp _ _ _ _)))
                     (≈-trans (≈-sym (prod-m-comp _ _ _ _))
                       (≈-trans (prod-m-cong (embed-unembed-fam Q₁ x) (embed-unembed-fam Q₂ y))
                                prod-m-id))))
                 Lmap-id))
    embed-unembed-fam (μ Q') t =
      ≈-trans (∘-cong (TX.fib-refl* Q' (λ v → lift tt) t) ≈-refl) (≈-trans id-left id-left)

    -- Unembedding after embedding is the identity, on indexes and on fibres.
    unembed-embed : (Q : Poly (suc n)) (x : fobj μ-fam Q δ' .idx .Carrier) →
                    _≈s_ (fobj μ-fam Q δ' .idx) (unembed-idx Q (embed-idx Q x)) x
    unembed-embed (const A) a = A .idx .isEquivalence .refl
    unembed-embed (var v)   a = TX.elEq-refl (inj₁ v) a
    unembed-embed (Q₁ + Q₂) (inj₁ x) = unembed-embed Q₁ x
    unembed-embed (Q₁ + Q₂) (inj₂ y) = unembed-embed Q₂ y
    unembed-embed (Q₁ × Q₂) (x , y) = unembed-embed Q₁ x , unembed-embed Q₂ y
    unembed-embed (μ Q')    t = TX.W-≈-refl t

    unembed-embed-fam : (Q : Poly (suc n)) (x : fobj μ-fam Q δ' .idx .Carrier) →
                        (fobj μ-fam Q δ' .fam .subst (unembed-embed Q x)
                         ∘ (unembed-fam Q (embed-idx Q x) ∘ embed-fam Q x))
                        ≈ id _
    unembed-embed-fam (const A) a =
      ≈-trans (∘-cong (A .fam .refl*) ≈-refl) (≈-trans id-left id-left)
    unembed-embed-fam (var v) a =
      ≈-trans (∘-cong (TX.fib-el-refl* (inj₁ v) (lift tt) a) ≈-refl) (≈-trans id-left id-left)
    unembed-embed-fam (Q₁ + Q₂) (inj₁ x) =
      ≈-trans (∘-cong ≈-refl (≈-sym (Lmap-comp _ _)))
      (≈-trans (≈-sym (Lmap-comp _ _))
        (≈-trans (Lmap-cong (unembed-embed-fam Q₁ x)) Lmap-id))
    unembed-embed-fam (Q₁ + Q₂) (inj₂ y) =
      ≈-trans (∘-cong ≈-refl (≈-sym (Lmap-comp _ _)))
      (≈-trans (≈-sym (Lmap-comp _ _))
        (≈-trans (Lmap-cong (unembed-embed-fam Q₂ y)) Lmap-id))
    unembed-embed-fam (Q₁ × Q₂) (x , y) =
      ≈-trans (∘-cong ≈-refl (≈-sym (Lmap-comp _ _)))
      (≈-trans (≈-sym (Lmap-comp _ _))
        (≈-trans (Lmap-cong
                   (≈-trans (∘-cong ≈-refl (≈-sym (prod-m-comp _ _ _ _)))
                     (≈-trans (≈-sym (prod-m-comp _ _ _ _))
                       (≈-trans (prod-m-cong (unembed-embed-fam Q₁ x) (unembed-embed-fam Q₂ y))
                                prod-m-id))))
                 Lmap-id))
    unembed-embed-fam (μ Q') t =
      ≈-trans (∘-cong (TX.fib-refl* Q' (λ v → lift tt) t) ≈-refl) (≈-trans id-left id-left)

    inMor : Mor (fobj μ-fam P δ') (μ-fam P δ)
    inMor .idxf .PS._⇒_.func i = Tδ.sup (R.reindex-shape ∣ P ∣ mor₀ (embed-idx P i))
    inMor .idxf .PS._⇒_.func-resp-≈ x≈y = R.reindex-shape-resp ∣ P ∣ mor₀ (embed-idx-resp P x≈y)
    inMor .famf ._⇒f_.transf x = R.reindex-fam P mor₀ ∘ embed-fam P x
    inMor .famf ._⇒f_.natural e =
      ≈-trans (assoc _ _ _)
      (≈-trans (∘-cong₂ (embed-fam-natural P e))
      (≈-trans (≈-sym (assoc _ _ _))
      (≈-trans (∘-cong₁ (R.reindex-fam-natural P mor₀ (embed-idx-resp P e)))
               (assoc _ _ _))))

-- FIXME: Should this file be called has-mu? I'm also not sure we need all these separate files.
hasMu : HasMu
hasMu .HasMu.μ-obj = μ-fam
hasMu .HasMu.inMap P δ = InMapDef.inMor P δ
hasMu .HasMu.⦅_⦆ alg = FoldDef.foldMor alg
