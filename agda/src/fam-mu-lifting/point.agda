{-# OPTIONS --prop --postfix-projections --safe #-}

------------------------------------------------------------------------------
-- Chosen constants of the rooted μ-carriers: given constants at the const
-- leaves of the polynomial and at the environment, every tree fibre has a
-- constant, by the same recursion that computes the fibre. Each root
-- contributes itself together with the payload's constant beneath it, so at
-- the top the constant selects the whole fibre when the leaf constants do.
-- Naturality along bisimilarity carries the payload transports under the
-- lifting's action, which is natural at transports because they are
-- isomorphisms.
------------------------------------------------------------------------------

open import Level using (Level; _⊔_; Lift; lift)
open import Data.Nat using (suc)
import Data.Fin as Fin
open Fin using (Fin)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import Data.Unit using (⊤; tt)
open import prop using (_,_)
open import categories using (Category; HasTerminal)
open import cmon-enriched using (CMonEnriched; Biproduct)
open import commutative-monoid using (CommutativeMonoid)
open import lifting using (Lifting)
import fam-mu-lifting.carrier

module fam-mu-lifting.point {o m e} (os es : Level) {𝒞 : Category o m e}
    (T : HasTerminal 𝒞) (CM : CMonEnriched 𝒞) (BP : ∀ x y → Biproduct CM x y)
    {𝟙c : Category.obj 𝒞} (Lft : Lifting CM 𝟙c) where

open fam-mu-lifting.carrier os es T CM BP Lft

private
  module CME = CMonEnriched CM

+m-cong : ∀ {x y} {f f' g g' : x ⇒ y} → f ≈ f' → g ≈ g' → (f CME.+m g) ≈ (f' CME.+m g')
+m-cong = CME.homCM _ _ .CommutativeMonoid.+-cong

-- A constant assignment for a polynomial: a chosen constant at each const leaf.
PolyPt : ∀ {j} → Poly j → Set (o ⊔ m ⊔ e ⊔ os ⊔ es)
PolyPt (const A) = Pointed A
PolyPt (var i)   = Lift _ ⊤
PolyPt (P + Q)   = PolyPt P ×T PolyPt Q
PolyPt (P × Q)   = PolyPt P ×T PolyPt Q
PolyPt (μ Q)     = PolyPt Q

module Point {n} (δ : Fin n → Obj) (δ-pt : ∀ i → Pointed (δ i)) where
  open Tree δ

  -- Constant assignments for decorations, mirroring the decoration structure.
  DecoPt : ∀ {s} → Deco s → Set (o ⊔ m ⊔ e ⊔ os ⊔ es)
  DecoAssignPt : ∀ (r : Fin n ⊎ Sort n) → DecoAssign r → Set (o ⊔ m ⊔ e ⊔ os ⊔ es)

  DecoAssignPt (inj₁ p) _  = Lift _ ⊤
  DecoAssignPt (inj₂ s) dd = DecoPt dd

  DecoPt (mkDeco Q d) = PolyPt Q ×T (∀ i → DecoAssignPt _ (d i))

  deco-ext-pt : ∀ {k} (Q : Poly (suc k)) {ρ̄ : Fin k → Fin n ⊎ Sort n}
                {d : ∀ i → DecoAssign (ρ̄ i)}
                (pQ : PolyPt Q) (pd : ∀ i → DecoAssignPt (ρ̄ i) (d i)) →
                ∀ i → DecoAssignPt (extend ρ̄ (inj₂ (mkSort ∣ Q ∣ ρ̄)) i) (deco-ext Q d i)
  deco-ext-pt Q pQ pd Fin.zero    = pQ , pd
  deco-ext-pt Q pQ pd (Fin.suc i) = pd i

  -- The constant of each tree fibre, by the fibre's own recursion.
  mutual
    pt-fib : ∀ {k} (Q : Poly (suc k)) {ρ̄ : Fin k → Fin n ⊎ Sort n}
             (d : ∀ i → DecoAssign (ρ̄ i))
             (pQ : PolyPt Q) (pd : ∀ i → DecoAssignPt (ρ̄ i) (d i))
             (t : W ∣ Q ∣ ρ̄) → 𝟙c ⇒ fib Q d t
    pt-fib Q d pQ pd (sup x) = pt-shape Q (deco-ext Q d) pQ (deco-ext-pt Q pQ pd) x

    pt-shape : ∀ {j} (Q : Poly j) {η̄ : Fin j → Fin n ⊎ Sort n}
               (d : ∀ i → DecoAssign (η̄ i))
               (pQ : PolyPt Q) (pd : ∀ i → DecoAssignPt (η̄ i) (d i))
               (x : ⟦ ∣ Q ∣ ⟧shape η̄) → 𝟙c ⇒ fib-shape Q d x
    pt-shape (const A) d pA pd x = pA .pt x
    pt-shape (var i)   d _  pd x = pt-el _ (d i) (pd i) x
    pt-shape (P + Q) d (pP , pQ) pd (inj₁ x) = root CME.+m (inj ∘ pt-shape P d pP pd x)
    pt-shape (P + Q) d (pP , pQ) pd (inj₂ y) = root CME.+m (inj ∘ pt-shape Q d pQ pd y)
    pt-shape (P × Q) d (pP , pQ) pd (x , y) =
      root CME.+m (inj ∘ pair (pt-shape P d pP pd x) (pt-shape Q d pQ pd y))
    pt-shape (μ Q') d pQ' pd t = pt-fib Q' d pQ' pd t

    pt-el : (r : Fin n ⊎ Sort n) (dr : DecoAssign r) (pr : DecoAssignPt r dr)
            (x : El r) → 𝟙c ⇒ fib-el r dr x
    pt-el (inj₁ p) _ _ x = δ-pt p .pt x
    pt-el (inj₂ s) (mkDeco Q ρd) (pQ , pρ) x = pt-fib Q ρd pQ pρ x

  -- The constants are natural along bisimilarity.
  mutual
    pt-fib-natural : ∀ {k} (Q : Poly (suc k)) {ρ̄ : Fin k → Fin n ⊎ Sort n}
                     (d : ∀ i → DecoAssign (ρ̄ i))
                     (pQ : PolyPt Q) (pd : ∀ i → DecoAssignPt (ρ̄ i) (d i))
                     {t₁ t₂ : W ∣ Q ∣ ρ̄} (p : W-≈ t₁ t₂) →
                     (fib-subst Q d {x = t₁} {y = t₂} p ∘ pt-fib Q d pQ pd t₁) ≈ pt-fib Q d pQ pd t₂
    pt-fib-natural Q d pQ pd {sup x} {sup y} p =
      pt-shape-natural Q (deco-ext Q d) pQ (deco-ext-pt Q pQ pd) p

    pt-shape-natural : ∀ {j} (Q : Poly j) {η̄ : Fin j → Fin n ⊎ Sort n}
                       (d : ∀ i → DecoAssign (η̄ i))
                       (pQ : PolyPt Q) (pd : ∀ i → DecoAssignPt (η̄ i) (d i))
                       {x y : ⟦ ∣ Q ∣ ⟧shape η̄} (p : shape≈ ∣ Q ∣ η̄ x y) →
                       (fib-shape-subst Q d p ∘ pt-shape Q d pQ pd x) ≈ pt-shape Q d pQ pd y
    pt-shape-natural (const A) d pA pd p = pA .pt-natural p
    pt-shape-natural (var i)   d _  pd p = pt-el-natural _ (d i) (pd i) p
    pt-shape-natural (P + Q) d (pP , pQ) pd {inj₁ _} {inj₁ _} p =
      ≈-trans (CME.comp-bilinear₂ _ _ _)
        (+m-cong (Lmap-root _)
          (≈-trans (≈-sym (assoc _ _ _))
            (≈-trans (∘-cong₁ (Lmap-inj (fib-shape-iso₁ P d p) (fib-shape-iso₂ P d p)))
              (≈-trans (assoc _ _ _) (∘-cong₂ (pt-shape-natural P d pP pd p))))))
    pt-shape-natural (P + Q) d (pP , pQ) pd {inj₂ _} {inj₂ _} p =
      ≈-trans (CME.comp-bilinear₂ _ _ _)
        (+m-cong (Lmap-root _)
          (≈-trans (≈-sym (assoc _ _ _))
            (≈-trans (∘-cong₁ (Lmap-inj (fib-shape-iso₁ Q d p) (fib-shape-iso₂ Q d p)))
              (≈-trans (assoc _ _ _) (∘-cong₂ (pt-shape-natural Q d pQ pd p))))))
    pt-shape-natural (P × Q) d (pP , pQ) pd {_ , _} {_ , _} (p₁ , p₂) =
      ≈-trans (CME.comp-bilinear₂ _ _ _)
        (+m-cong (Lmap-root _)
          (≈-trans (≈-sym (assoc _ _ _))
            (≈-trans (∘-cong₁ (Lmap-inj
                       (pm-iso (fib-shape-iso₁ P d p₁) (fib-shape-iso₁ Q d p₂))
                       (pm-iso (fib-shape-iso₂ P d p₁) (fib-shape-iso₂ Q d p₂))))
              (≈-trans (assoc _ _ _)
                (∘-cong₂ (≈-trans (pair-natural _ _ _)
                  (pair-cong
                    (≈-trans (assoc _ _ _)
                      (≈-trans (∘-cong₂ (pair-p₁ _ _)) (pt-shape-natural P d pP pd p₁)))
                    (≈-trans (assoc _ _ _)
                      (≈-trans (∘-cong₂ (pair-p₂ _ _)) (pt-shape-natural Q d pQ pd p₂))))))))))
    pt-shape-natural (μ Q') d pQ' pd {x} {y} p = pt-fib-natural Q' d pQ' pd {x} {y} p

    pt-el-natural : (r : Fin n ⊎ Sort n) (dr : DecoAssign r) (pr : DecoAssignPt r dr)
                    {x y : El r} (e : elEq r x y) →
                    (fib-el-subst r dr e ∘ pt-el r dr pr x) ≈ pt-el r dr pr y
    pt-el-natural (inj₁ p) _ _ e = δ-pt p .pt-natural e
    pt-el-natural (inj₂ s) (mkDeco Q ρd) (pQ , pρ) {x} {y} e =
      pt-fib-natural Q ρd pQ pρ {x} {y} e

-- The μ-carrier's chosen constant, at the canonical decoration.
μObj-pointed : ∀ {k} {δ : Fin k → Obj} (P : Poly (suc k)) →
               (∀ i → Pointed (δ i)) → PolyPt P → Pointed (μObj P δ)
μObj-pointed {k} {δ} P δ-pt pP .pt t =
  Point.pt-fib δ δ-pt P (λ i → lift tt) pP (λ i → lift tt) t
μObj-pointed {k} {δ} P δ-pt pP .pt-natural {t₁} {t₂} p =
  Point.pt-fib-natural δ δ-pt P (λ i → lift tt) pP (λ i → lift tt) {t₁} {t₂} p
