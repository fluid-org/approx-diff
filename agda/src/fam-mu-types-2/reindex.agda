{-# OPTIONS --prop --postfix-projections --safe #-}

------------------------------------------------------------------------------
-- Reindexing of carrier trees along context morphisms: MorD carries index and
-- fibre data, IMorD the index action only (MorD's index side factors through it
-- via `erase`), and FReindex's FAct pairs an IMorD with an "external" Γ-dependent
-- fibre action. The morphisms are first-order data so the recursion stays
-- structural. The index actions work on the category-free shapes; the fibre
-- actions carry the decorations of both sides.
------------------------------------------------------------------------------

open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Data.Nat using (ℕ; suc)
import Data.Fin as Fin
open Fin using (Fin)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import prop using (_,_)
open import categories using (Category; HasTerminal; HasProducts)
import fam-mu-types-2.carrier

module fam-mu-types-2.reindex {o m e} (os es : Level) {𝒞 : Category o m e}
    (T : HasTerminal 𝒞) (P : HasProducts 𝒞) where

open fam-mu-types-2.carrier os es T P public

-- Reindex a tree from one parameter context to another along a context morphism.
-- The morphism is first-order data: `base` carries the leaf maps (applied only at
-- leaves), `bind` records one binder. So `reindex`'s recursive calls are syntactically
-- direct and structurally terminating — no closure, no fuel.
module Reindex {nA nB} (δA : Fin nA → Obj) (δB : Fin nB → Obj) where
  private
    module TA = Tree δA
    module TB = Tree δB

  data MorD : ∀ {k} (ρA : Fin k → Fin nA ⊎ Sort nA) (ρB : Fin k → Fin nB ⊎ Sort nB) →
              (∀ v → TA.DecoRes (ρA v)) → (∀ v → TB.DecoRes (ρB v)) →
              Set (o ⊔ m ⊔ e ⊔ lsuc os ⊔ lsuc es) where
    base : ∀ {k} {ρA ρB dA dB} (f : ∀ v → TA.El (ρA v) → TB.El (ρB v))
           (f-resp : ∀ v {a a'} → TA.elEq (ρA v) a a' → TB.elEq (ρB v) (f v a) (f v a'))
           (ffam : ∀ v a → TA.fib-el (ρA v) (dA v) a ⇒ TB.fib-el (ρB v) (dB v) (f v a)) →
           (∀ v {a a'} (p : TA.elEq (ρA v) a a') →
              (ffam v a' ∘ TA.fib-el-subst (ρA v) (dA v) p) ≈ (TB.fib-el-subst (ρB v) (dB v) (f-resp v p) ∘ ffam v a)) →
           MorD {k} ρA ρB dA dB
    bind : ∀ {k} {ρA ρB dA dB} (Q : Poly (suc k)) → MorD ρA ρB dA dB →
           MorD (extend ρA (inj₂ (mkSort ∣ Q ∣ ρA))) (extend ρB (inj₂ (mkSort ∣ Q ∣ ρB)))
                (TA.deco-ext Q dA) (TB.deco-ext Q dB)

  -- Index-only reindex: the index action of a context morphism, with no fibre data,
  -- so entirely at the category-free shapes. Carries both `MorD`'s index side (via
  -- `erase` below) and the fusion morphisms (`combine`), whose Γ-dependent fibre
  -- action lives externally in `FReindex`.
  data IMorD : ∀ {k} → (Fin k → Fin nA ⊎ Sort nA) → (Fin k → Fin nB ⊎ Sort nB) →
               Set (o ⊔ m ⊔ e ⊔ lsuc os ⊔ lsuc es) where
    ibase : ∀ {k} {ρA ρB} (f : ∀ v → TA.El (ρA v) → TB.El (ρB v))
            (f-resp : ∀ v {a a'} → TA.elEq (ρA v) a a' → TB.elEq (ρB v) (f v a) (f v a')) →
            IMorD {k} ρA ρB
    ibind : ∀ {k} {ρA ρB} (R : Sh.Poly (suc k)) → IMorD ρA ρB →
            IMorD (extend ρA (inj₂ (mkSort R ρA))) (extend ρB (inj₂ (mkSort R ρB)))

  mutual
    ireindex : ∀ {k} {R : Sh.Poly (suc k)} {ρA ρB} (md : IMorD ρA ρB) → TA.W R ρA → TB.W R ρB
    ireindex {R = R} md (TA.sup x) = TB.sup (ireindex-shape R (ibind R md) x)

    ireindex-shape : ∀ {j} (R : Sh.Poly j) {ηA ηB} (md : IMorD ηA ηB) → TA.⟦ R ⟧shape ηA → TB.⟦ R ⟧shape ηB
    ireindex-shape (const S) md a = a
    ireindex-shape (var v) md a = iapply md v a
    ireindex-shape (P + Q) md (inj₁ a) = inj₁ (ireindex-shape P md a)
    ireindex-shape (P + Q) md (inj₂ b) = inj₂ (ireindex-shape Q md b)
    ireindex-shape (P × Q) md (a , b) = ireindex-shape P md a , ireindex-shape Q md b
    ireindex-shape (μ Q') md t = ireindex md t

    iapply : ∀ {k} {ρA ρB} (md : IMorD {k} ρA ρB) (v : Fin k) → TA.El (ρA v) → TB.El (ρB v)
    iapply (ibase f _) v a = f v a
    iapply (ibind R md) Fin.zero a = ireindex md a
    iapply (ibind R md) (Fin.suc v) a = iapply md v a

  mutual
    ireindex-resp : ∀ {k} {R : Sh.Poly (suc k)} {ρA ρB} (md : IMorD ρA ρB) {t t' : TA.W R ρA} →
                    TA.W-≈ t t' → TB.W-≈ (ireindex md t) (ireindex md t')
    ireindex-resp {R = R} md {TA.sup x} {TA.sup y} p = ireindex-shape-resp R (ibind R md) {x} {y} p

    ireindex-shape-resp : ∀ {j} (R : Sh.Poly j) {ηA ηB} (md : IMorD ηA ηB) {a a' : TA.⟦ R ⟧shape ηA} →
                          TA.shape≈ R ηA a a' → TB.shape≈ R ηB (ireindex-shape R md a) (ireindex-shape R md a')
    ireindex-shape-resp (const S) md p = p
    ireindex-shape-resp (var v)   md p = iapply-resp md v p
    ireindex-shape-resp (P + Q) md {inj₁ _} {inj₁ _} p = ireindex-shape-resp P md p
    ireindex-shape-resp (P + Q) md {inj₂ _} {inj₂ _} p = ireindex-shape-resp Q md p
    ireindex-shape-resp (P × Q) md {_ , _} {_ , _} (p₁ , p₂) = ireindex-shape-resp P md p₁ , ireindex-shape-resp Q md p₂
    ireindex-shape-resp (μ Q') md {a} {a'} p = ireindex-resp md {a} {a'} p

    iapply-resp : ∀ {k} {ρA ρB} (md : IMorD {k} ρA ρB) (v : Fin k) {a a'} →
                  TA.elEq (ρA v) a a' → TB.elEq (ρB v) (iapply md v a) (iapply md v a')
    iapply-resp (ibase f f-resp) v p = f-resp v p
    iapply-resp (ibind R md) Fin.zero {a} {a'} p = ireindex-resp md {a} {a'} p
    iapply-resp (ibind R md) (Fin.suc v) p = iapply-resp md v p

  -- Erase the fibre fields; `MorD`'s index-level operations are `IMorD`'s.
  erase : ∀ {k} {ρA ρB dA dB} → MorD {k} ρA ρB dA dB → IMorD ρA ρB
  erase (base f f-resp _ _) = ibase f f-resp
  erase (bind Q md) = ibind ∣ Q ∣ (erase md)

  reindex : ∀ {k} {R : Sh.Poly (suc k)} {ρA ρB dA dB} → MorD ρA ρB dA dB → TA.W R ρA → TB.W R ρB
  reindex md = ireindex (erase md)

  reindex-shape : ∀ {j} (R : Sh.Poly j) {ηA ηB dA dB} → MorD ηA ηB dA dB → TA.⟦ R ⟧shape ηA → TB.⟦ R ⟧shape ηB
  reindex-shape R md = ireindex-shape R (erase md)

  apply : ∀ {k} {ρA ρB dA dB} (md : MorD {k} ρA ρB dA dB) (v : Fin k) → TA.El (ρA v) → TB.El (ρB v)
  apply md = iapply (erase md)

  reindex-resp : ∀ {k} {R : Sh.Poly (suc k)} {ρA ρB dA dB} (md : MorD ρA ρB dA dB) {t t' : TA.W R ρA} →
                 TA.W-≈ t t' → TB.W-≈ (reindex md t) (reindex md t')
  reindex-resp md {t} {t'} = ireindex-resp (erase md) {t} {t'}

  reindex-shape-resp : ∀ {j} (R : Sh.Poly j) {ηA ηB dA dB} (md : MorD ηA ηB dA dB) {a a' : TA.⟦ R ⟧shape ηA} →
                       TA.shape≈ R ηA a a' → TB.shape≈ R ηB (reindex-shape R md a) (reindex-shape R md a')
  reindex-shape-resp R md {a} {a'} = ireindex-shape-resp R (erase md) {a} {a'}

  apply-resp : ∀ {k} {ρA ρB dA dB} (md : MorD {k} ρA ρB dA dB) (v : Fin k) {a a'} →
               TA.elEq (ρA v) a a' → TB.elEq (ρB v) (apply md v a) (apply md v a')
  apply-resp md v {a} {a'} = iapply-resp (erase md) v {a} {a'}

  -- The fibre side of `reindex`: a 𝒞-morphism into the reindexed fibre.
  mutual
    reindex-fam : ∀ {j} (R : Poly j) {ηA ηB dA dB} (md : MorD ηA ηB dA dB) {a : TA.⟦ ∣ R ∣ ⟧shape ηA} →
                  TA.fib-shape R dA a ⇒ TB.fib-shape R dB (reindex-shape ∣ R ∣ md a)
    reindex-fam (const A) md = id _
    reindex-fam (var v) md {a} = apply-fam md v a
    reindex-fam (P + Q) md {inj₁ a} = reindex-fam P md
    reindex-fam (P + Q) md {inj₂ b} = reindex-fam Q md
    reindex-fam (P × Q) md {a , b} = prod-m (reindex-fam P md) (reindex-fam Q md)
    reindex-fam (μ Q') md {t} = reindex-fam-W md {t}

    reindex-fam-W : ∀ {k} {Q : Poly (suc k)} {ρA ρB dA dB} (md : MorD ρA ρB dA dB) {t : TA.W ∣ Q ∣ ρA} →
                    TA.fib Q dA t ⇒ TB.fib Q dB (reindex md t)
    reindex-fam-W {Q = Q} md {TA.sup x} = reindex-fam Q (bind Q md)

    apply-fam : ∀ {k} {ρA ρB dA dB} (md : MorD {k} ρA ρB dA dB) (v : Fin k) (a : TA.El (ρA v)) →
                TA.fib-el (ρA v) (dA v) a ⇒ TB.fib-el (ρB v) (dB v) (apply md v a)
    apply-fam (base _ _ ffam _) v a = ffam v a
    apply-fam (bind Q md) Fin.zero a = reindex-fam-W md {a}
    apply-fam (bind Q md) (Fin.suc v) a = apply-fam md v a

  -- The fibre reindex commutes with subst (naturality).
  mutual
    reindex-fam-natural : ∀ {j} (R : Poly j) {ηA ηB dA dB} (md : MorD ηA ηB dA dB)
                      {a a' : TA.⟦ ∣ R ∣ ⟧shape ηA} (p : TA.shape≈ ∣ R ∣ ηA a a') →
                      (reindex-fam R md {a'} ∘ TA.fib-shape-subst R dA p)
                        ≈ (TB.fib-shape-subst R dB (reindex-shape-resp ∣ R ∣ md p) ∘ reindex-fam R md {a})
    reindex-fam-natural (const A) md p = ≈-trans id-left (≈-sym id-right)
    reindex-fam-natural (var v)   md {a} {a'} p = apply-fam-natural md v {a} {a'} p
    reindex-fam-natural (P + Q) md {inj₁ a} {inj₁ a'} p = reindex-fam-natural P md p
    reindex-fam-natural (P + Q) md {inj₂ b} {inj₂ b'} p = reindex-fam-natural Q md p
    reindex-fam-natural (P × Q) md {a , b} {a' , b'} (p₁ , p₂) =
      ≈-trans (≈-sym (prod-m-comp _ _ _ _))
      (≈-trans (prod-m-cong (reindex-fam-natural P md p₁) (reindex-fam-natural Q md p₂))
               (prod-m-comp _ _ _ _))
    reindex-fam-natural (μ Q') md {t} {t'} p = reindex-fam-W-natural md {t} {t'} p

    reindex-fam-W-natural : ∀ {k} {Q : Poly (suc k)} {ρA ρB dA dB} (md : MorD ρA ρB dA dB)
                        {t t' : TA.W ∣ Q ∣ ρA} (p : TA.W-≈ t t') →
                        (reindex-fam-W md {t'} ∘ TA.fib-subst Q dA {x = t} {y = t'} p)
                          ≈ (TB.fib-subst Q dB {x = reindex md t} {y = reindex md t'}
                                          (reindex-resp md {t} {t'} p) ∘ reindex-fam-W md {t})
    reindex-fam-W-natural {Q = Q} md {TA.sup x} {TA.sup y} p = reindex-fam-natural Q (bind Q md) {x} {y} p

    apply-fam-natural : ∀ {k} {ρA ρB dA dB} (md : MorD {k} ρA ρB dA dB) (v : Fin k) {a a'}
                    (p : TA.elEq (ρA v) a a') →
                    (apply-fam md v a' ∘ TA.fib-el-subst (ρA v) (dA v) p)
                      ≈ (TB.fib-el-subst (ρB v) (dB v) (apply-resp md v p) ∘ apply-fam md v a)
    apply-fam-natural (base _ _ _ ffam-natural) v p = ffam-natural v p
    apply-fam-natural (bind Q md) Fin.zero    {a} {a'} p = reindex-fam-W-natural md {a} {a'} p
    apply-fam-natural (bind Q md) (Fin.suc v) p = apply-fam-natural md v p

-- Fibre reindex over an index-only reindex `cmb`, driven by an "external" per-variable action `act`: a
-- fold's fibre action is Γ-dependent, so it can't live in a reindex morphism and is carried separately.
-- The ambient Γ-fibre is `G`.
module FReindex {nA nB} {δA : Fin nA → Obj} {δB : Fin nB → Obj} (G : obj) where
  private
    module TA = Tree δA
    module TB = Tree δB
  open Reindex δA δB using (IMorD; ireindex; ireindex-shape; iapply; ibind)

  -- Defunctionalised action: `abase` supplies all var fibres directly (a Γ-dependent fold);
  -- `abind` extends across a binder. Data (not a function) so the recursion stays structural.
  data FAct : ∀ {k} {ρA : Fin k → Fin nA ⊎ Sort nA} {ρB : Fin k → Fin nB ⊎ Sort nB} →
              IMorD ρA ρB → (∀ v → TA.DecoRes (ρA v)) → (∀ v → TB.DecoRes (ρB v)) →
              Set (o ⊔ m ⊔ e ⊔ lsuc os ⊔ lsuc es) where
    abase : ∀ {k} {ρA ρB} {cmb : IMorD {k} ρA ρB} {dA dB}
            (afib : ∀ v (a : TA.El (ρA v)) → prod G (TA.fib-el (ρA v) (dA v) a) ⇒ TB.fib-el (ρB v) (dB v) (iapply cmb v a)) →
            FAct cmb dA dB
    abind : ∀ {k} {ρA ρB} (Q : Poly (suc k)) (cmb : IMorD ρA ρB) {dA dB} → FAct cmb dA dB →
            FAct (ibind ∣ Q ∣ cmb) (TA.deco-ext Q dA) (TB.deco-ext Q dB)

  mutual
    freindex-fam : ∀ {k} {Q : Poly (suc k)} {ρA ρB} {cmb : IMorD ρA ρB} {dA dB} (act : FAct cmb dA dB)
                   {t : TA.W ∣ Q ∣ ρA} → prod G (TA.fib Q dA t) ⇒ TB.fib Q dB (ireindex cmb t)
    freindex-fam {Q = Q} {cmb = cmb} act {TA.sup x} = freindex-shape-fam Q (abind Q cmb act) {x}

    freindex-shape-fam : ∀ {j} (R : Poly j) {ηA ηB} {cmb : IMorD ηA ηB} {dA dB} (act : FAct cmb dA dB)
                         {a : TA.⟦ ∣ R ∣ ⟧shape ηA} →
                         prod G (TA.fib-shape R dA a) ⇒ TB.fib-shape R dB (ireindex-shape ∣ R ∣ cmb a)
    freindex-shape-fam (const A') act = p₂
    freindex-shape-fam (var v)    act {a} = aapply act v a
    freindex-shape-fam (P + Q) act {inj₁ a} = freindex-shape-fam P act {a}
    freindex-shape-fam (P + Q) act {inj₂ b} = freindex-shape-fam Q act {b}
    freindex-shape-fam (P × Q) act {a , b} =
      strong-prod-m (freindex-shape-fam P act {a}) (freindex-shape-fam Q act {b})
    freindex-shape-fam (μ Q') act {t} = freindex-fam act {t}

    aapply : ∀ {k} {ρA ρB} {cmb : IMorD {k} ρA ρB} {dA dB} (act : FAct cmb dA dB) (v : Fin k) (a : TA.El (ρA v)) →
             prod G (TA.fib-el (ρA v) (dA v) a) ⇒ TB.fib-el (ρB v) (dB v) (iapply cmb v a)
    aapply (abase afib)      v           a = afib v a
    aapply (abind Q cmb act) Fin.zero    a = freindex-fam act {a}
    aapply (abind Q cmb act) (Fin.suc v) a = aapply act v a
