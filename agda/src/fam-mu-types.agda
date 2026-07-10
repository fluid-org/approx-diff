{-# OPTIONS --prop --postfix-projections --safe #-}

------------------------------------------------------------------------------
-- μ-types (parameterised initial algebras of polynomial functors) for the Fam
-- construction, built as sort-indexed W-types in setoids. This root module
-- proves the initial-algebra laws — β (BetaDef, the fold satisfies the algebra
-- square) and η (EtaDef, uniqueness), each by tree induction with the nested-μ
-- cases discharged through fusion — and re-exports the construction itself
-- from the layers beneath it.
------------------------------------------------------------------------------

open import Level using (Level; _⊔_; lift) renaming (suc to lsuc)
open import Data.Nat using (ℕ; suc)
import Data.Fin as Fin
open Fin using (Fin)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import Data.Unit using (tt)
open import prop using (_,_)
open import categories using (Category; HasTerminal; HasProducts)
open import prop-setoid as PS using ()
import indexed-family
open indexed-family using (Fam; _⇒f_)
import fam-mu-types.fuse

module fam-mu-types {o m e} (os es : Level) {𝒞 : Category o m e}
    (T : HasTerminal 𝒞) (P : HasProducts 𝒞) where

open fam-mu-types.fuse os es T P public

-- β/η proof machinery: the fusion of α's reconstruction with the fold equals the strong functorial action
-- of `⦅ alg ⦆`.
module BetaDef {n} {Γ A : Obj} {P : Poly (suc n)} {δ : Fin n → Obj}
               (alg : Mor (Fam𝒞-P.prod Γ (fobj μObj P (extend δ A))) A) where
  open HasMu hasMu using (strong-fmor; strong-extend-mor; ⦅_⦆; α)
  module Aα = AlphaDef P δ
  module Fα = FoldDef {Γ = Γ} {A = A} {P = P} {δ = δ} alg
  δ' = extend δ (μObj P δ)
  fs : ∀ i → Mor (Fam𝒞-P.prod Γ (δ' i)) (extend δ A i)
  fs = strong-extend-mor (λ i → Fam𝒞-P.p₂) Fα.foldMor

  -- Collapse the α-reconstruction reindex followed by the fold's reindex into one
  -- index-only reindex, so the fusion lemmas can treat them as a single morphism.
  module Rcomb = Reindex δ' (extend δ A)
  combine : (γ : Γ .idx .Carrier) → ∀ {k} {ρA ρB ρC} {dA dB dC} →
            Aα.R.MorD {k} ρA ρB dA dB → Fα.FMor {k} ρB ρC dB dC → Rcomb.IMorD {k} ρA ρC
  combine γ md fm = Rcomb.ibase (λ v a → Fα.fold-apply γ fm v (Aα.R.apply md v a))
    (λ v {a} {a'} p → Fα.fold-apply-resp (Γ .idx .isEquivalence .refl) fm v
      (Aα.R.apply-resp md v {a} {a'} p))

  mutual
    -- Defunctionalised relation "these two Rcomb.IMorDs are combine-lemma-related under binders".
    data Rel : ∀ {k} {ρA ρB} → Rcomb.IMorD {k} ρA ρB → Rcomb.IMorD {k} ρA ρB →
               Set (o ⊔ m ⊔ e ⊔ lsuc os ⊔ lsuc es) where
      rcomb : ∀ {k} {ρA ρB ρC} {dA dB dC} (γ : Γ .idx .Carrier) (Q : Poly (suc k))
              (md : Aα.R.MorD ρA ρB dA dB) (fm : Fα.FMor ρB ρC dB dC) →
              Rel (combine γ (Aα.R.bind Q md) (Fα.fbind Q fm)) (Rcomb.ibind ∣ Q ∣ (combine γ md fm))
      rbind : ∀ {k} {ρA ρB} {md₁ md₂ : Rcomb.IMorD ρA ρB} (R : Sh.Poly (suc k)) →
              Rel md₁ md₂ → Rel (Rcomb.ibind R md₁) (Rcomb.ibind R md₂)

    -- reindex respects Rel-related morphisms; the binder recursion is structural on Rel.
    reindex-mcong : ∀ {k} {R : Sh.Poly (suc k)} {ρA ρB} {md₁ md₂ : Rcomb.IMorD ρA ρB}
                    (r : Rel md₁ md₂) (t : Aα.TX.W R ρA) → Fα.TA'.W-≈ (Rcomb.ireindex md₁ t) (Rcomb.ireindex md₂ t)
    reindex-mcong {R = R} r (Aα.TX.sup y) = reindex-mcong-shape R (rbind R r) y

    reindex-mcong-shape : ∀ {j} (R : Sh.Poly j) {ρA ρB} {md₁ md₂ : Rcomb.IMorD ρA ρB}
                          (r : Rel md₁ md₂) (y : Aα.TX.⟦ R ⟧shape ρA) →
                          Fα.TA'.shape≈ R ρB (Rcomb.ireindex-shape R md₁ y) (Rcomb.ireindex-shape R md₂ y)
    reindex-mcong-shape (const S) r y = S .isEquivalence .refl
    reindex-mcong-shape (var v)    r y = mrel-apply r v
    reindex-mcong-shape (P + P') r (inj₁ y) = reindex-mcong-shape P r y
    reindex-mcong-shape (P + P') r (inj₂ z) = reindex-mcong-shape P' r z
    reindex-mcong-shape (P × P') r (y , z) = reindex-mcong-shape P r y , reindex-mcong-shape P' r z
    reindex-mcong-shape (μ R'') r y = reindex-mcong r y

    mrel-apply : ∀ {k} {ρA ρB} {md₁ md₂ : Rcomb.IMorD ρA ρB} (r : Rel md₁ md₂) (v : Fin k) {a} →
                 Fα.TA'.elEq (ρB v) (Rcomb.iapply md₁ v a) (Rcomb.iapply md₂ v a)
    mrel-apply (rcomb γ Q md fm)            Fin.zero     {a} = combine-lemma γ md fm a
    mrel-apply (rcomb {ρC = ρC} γ Q md fm) (Fin.suc v')      = Fα.TA'.elEq-refl (ρC v') _
    mrel-apply (rbind R r)                  Fin.zero     {a} = reindex-mcong r a
    mrel-apply (rbind R r)                 (Fin.suc v')      = mrel-apply r v'

    combine-lemma : ∀ {k} {Q : Poly (suc k)} {ρA ρB ρC} {dA dB dC} (γ : Γ .idx .Carrier)
                    (md : Aα.R.MorD ρA ρB dA dB) (fm : Fα.FMor ρB ρC dB dC) (t : Aα.TX.W ∣ Q ∣ ρA) →
                    Fα.TA'.W-≈ (Fα.fold-reindex γ fm (Aα.R.reindex md t)) (Rcomb.ireindex (combine γ md fm) t)
    combine-lemma {Q = Q} γ md fm (Aα.TX.sup x) = combine-lemma-shape Q Q γ md fm x

    combine-lemma-shape : ∀ {k} (Q : Poly (suc k)) (R : Poly (suc k)) {ρA ρB ρC} {dA dB dC} (γ : Γ .idx .Carrier)
                          (md : Aα.R.MorD ρA ρB dA dB) (fm : Fα.FMor ρB ρC dB dC)
                          (x : Aα.TX.⟦ ∣ R ∣ ⟧shape (extend ρA (inj₂ (mkSort ∣ Q ∣ ρA)))) →
                          Fα.TA'.shape≈ ∣ R ∣ (extend ρC (inj₂ (mkSort ∣ Q ∣ ρC)))
                            (Fα.fold-reindex-shape γ R (Fα.fbind Q fm) (Aα.R.reindex-shape ∣ R ∣ (Aα.R.bind Q md) x))
                            (Rcomb.ireindex-shape ∣ R ∣ (Rcomb.ibind ∣ Q ∣ (combine γ md fm)) x)
    combine-lemma-shape Q (const A')              γ md fm x = A' .idx .isEquivalence .refl
    combine-lemma-shape Q (var Fin.zero)          γ md fm x = combine-lemma γ md fm x
    combine-lemma-shape Q (var (Fin.suc v)) {ρC = ρC} γ md fm x = Fα.TA'.elEq-refl (ρC v) _
    combine-lemma-shape Q (P + Q') γ md fm (inj₁ x) = combine-lemma-shape Q P γ md fm x
    combine-lemma-shape Q (P + Q') γ md fm (inj₂ y) = combine-lemma-shape Q Q' γ md fm y
    combine-lemma-shape Q (P × Q') γ md fm (x , y) =
      combine-lemma-shape Q P γ md fm x , combine-lemma-shape Q Q' γ md fm y
    combine-lemma-shape Q (μ R'') γ md fm x =
      Fα.TA'.W-≈-trans {x = Fα.fold-reindex γ (Fα.fbind Q fm) (Aα.R.reindex (Aα.R.bind Q md) x)}
                       {y = Rcomb.ireindex (combine γ (Aα.R.bind Q md) (Fα.fbind Q fm)) x}
                       (combine-lemma γ (Aα.R.bind Q md) (Fα.fbind Q fm) x)
                       (reindex-mcong (rcomb γ Q md fm) x)

  -- Fibre mirror of the collapse, at a fixed γ: `combine-act` is combine's Γ-dependent
  -- fibre action, and the lemmas transport the fibre composites along the corresponding
  -- index proofs, mirroring `Rel`/`reindex-mcong`/`combine-lemma` clause by clause.
  module CombineFam (γ : Γ .idx .Carrier) where
    module FR = FReindex {δA = δ'} {δB = extend δ A} (Γ .fam .fm γ)

    combine-act : ∀ {k} {ρA ρB ρC} {dA dB dC} (md : Aα.R.MorD {k} ρA ρB dA dB) (fm : Fα.FMor {k} ρB ρC dB dC) →
                  FR.FAct (combine γ md fm) dA dC
    combine-act md fm =
      FR.abase (λ v a → Fα.fold-apply-fam γ fm v (Aα.R.apply md v a)
                        ∘ prod-m (id (Fam.fm (Γ .fam) γ)) (Aα.R.apply-fam md v a))

    mutual
      -- Fibre actions over Rel-related morphisms, related constructor by constructor.
      data RelAct : ∀ {k} {ρA ρB} {dA dB} {md₁ md₂ : Rcomb.IMorD {k} ρA ρB} →
                    Rel md₁ md₂ → FR.FAct md₁ dA dB → FR.FAct md₂ dA dB →
                    Set (o ⊔ m ⊔ e ⊔ lsuc os ⊔ lsuc es) where
        rcombA : ∀ {k} {ρA ρB ρC} {dA dB dC} (Q : Poly (suc k))
                 (md : Aα.R.MorD ρA ρB dA dB) (fm : Fα.FMor ρB ρC dB dC) →
                 RelAct (rcomb γ Q md fm) (combine-act (Aα.R.bind Q md) (Fα.fbind Q fm))
                        (FR.abind Q (combine γ md fm) (combine-act md fm))
        rbindA : ∀ {k} {ρA ρB} {dA dB} {md₁ md₂ : Rcomb.IMorD ρA ρB} {r : Rel md₁ md₂}
                 {a₁ : FR.FAct md₁ dA dB} {a₂ : FR.FAct md₂ dA dB} (Q : Poly (suc k)) →
                 RelAct r a₁ a₂ → RelAct (rbind ∣ Q ∣ r) (FR.abind Q md₁ a₁) (FR.abind Q md₂ a₂)

      reindex-mcong-fam : ∀ {k} {Q : Poly (suc k)} {ρA ρB} {dA dB} {md₁ md₂ : Rcomb.IMorD ρA ρB}
                          {r : Rel md₁ md₂} {a₁ : FR.FAct md₁ dA dB} {a₂ : FR.FAct md₂ dA dB}
                          (ra : RelAct r a₁ a₂) (t : Aα.TX.W ∣ Q ∣ ρA) →
                          Fα.TA'.fib-subst Q dB {x = Rcomb.ireindex md₁ t} {y = Rcomb.ireindex md₂ t}
                             (reindex-mcong r t) ∘ FR.freindex-fam a₁ {t} ≈
                          FR.freindex-fam a₂ {t}
      reindex-mcong-fam {Q = Q} ra (Aα.TX.sup y) = reindex-mcong-shape-fam Q (rbindA Q ra) y

      reindex-mcong-shape-fam : ∀ {j} (R : Poly j) {ρA ρB} {dA dB} {md₁ md₂ : Rcomb.IMorD ρA ρB}
                                {r : Rel md₁ md₂} {a₁ : FR.FAct md₁ dA dB} {a₂ : FR.FAct md₂ dA dB}
                                (ra : RelAct r a₁ a₂) (y : Aα.TX.⟦ ∣ R ∣ ⟧shape ρA) →
                                (Fα.TA'.fib-shape-subst R dB (reindex-mcong-shape ∣ R ∣ r y) ∘ FR.freindex-shape-fam R a₁ {y})
                                ≈ FR.freindex-shape-fam R a₂ {y}
      reindex-mcong-shape-fam (const A') ra y =
        ≈-trans (∘-cong (A' .fam .refl*) ≈-refl) id-left
      reindex-mcong-shape-fam (var v) ra y = mrel-apply-fam ra v
      reindex-mcong-shape-fam (P + P') ra (inj₁ y) = reindex-mcong-shape-fam P ra y
      reindex-mcong-shape-fam (P + P') ra (inj₂ z) = reindex-mcong-shape-fam P' ra z
      reindex-mcong-shape-fam (P × P') ra (y , z) =
        ≈-trans (strong-prod-m-post _ _ _ _)
          (strong-prod-m-cong (reindex-mcong-shape-fam P ra y) (reindex-mcong-shape-fam P' ra z))
      reindex-mcong-shape-fam (μ R'') ra y = reindex-mcong-fam {Q = R''} ra y

      mrel-apply-fam : ∀ {k} {ρA ρB} {dA dB} {md₁ md₂ : Rcomb.IMorD ρA ρB}
                       {r : Rel md₁ md₂} {a₁ : FR.FAct md₁ dA dB} {a₂ : FR.FAct md₂ dA dB}
                       (ra : RelAct r a₁ a₂) (v : Fin k) {z} →
                       Fα.TA'.fib-el-subst (ρB v) (dB v) (mrel-apply r v {z}) ∘ FR.aapply a₁ v z ≈ FR.aapply a₂ v z
      mrel-apply-fam (rcombA Q md fm) Fin.zero {z} = combine-lemma-fam md fm z
      mrel-apply-fam (rcombA {ρC = ρC} Q md fm) (Fin.suc v') {z} =
        ≈-trans (∘-cong (Fα.TA'.fib-el-refl* (ρC v') _ _) ≈-refl) id-left
      mrel-apply-fam (rbindA Q ra) Fin.zero {z} = reindex-mcong-fam {Q = Q} ra z
      mrel-apply-fam (rbindA Q ra) (Fin.suc v') = mrel-apply-fam ra v'

      combine-lemma-fam : ∀ {k} {Q : Poly (suc k)} {ρA ρB ρC} {dA dB dC}
                          (md : Aα.R.MorD ρA ρB dA dB) (fm : Fα.FMor ρB ρC dB dC) (t : Aα.TX.W ∣ Q ∣ ρA) →
                          (Fα.TA'.fib-subst Q dC {x = Fα.fold-reindex γ fm (Aα.R.reindex md t)}
                                            {y = Rcomb.ireindex (combine γ md fm) t}
                             (combine-lemma γ md fm t)
                           ∘ (Fα.fold-reindex-fam γ fm (Aα.R.reindex md t)
                              ∘ prod-m (id _) (Aα.R.reindex-fam-W {Q = Q} md {t})))
                          ≈ FR.freindex-fam (combine-act md fm) {t}
      combine-lemma-fam {Q = Q} md fm (Aα.TX.sup x) = combine-lemma-shape-fam Q Q md fm x

      combine-lemma-shape-fam : ∀ {k} (Q : Poly (suc k)) (R : Poly (suc k)) {ρA ρB ρC} {dA dB dC}
                                (md : Aα.R.MorD ρA ρB dA dB) (fm : Fα.FMor ρB ρC dB dC)
                                (x : Aα.TX.⟦ ∣ R ∣ ⟧shape (extend ρA (inj₂ (mkSort ∣ Q ∣ ρA)))) →
                                Fα.TA'.fib-shape-subst R (Fα.TA'.deco-ext Q dC)
                                   (combine-lemma-shape Q R γ md fm x)
                                 ∘ (Fα.fold-reindex-shape-fam γ R (Fα.fbind Q fm)
                                      (Aα.R.reindex-shape ∣ R ∣ (Aα.R.bind Q md) x)
                                    ∘ prod-m (id _) (Aα.R.reindex-fam R (Aα.R.bind Q md) {x}))
                                ≈ FR.freindex-shape-fam R (FR.abind Q (combine γ md fm) (combine-act md fm)) {x}
      combine-lemma-shape-fam Q (const A') md fm x =
        ≈-trans (∘-cong (A' .fam .refl*) ≈-refl)
          (≈-trans id-left (≈-trans (pair-p₂ _ _) id-left))
      combine-lemma-shape-fam Q (var Fin.zero) md fm x = combine-lemma-fam md fm x
      combine-lemma-shape-fam Q (var (Fin.suc v)) {ρC = ρC} md fm x =
        ≈-trans (∘-cong (Fα.TA'.fib-el-refl* (ρC v) _ _) ≈-refl) id-left
      combine-lemma-shape-fam Q (P + Q') md fm (inj₁ x) = combine-lemma-shape-fam Q P md fm x
      combine-lemma-shape-fam Q (P + Q') md fm (inj₂ y) = combine-lemma-shape-fam Q Q' md fm y
      combine-lemma-shape-fam Q (P × Q') md fm (x , y) =
        ≈-trans (∘-cong ≈-refl (strong-prod-m-pre _ _ _ _ _))
          (≈-trans (strong-prod-m-post _ _ _ _)
            (strong-prod-m-cong (combine-lemma-shape-fam Q P md fm x) (combine-lemma-shape-fam Q Q' md fm y)))
      combine-lemma-shape-fam Q (μ R'') md fm x =
        ≈-trans (∘-cong (Fα.TA'.fib-trans* R'' _
                           {x = Fα.fold-reindex γ (Fα.fbind Q fm) (Aα.R.reindex (Aα.R.bind Q md) x)}
                           {y = Rcomb.ireindex (combine γ (Aα.R.bind Q md) (Fα.fbind Q fm)) x}
                           {z = Rcomb.ireindex (Rcomb.ibind ∣ Q ∣ (combine γ md fm)) x}
                           (reindex-mcong (rcomb γ Q md fm) x)
                           (combine-lemma γ (Aα.R.bind Q md) (Fα.fbind Q fm) x)) ≈-refl)
          (≈-trans (assoc _ _ _)
            (≈-trans (∘-cong ≈-refl (combine-lemma-fam (Aα.R.bind Q md) (Fα.fbind Q fm) x))
              (reindex-mcong-fam {Q = R''} (rcombA Q md fm) x)))

  -- Correspondence hypothesis for the fuse instances: `combine mor₀ fbase` acts as the fold at the
  -- recursion slot and as the identity at the parameter slots.
  corr-fs : ∀ i {γ₁ γ₂} (γ≈ : _≈s_ (Γ .idx) γ₁ γ₂) {a₁ a₂} (a≈ : _≈s_ (δ' i .idx) a₁ a₂) →
            _≈s_ (extend δ A i .idx)
                 (Rcomb.iapply (combine γ₁ Aα.mor₀ Fα.fbase) i a₁)
                 (fs i .idxf .PS._⇒_.func (γ₂ , a₂))
  corr-fs Fin.zero γ≈ {a₁} {a₂} a≈ = Fα.fold-idx-resp γ≈ {a₁} {a₂} a≈
  corr-fs (Fin.suc j) γ≈ a≈ = a≈

  -- fold-shape-idx ∘ reindex-shape ∘ embed-idx ≈ strong-fmor's idx action of the fold.
  β-idx : (R : Poly (suc n)) → ∀ {γ₁ γ₂} (γ≈ : _≈s_ (Γ .idx) γ₁ γ₂) {m₁ m₂}
          (m≈ : _≈s_ (fobj μObj R δ' .idx) m₁ m₂) →
          _≈s_ (fobj μObj R (extend δ A) .idx)
               (Fα.fold-shape-idx R γ₁ (Aα.R.reindex-shape ∣ R ∣ Aα.mor₀ (Aα.embed-idx R m₁)))
               (strong-fmor R fs .idxf .PS._⇒_.func (γ₂ , m₂))
  β-idx (const A')        γ≈ m≈ = m≈
  β-idx (var Fin.zero)    γ≈ {m₁} {m₂} m≈ = Fα.fold-idx-resp γ≈ {m₁} {m₂} m≈
  β-idx (var (Fin.suc j)) γ≈ m≈ = m≈
  β-idx (Q₁ + Q₂) γ≈ {inj₁ _} {inj₁ _} m≈ = β-idx Q₁ γ≈ m≈
  β-idx (Q₁ + Q₂) γ≈ {inj₂ _} {inj₂ _} m≈ = β-idx Q₂ γ≈ m≈
  β-idx (Q₁ × Q₂) γ≈ {_ , _} {_ , _} (m≈₁ , m≈₂) = β-idx Q₁ γ≈ m≈₁ , β-idx Q₂ γ≈ m≈₂
  β-idx (μ Q') {γ₁} {γ₂} γ≈ {m₁} {m₂} m≈ =
    Fα.TA'.W-≈-trans
      {x = Fα.fold-shape-idx (μ Q') γ₁ (Aα.R.reindex-shape ∣ μ Q' ∣ Aα.mor₀ (Aα.embed-idx (μ Q') m₁))}
      {y = Rcomb.ireindex (combine γ₁ Aα.mor₀ Fα.fbase) m₁}
      {z = strong-fmor (μ Q') fs .idxf .PS._⇒_.func (γ₂ , m₂)}
      (combine-lemma {Q = Q'} γ₁ Aα.mor₀ Fα.fbase m₁)
      (fuse-idx {n = suc n} {Γ = Γ} {sₛ = δ'} {sₜ = extend δ A} Q'
        (λ γ → combine γ Aα.mor₀ Fα.fbase) fs corr-fs γ≈ {m₁} {m₂} m≈)

  -- Fibre analogue of `β-idx`: the fibre transformations agree (modulo transport along β-idx).
  β-fam : (R : Poly (suc n)) → ∀ {γ} {m} →
          Category._≈_ 𝒞
            (fobj μObj R (extend δ A) .fam .subst
               (β-idx R (Γ .idx .isEquivalence .refl) (fobj μObj R δ' .idx .isEquivalence .refl))
             ∘ (Fα.fold-shape-fam R γ (Aα.R.reindex-shape ∣ R ∣ Aα.mor₀ (Aα.embed-idx R m))
                ∘ prod-m (id _) (Aα.R.reindex-fam R Aα.mor₀ ∘ Aα.embed-fam R m)))
            (strong-fmor R fs .famf ._⇒f_.transf (γ , m))
  β-fam (const A') = ≈-trans (∘-cong (A' .fam .refl*) ≈-refl) (≈-trans id-left (≈-trans (∘-cong ≈-refl (≈-trans (prod-m-cong ≈-refl id-left) prod-m-id)) id-right))
  β-fam (var Fin.zero) = ≈-trans (∘-cong (A .fam .refl*) ≈-refl) (≈-trans id-left (≈-trans (∘-cong ≈-refl (≈-trans (prod-m-cong ≈-refl id-left) prod-m-id)) id-right))
  β-fam (var (Fin.suc i)) = ≈-trans (∘-cong (δ i .fam .refl*) ≈-refl) (≈-trans id-left (≈-trans (∘-cong ≈-refl (≈-trans (prod-m-cong ≈-refl id-left) prod-m-id)) id-right))
  β-fam (R₁ + R₂) {m = inj₁ m'} = ≈-trans (β-fam R₁) (≈-sym (≈-trans id-left id-left))
  β-fam (R₁ + R₂) {m = inj₂ m'} = ≈-trans (β-fam R₂) (≈-sym (≈-trans id-left id-left))
  β-fam (R₁ × R₂) {m = m₁' , m₂'} =
    ≈-trans (∘-cong ≈-refl (pair-natural _ _ _))
      (≈-trans (pair-compose _ _ _ _)
        (pair-cong
          (≈-trans (∘-cong ≈-refl
                     (≈-trans (assoc _ _ _)
                       (≈-trans (∘-cong ≈-refl
                                  (≈-trans (∘-cong ≈-refl (prod-m-cong ≈-refl (≈-sym (prod-m-comp _ _ _ _))))
                                    (strong-p₁-natural (id _) _ _)))
                         (≈-sym (assoc _ _ _)))))
            (≈-trans (≈-sym (assoc _ _ _))
              (≈-trans (∘-cong (β-fam R₁) ≈-refl)
                (≈-trans (∘-cong ≈-refl (pair-cong ≈-refl (≈-sym id-left))) (≈-sym id-left)))))
          (≈-trans (∘-cong ≈-refl
                     (≈-trans (assoc _ _ _)
                       (≈-trans (∘-cong ≈-refl
                                  (≈-trans (∘-cong ≈-refl (prod-m-cong ≈-refl (≈-sym (prod-m-comp _ _ _ _))))
                                    (strong-p₂-natural (id _) _ _)))
                         (≈-sym (assoc _ _ _)))))
            (≈-trans (≈-sym (assoc _ _ _))
              (≈-trans (∘-cong (β-fam R₂) ≈-refl)
                (≈-trans (∘-cong ≈-refl (pair-cong ≈-refl (≈-sym id-left))) (≈-sym id-left)))))))
  β-fam (μ Q') {γ} {m} =
    ≈-trans (∘-cong ≈-refl (∘-cong ≈-refl (prod-m-cong ≈-refl id-right)))
      (≈-trans (∘-cong (Fα.TA'.fib-trans* Q' _
                          {x = Fα.fold-reindex γ Fα.fbase (Aα.R.reindex Aα.mor₀ m)}
                          {y = Rcomb.ireindex (combine γ Aα.mor₀ Fα.fbase) m}
                          {z = strong-fmor (μ Q') fs .idxf .PS._⇒_.func (γ , m)}
                          (fuse-idx {n = suc n} {Γ = Γ} {sₛ = δ'} {sₜ = extend δ A} Q'
                            (λ γ' → combine γ' Aα.mor₀ Fα.fbase) fs corr-fs
                            (Γ .idx .isEquivalence .refl) {m} {m}
                            (μObj Q' δ' .idx .isEquivalence .refl {m}))
                          (combine-lemma {Q = Q'} γ Aα.mor₀ Fα.fbase m)) ≈-refl)
        (≈-trans (assoc _ _ _)
          (≈-trans (∘-cong ≈-refl (Cγ.combine-lemma-fam {Q = Q'} Aα.mor₀ Fα.fbase m))
            (fuse-fam γ Q' (λ γ' → combine γ' Aα.mor₀ Fα.fbase)
              (Cγ.combine-act Aα.mor₀ Fα.fbase) fs corr-fs corr-fs-fam {m}))))
    where
      module Cγ = CombineFam γ
      corr-fs-fam : ∀ i {a} →
                    (extend δ A i .fam .subst
                       (corr-fs i (Γ .idx .isEquivalence .refl) (δ' i .idx .isEquivalence .refl {a}))
                     ∘ Cγ.FR.aapply (Cγ.combine-act Aα.mor₀ Fα.fbase) i a)
                    ≈ (fs i .famf ._⇒f_.transf (γ , a))
      corr-fs-fam Fin.zero {a} =
        ≈-trans (∘-cong (A .fam .refl*) ≈-refl)
          (≈-trans id-left (≈-trans (∘-cong ≈-refl prod-m-id) id-right))
      corr-fs-fam (Fin.suc j) {a} =
        ≈-trans (∘-cong (δ j .fam .refl*) ≈-refl)
          (≈-trans id-left (≈-trans (∘-cong ≈-refl prod-m-id) id-right))

-- η/uniqueness machinery: any h satisfying the β square agrees with the fold, pointwise by tree induction.
-- Nested-μ case collapses h's strong action to an index-only reindex (`cmb-hs`, via fuse-idx) and telescopes
-- it against the fold.
module EtaDef {n} {Γ A : Obj} {P : Poly (suc n)} {δ : Fin n → Obj}
              (alg : Mor (Fam𝒞-P.prod Γ (fobj μObj P (extend δ A))) A)
              (h : Mor (Fam𝒞-P.prod Γ (μObj P δ)) A)
              (eq : Fam𝒞._≈_
                      (Fam𝒞._∘_ h (Fam𝒞-P.pair Fam𝒞-P.p₁ (Fam𝒞._∘_ (AlphaDef.αmor P δ) Fam𝒞-P.p₂)))
                      (Fam𝒞._∘_ alg (Fam𝒞-P.pair Fam𝒞-P.p₁
                        (HasMu.strong-fmor hasMu P (HasMu.strong-extend-mor hasMu (λ i → Fam𝒞-P.p₂) h))))) where
  open HasMu hasMu using (strong-fmor; strong-extend-mor)
  module Aα = AlphaDef P δ
  module Fα = FoldDef {Γ = Γ} {A = A} {P = P} {δ = δ} alg
  δ' = extend δ (μObj P δ)
  hs : ∀ i → Mor (Fam𝒞-P.prod Γ (δ' i)) (extend δ A i)
  hs = strong-extend-mor (λ i → Fam𝒞-P.p₂) h

  -- Context shift δ → δ': the μ-binder slot of the body environment is exactly the
  -- fresh δ' slot (identity on indices and fibres).
  module Rδ = Reindex δ δ'

  mor₀δ : Rδ.MorD (Sh.η₀ ∣ P ∣) (λ v → inj₁ v)
                  (Fα.Tδ.deco-ext P {ρ̄ = λ i → inj₁ i} (λ i → lift tt)) (λ v → lift tt)
  mor₀δ = Rδ.base (λ { Fin.zero a → a ; (Fin.suc i) a → a })
                  (λ { Fin.zero p → p ; (Fin.suc i) p → p })
                  (λ { Fin.zero a → id _ ; (Fin.suc i) a → id _ })
                  (λ { Fin.zero p → ≈-trans id-left (≈-sym id-right)
                     ; (Fin.suc i) p → ≈-trans id-left (≈-sym id-right) })

  -- Shift a shape over the μ-binder environment into `fobj`'s native form over δ'.
  shift : (R : Poly (suc n)) → Fα.Tδ.⟦ ∣ R ∣ ⟧shape (Sh.η₀ ∣ P ∣) → fobj μObj R δ' .idx .Carrier
  shift R x = Aα.unembed-idx R (Rδ.reindex-shape ∣ R ∣ mor₀δ x)

  shift-resp : (R : Poly (suc n)) {x y : Fα.Tδ.⟦ ∣ R ∣ ⟧shape (Sh.η₀ ∣ P ∣)} →
               Fα.Tδ.shape≈ ∣ R ∣ (Sh.η₀ ∣ P ∣) x y → _≈s_ (fobj μObj R δ' .idx) (shift R x) (shift R y)
  shift-resp R p = Aα.unembed-idx-resp R (Rδ.reindex-shape-resp ∣ R ∣ mor₀δ p)

  -- Round trip: shifting into δ' and reindexing back along mor₀ is the identity,
  -- on indices and fibres.
  mutual
    data RT : ∀ {j} {ρD : Fin j → Fin n ⊎ Sort n} {ρX : Fin j → Fin (suc n) ⊎ Sort (suc n)}
              {dD : ∀ v → Fα.Tδ.DecoRes (ρD v)} {dX : ∀ v → Aα.TX.DecoRes (ρX v)} →
              Rδ.MorD ρD ρX dD dX → Aα.R.MorD ρX ρD dX dD → Set (o ⊔ m ⊔ e ⊔ lsuc os ⊔ lsuc es) where
      rtbase : RT mor₀δ Aα.mor₀
      rtbind : ∀ {j} {ρD ρX dD dX} {md : Rδ.MorD {j} ρD ρX dD dX} {md' : Aα.R.MorD ρX ρD dX dD} (Q : Poly (suc j)) →
               RT md md' → RT (Rδ.bind Q md) (Aα.R.bind Q md')

    rt-shape : ∀ {j} (S : Poly j) {ρD ρX dD dX} {md : Rδ.MorD ρD ρX dD dX} {md' : Aα.R.MorD ρX ρD dX dD}
               (rt : RT md md') (z : Fα.Tδ.⟦ ∣ S ∣ ⟧shape ρD) →
               Fα.Tδ.shape≈ ∣ S ∣ ρD (Aα.R.reindex-shape ∣ S ∣ md' (Rδ.reindex-shape ∣ S ∣ md z)) z
    rt-shape (const A') rt z = A' .idx .isEquivalence .refl
    rt-shape (var v) rt z = rt-apply rt v
    rt-shape (S₁ + S₂) rt (inj₁ z) = rt-shape S₁ rt z
    rt-shape (S₁ + S₂) rt (inj₂ z) = rt-shape S₂ rt z
    rt-shape (S₁ × S₂) rt (z₁ , z₂) = rt-shape S₁ rt z₁ , rt-shape S₂ rt z₂
    rt-shape (μ S') rt (Fα.Tδ.sup z) = rt-shape S' (rtbind S' rt) z

    rt-apply : ∀ {j} {ρD ρX dD dX} {md : Rδ.MorD {j} ρD ρX dD dX} {md' : Aα.R.MorD ρX ρD dX dD}
               (rt : RT md md') (v : Fin j) {z} → Fα.Tδ.elEq (ρD v) (Aα.R.apply md' v (Rδ.apply md v z)) z
    rt-apply rtbase Fin.zero {z} = Fα.Tδ.W-≈-refl z
    rt-apply rtbase (Fin.suc i) {z} = δ i .idx .isEquivalence .refl
    rt-apply (rtbind S' rt) Fin.zero {z} = rt-shape (μ S') rt z
    rt-apply (rtbind S' rt) (Fin.suc v) = rt-apply rt v

    rtf-shape : ∀ {j} (S : Poly j) {ρD ρX dD dX} {md : Rδ.MorD ρD ρX dD dX} {md' : Aα.R.MorD ρX ρD dX dD}
                (rt : RT md md') (z : Fα.Tδ.⟦ ∣ S ∣ ⟧shape ρD) →
                Fα.Tδ.fib-shape-subst S dD (rt-shape S rt z)
                 ∘ (Aα.R.reindex-fam S md' {Rδ.reindex-shape ∣ S ∣ md z} ∘ Rδ.reindex-fam S md {z}) ≈ id _
    rtf-shape (const A') rt z =
      ≈-trans (∘-cong (A' .fam .refl*) ≈-refl) (≈-trans id-left id-left)
    rtf-shape (var v) rt z = rtf-apply rt v
    rtf-shape (S₁ + S₂) rt (inj₁ z) = rtf-shape S₁ rt z
    rtf-shape (S₁ + S₂) rt (inj₂ z) = rtf-shape S₂ rt z
    rtf-shape (S₁ × S₂) rt (z₁ , z₂) =
      ≈-trans (∘-cong ≈-refl (≈-sym (prod-m-comp _ _ _ _)))
        (≈-trans (≈-sym (prod-m-comp _ _ _ _))
          (≈-trans (prod-m-cong (rtf-shape S₁ rt z₁) (rtf-shape S₂ rt z₂)) prod-m-id))
    rtf-shape (μ S') rt (Fα.Tδ.sup z) = rtf-shape S' (rtbind S' rt) z

    rtf-apply : ∀ {j} {ρD ρX dD dX} {md : Rδ.MorD {j} ρD ρX dD dX} {md' : Aα.R.MorD ρX ρD dX dD}
                (rt : RT md md') (v : Fin j) {z} →
                Fα.Tδ.fib-el-subst (ρD v) (dD v) (rt-apply rt v {z})
                 ∘ (Aα.R.apply-fam md' v (Rδ.apply md v z) ∘ Rδ.apply-fam md v z) ≈ id _
    rtf-apply rtbase Fin.zero {z} =
      ≈-trans (∘-cong (Fα.Tδ.fib-refl* P _ z) ≈-refl) (≈-trans id-left id-left)
    rtf-apply rtbase (Fin.suc i) {z} =
      ≈-trans (∘-cong (δ i .fam .refl*) ≈-refl) (≈-trans id-left id-left)
    rtf-apply (rtbind S' rt) Fin.zero {z} = rtf-shape (μ S') rt z
    rtf-apply (rtbind S' rt) (Fin.suc v) = rtf-apply rt v

  -- α reconstructs the shifted shape.
  roundtrip : (x : Fα.Tδ.⟦ ∣ P ∣ ⟧shape (Sh.η₀ ∣ P ∣)) →
              Fα.Tδ.W-≈ (Aα.αmor .idxf .PS._⇒_.func (shift P x)) (Fα.Tδ.sup x)
  roundtrip x =
    Fα.Tδ.shape≈-trans ∣ P ∣ (Sh.η₀ ∣ P ∣)
      (Aα.R.reindex-shape-resp ∣ P ∣ Aα.mor₀ (Aα.embed-unembed P (Rδ.reindex-shape ∣ P ∣ mor₀δ x))) (rt-shape P rtbase x)

  shift-fam : (R : Poly (suc n)) (x : Fα.Tδ.⟦ ∣ R ∣ ⟧shape (Sh.η₀ ∣ P ∣)) →
              Fα.Tδ.fib-shape R (Fα.Tδ.deco-ext P (λ i → lift tt)) x ⇒ fobj μObj R δ' .fam .fm (shift R x)
  shift-fam R x = Aα.unembed-fam R (Rδ.reindex-shape ∣ R ∣ mor₀δ x) ∘ Rδ.reindex-fam R mor₀δ {x}

  roundtrip-fam : (x : Fα.Tδ.⟦ ∣ P ∣ ⟧shape (Sh.η₀ ∣ P ∣)) →
                  μObj P δ .fam .subst (roundtrip x) ∘ (Aα.αmor .famf ._⇒f_.transf (shift P x) ∘ shift-fam P x) ≈ id _
  roundtrip-fam x =
    ≈-trans (∘-cong (Fα.Tδ.fib-shape-trans* P _
                       (rt-shape P rtbase x)
                       (Aα.R.reindex-shape-resp ∣ P ∣ Aα.mor₀ (Aα.embed-unembed P y'))) ≈-refl)
      (≈-trans (assoc _ _ _)
        (≈-trans (∘-cong ≈-refl
                   (≈-trans (∘-cong ≈-refl (assoc _ _ _))
                     (≈-trans (≈-sym (assoc _ _ _))
                       (≈-trans (∘-cong (≈-sym (Aα.R.reindex-fam-natural P Aα.mor₀
                                                 (Aα.embed-unembed P y'))) ≈-refl)
                         (≈-trans (assoc _ _ _)
                           (∘-cong ≈-refl
                             (≈-trans (∘-cong ≈-refl (≈-sym (assoc _ _ _)))
                               (≈-trans (≈-sym (assoc _ _ _))
                                 (≈-trans (∘-cong (Aα.embed-unembed-fam P y') ≈-refl) id-left)))))))))
          (rtf-shape P rtbase x)))
    where y' = Rδ.reindex-shape ∣ P ∣ mor₀δ x

  -- Transport along the inverted round trip is α's fibre action after the shift.
  shift-subst : (x : Fα.Tδ.⟦ ∣ P ∣ ⟧shape (Sh.η₀ ∣ P ∣)) →
                μObj P δ .fam .subst
                  (Fα.Tδ.W-≈-sym {x = Aα.αmor .idxf .PS._⇒_.func (shift P x)} {y = Fα.Tδ.sup x}
                    (roundtrip x))
                ≈ Aα.αmor .famf ._⇒f_.transf (shift P x) ∘ shift-fam P x
  shift-subst x =
    ≈-trans (≈-sym id-right)
      (≈-trans (∘-cong ≈-refl (≈-sym (roundtrip-fam x)))
        (≈-trans (≈-sym (assoc _ _ _))
          (≈-trans (∘-cong (≈-trans (≈-sym (μObj P δ .fam .trans*
                                              (Fα.Tδ.W-≈-sym {x = Aα.αmor .idxf .PS._⇒_.func (shift P x)}
                                                             {y = Fα.Tδ.sup x} (roundtrip x))
                                              (roundtrip x)))
                             (μObj P δ .fam .refl*)) ≈-refl)
            id-left)))

  -- h's strong action collapsed to an index-only reindex, and its fuse-idx hypothesis.
  module Rcomb = Reindex δ' (extend δ A)
  cmb-hs : Γ .idx .Carrier → Rcomb.IMorD (λ v → inj₁ v) (λ v → inj₁ v)
  cmb-hs γ = Rcomb.ibase (λ { Fin.zero a → h .idxf .PS._⇒_.func (γ , a) ; (Fin.suc i) a → a })
                         (λ { Fin.zero p → h .idxf .PS._⇒_.func-resp-≈ (Γ .idx .isEquivalence .refl , p)
                            ; (Fin.suc i) p → p })

  corr-hs : ∀ i {γ₁ γ₂} (γ≈ : _≈s_ (Γ .idx) γ₁ γ₂) {a₁ a₂} (a≈ : _≈s_ (δ' i .idx) a₁ a₂) →
            _≈s_ (extend δ A i .idx) (Rcomb.iapply (cmb-hs γ₁) i a₁) (hs i .idxf .PS._⇒_.func (γ₂ , a₂))
  corr-hs Fin.zero γ≈ a≈ = h .idxf .PS._⇒_.func-resp-≈ (γ≈ , a≈)
  corr-hs (Fin.suc j) γ≈ a≈ = a≈

  mutual
    -- h agrees with the fold, pointwise. At sup, round-trip through α's reconstruction so the β square
    -- `eq` applies, then push through the shape.
    η-idx : ∀ {γ₁ γ₂} (γ≈ : _≈s_ (Γ .idx) γ₁ γ₂) {t₁ t₂ : Fα.Tδ.W ∣ P ∣ (λ i → inj₁ i)}
            (t≈ : Fα.Tδ.W-≈ t₁ t₂) → _≈s_ (A .idx) (h .idxf .PS._⇒_.func (γ₁ , t₁)) (Fα.fold-idx γ₂ t₂)
    η-idx {γ₁} {γ₂} γ≈ {Fα.Tδ.sup x₁} {Fα.Tδ.sup x₂} t≈ =
      A .idx .isEquivalence .trans
        (h .idxf .PS._⇒_.func-resp-≈
          (Γ .idx .isEquivalence .refl {γ₁} ,
           Fα.Tδ.W-≈-sym
             {x = Aα.αmor .idxf .PS._⇒_.func (shift P x₁)} {y = Fα.Tδ.sup x₁}
             (roundtrip x₁)))
        (A .idx .isEquivalence .trans
          (eq ._≃_.idxf-eq .PS._≃m_.func-eq (γ≈ , shift-resp P t≈))
          (alg .idxf .PS._⇒_.func-resp-≈ (Γ .idx .isEquivalence .refl {γ₂} , η-shape P γ₂ x₂)))

    -- h's strong action at the unembedded shift agrees with the fold's shape action.
    η-shape : (R : Poly (suc n)) (γ : Γ .idx .Carrier) (x : Fα.Tδ.⟦ ∣ R ∣ ⟧shape (Sh.η₀ ∣ P ∣)) →
              _≈s_ (fobj μObj R (extend δ A) .idx)
                   (strong-fmor R hs .idxf .PS._⇒_.func (γ , shift R x))
                   (Fα.fold-shape-idx R γ x)
    η-shape (const A') γ x = A' .idx .isEquivalence .refl
    η-shape (var Fin.zero) γ x = η-idx (Γ .idx .isEquivalence .refl {γ}) (Fα.Tδ.W-≈-refl x)
    η-shape (var (Fin.suc j)) γ x = δ j .idx .isEquivalence .refl
    η-shape (R₁ + R₂) γ (inj₁ x) = η-shape R₁ γ x
    η-shape (R₁ + R₂) γ (inj₂ y) = η-shape R₂ γ y
    η-shape (R₁ × R₂) γ (x , y) = η-shape R₁ γ x , η-shape R₂ γ y
    η-shape (μ Q') γ x =
      Fα.TA'.W-≈-trans
        {x = strong-fmor (μ Q') hs .idxf .PS._⇒_.func (γ , Rδ.reindex mor₀δ x)}
        {y = Rcomb.ireindex (cmb-hs γ) (Rδ.reindex mor₀δ x)}
        {z = Fα.fold-reindex {Q = Q'} γ Fα.fbase x}
        (Fα.TA'.W-≈-sym
          {x = Rcomb.ireindex (cmb-hs γ) (Rδ.reindex mor₀δ x)}
          {y = strong-fmor (μ Q') hs .idxf .PS._⇒_.func (γ , Rδ.reindex mor₀δ x)}
          (fuse-idx {n = suc n} {Γ = Γ} {sₛ = δ'} {sₜ = extend δ A} Q' cmb-hs hs corr-hs
            (Γ .idx .isEquivalence .refl {γ}) {Rδ.reindex mor₀δ x} {Rδ.reindex mor₀δ x}
            (μObj Q' δ' .idx .isEquivalence .refl {Rδ.reindex mor₀δ x})))
        (htele-shape (μ Q') hbase x)
      where
      mutual
        -- Telescope: reindexing by h after the context shift is the fold's reindex,  by the outer induction
        -- at the recursion slots.
        data HRel : ∀ {j} {ρD : Fin j → Fin n ⊎ Sort n} {ρX ρC : Fin j → Fin (suc n) ⊎ Sort (suc n)}
                    {dD : ∀ v → Fα.Tδ.DecoRes (ρD v)} {dX : ∀ v → Aα.TX.DecoRes (ρX v)}
                    {dC : ∀ v → Fα.TA'.DecoRes (ρC v)} →
                    Rδ.MorD ρD ρX dD dX → Rcomb.IMorD ρX ρC → Fα.FMor ρD ρC dD dC →
                    Set (o ⊔ m ⊔ e ⊔ lsuc os ⊔ lsuc es) where
          hbase : HRel mor₀δ (cmb-hs γ) Fα.fbase
          hbind : ∀ {j} {ρD ρX ρC dD dX dC} {md : Rδ.MorD {j} ρD ρX dD dX} {mdc : Rcomb.IMorD ρX ρC}
                  {fm : Fα.FMor ρD ρC dD dC} (S' : Poly (suc j)) → HRel md mdc fm →
                  HRel (Rδ.bind S' md) (Rcomb.ibind ∣ S' ∣ mdc) (Fα.fbind S' fm)

        htele-shape : ∀ {j} (S : Poly j) {ρD ρX ρC dD dX dC} {md : Rδ.MorD ρD ρX dD dX} {mdc : Rcomb.IMorD ρX ρC}
                      {fm : Fα.FMor ρD ρC dD dC} (rel : HRel md mdc fm) (z : Fα.Tδ.⟦ ∣ S ∣ ⟧shape ρD) →
                      Fα.TA'.shape≈ ∣ S ∣ ρC (Rcomb.ireindex-shape ∣ S ∣ mdc (Rδ.reindex-shape ∣ S ∣ md z))
                        (Fα.fold-reindex-shape γ S fm z)
        htele-shape (const A') rel z = A' .idx .isEquivalence .refl
        htele-shape (var v) rel z = htele-apply rel v
        htele-shape (S₁ + S₂) rel (inj₁ z) = htele-shape S₁ rel z
        htele-shape (S₁ + S₂) rel (inj₂ z) = htele-shape S₂ rel z
        htele-shape (S₁ × S₂) rel (z₁ , z₂) = htele-shape S₁ rel z₁ , htele-shape S₂ rel z₂
        htele-shape (μ S') rel (Fα.Tδ.sup z) = htele-shape S' (hbind S' rel) z

        htele-apply : ∀ {j} {ρD ρX ρC dD dX dC} {md : Rδ.MorD {j} ρD ρX dD dX} {mdc : Rcomb.IMorD ρX ρC}
                      {fm : Fα.FMor ρD ρC dD dC} (rel : HRel md mdc fm) (v : Fin j) {z} →
                      Fα.TA'.elEq (ρC v) (Rcomb.iapply mdc v (Rδ.apply md v z)) (Fα.fold-apply γ fm v z)
        htele-apply hbase Fin.zero {z} = η-idx (Γ .idx .isEquivalence .refl {γ}) (Fα.Tδ.W-≈-refl z)
        htele-apply hbase (Fin.suc i) {z} = δ i .idx .isEquivalence .refl
        htele-apply (hbind S' rel) Fin.zero {z} = htele-shape (μ S') rel z
        htele-apply (hbind S' rel) (Fin.suc v) = htele-apply rel v

  -- Fibre side, at a fixed γ: h's fibre action agrees with the fold's, transported
  -- along the pointwise index agreement.
  module EtaFam (γ : Γ .idx .Carrier) where
    module FR = FReindex {δA = δ'} {δB = extend δ A} (Γ .fam .fm γ)

    act-hs : FR.FAct (cmb-hs γ) (λ v → lift tt) (λ v → lift tt)
    act-hs = FR.abase (λ { Fin.zero a → h .famf ._⇒f_.transf (γ , a) ; (Fin.suc i) a → p₂ })

    corr-hs-fam : ∀ i {a} →
                  extend δ A i .fam .subst
                     (corr-hs i (Γ .idx .isEquivalence .refl) (δ' i .idx .isEquivalence .refl {a}))
                   ∘ FR.aapply act-hs i a ≈
                  hs i .famf ._⇒f_.transf (γ , a)
    corr-hs-fam Fin.zero {a} = ≈-trans (∘-cong (A .fam .refl*) ≈-refl) id-left
    corr-hs-fam (Fin.suc j) {a} = ≈-trans (∘-cong (δ j .fam .refl*) ≈-refl) id-left

    mutual
      η-fam : (t : Fα.Tδ.W ∣ P ∣ (λ i → inj₁ i)) →
              A .fam .subst (η-idx (Γ .idx .isEquivalence .refl {γ}) {t} {t} (Fα.Tδ.W-≈-refl t))
               ∘ h .famf ._⇒f_.transf (γ , t)
              ≈ Fα.fold-fam γ t
      η-fam (Fα.Tδ.sup x) =
        ≈-trans (∘-cong (A .fam .trans* q₂₃ q₁) ≈-refl)
          (≈-trans (assoc _ _ _)
            (≈-trans (∘-cong ≈-refl (≈-sym (h .famf ._⇒f_.natural
                                             (Γ .idx .isEquivalence .refl {γ} , rt⁻))))
              (≈-trans (∘-cong ≈-refl (∘-cong ≈-refl (prod-m-cong (Γ .fam .refl*) (shift-subst x))))
                (≈-trans (∘-cong ≈-refl (∘-cong ≈-refl pairT-intro))
                  (≈-trans (∘-cong ≈-refl (≈-sym (assoc _ _ _)))
                    (≈-trans (≈-sym (assoc _ _ _))
                      (≈-trans (∘-cong (∘-cong (A .fam .trans* q₃ q₂) ≈-refl) ≈-refl)
                        (≈-trans (∘-cong (assoc _ _ _) ≈-refl)
                          (≈-trans (∘-cong (∘-cong ≈-refl eq-step) ≈-refl)
                            (≈-trans (∘-cong (≈-trans (≈-sym (assoc _ _ _))
                                               (≈-trans (∘-cong (≈-sym (alg .famf ._⇒f_.natural
                                                                         (Γ .idx .isEquivalence .refl {γ} ,
                                                                          η-shape P γ x))) ≈-refl)
                                                 (assoc _ _ _))) ≈-refl)
                              (≈-trans (assoc _ _ _)
                                (∘-cong ≈-refl
                                  (≈-trans (∘-cong (pair-compose _ _ _ _) ≈-refl)
                                    (≈-trans (pair-natural _ _ _)
                                      (pair-cong
                                        (≈-trans (∘-cong (≈-trans (∘-cong (Γ .fam .refl*) ≈-refl) id-left) ≈-refl)
                                          (≈-trans (pair-p₁ _ _) id-left))
                                        (≈-trans (assoc _ _ _) (η-shape-fam P x)))))))))))))))))
        where
        rt⁻ = Fα.Tδ.W-≈-sym {x = Aα.αmor .idxf .PS._⇒_.func (shift P x)} {y = Fα.Tδ.sup x} (roundtrip x)
        q₁ = h .idxf .PS._⇒_.func-resp-≈ (Γ .idx .isEquivalence .refl {γ} , rt⁻)
        q₂ = eq ._≃_.idxf-eq .PS._≃m_.func-eq
               (Γ .idx .isEquivalence .refl {γ} , shift-resp P (Fα.Tδ.shape≈-refl ∣ P ∣ (Sh.η₀ ∣ P ∣) x))
        q₃ = alg .idxf .PS._⇒_.func-resp-≈ (Γ .idx .isEquivalence .refl {γ} , η-shape P γ x)
        q₂₃ = A .idx .isEquivalence .trans q₂ q₃

        eq-step : A .fam .subst q₂ ∘ (h .famf ._⇒f_.transf (γ , Aα.αmor .idxf .PS._⇒_.func (shift P x))
                                        ∘ pair p₁ (id _ ∘ (Aα.αmor .famf ._⇒f_.transf (shift P x) ∘ p₂))) ≈
                  alg .famf ._⇒f_.transf (γ , strong-fmor P hs .idxf .PS._⇒_.func (γ , shift P x))
                     ∘ pair p₁ (strong-fmor P hs .famf ._⇒f_.transf (γ , shift P x))
        eq-step =
          ≈-trans (∘-cong ≈-refl (≈-sym id-left))
            (≈-trans (eq ._≃_.famf-eq .indexed-family._≃f_.transf-eq {γ , shift P x}) id-left)

        pairT-intro : prod-m (id _) (Aα.αmor .famf ._⇒f_.transf (shift P x) ∘ shift-fam P x)
                      ≈ (pair p₁ (id _ ∘ (Aα.αmor .famf ._⇒f_.transf (shift P x) ∘ p₂))
                         ∘ prod-m (id _) (shift-fam P x))
        pairT-intro =
          ≈-sym (≈-trans (pair-natural _ _ _)
            (pair-cong (pair-p₁ _ _)
              (≈-trans (∘-cong id-left ≈-refl)
                (≈-trans (assoc _ _ _)
                  (≈-trans (∘-cong ≈-refl (pair-p₂ _ _)) (≈-sym (assoc _ _ _)))))))

      η-shape-fam : (R : Poly (suc n)) (x : Fα.Tδ.⟦ ∣ R ∣ ⟧shape (Sh.η₀ ∣ P ∣)) →
                    fobj μObj R (extend δ A) .fam .subst (η-shape R γ x)
                     ∘ (strong-fmor R hs .famf ._⇒f_.transf (γ , shift R x) ∘ prod-m (id _) (shift-fam R x)) ≈
                    Fα.fold-shape-fam R γ x
      η-shape-fam (const A') x =
        ≈-trans (∘-cong (A' .fam .refl*) ≈-refl)
          (≈-trans id-left (≈-trans (∘-cong ≈-refl (≈-trans (prod-m-cong ≈-refl id-left) prod-m-id)) id-right))
      η-shape-fam (var Fin.zero) x =
        ≈-trans (∘-cong ≈-refl (≈-trans (∘-cong ≈-refl (≈-trans (prod-m-cong ≈-refl id-left) prod-m-id)) id-right))
          (η-fam x)
      η-shape-fam (var (Fin.suc j)) x =
        ≈-trans (∘-cong (δ j .fam .refl*) ≈-refl)
          (≈-trans id-left (≈-trans (∘-cong ≈-refl (≈-trans (prod-m-cong ≈-refl id-left) prod-m-id)) id-right))
      η-shape-fam (R₁ + R₂) (inj₁ x) =
        ≈-trans (∘-cong ≈-refl (∘-cong (≈-trans id-left id-left) ≈-refl)) (η-shape-fam R₁ x)
      η-shape-fam (R₁ + R₂) (inj₂ y) =
        ≈-trans (∘-cong ≈-refl (∘-cong (≈-trans id-left id-left) ≈-refl)) (η-shape-fam R₂ y)
      η-shape-fam (R₁ × R₂) (x , y) =
        ≈-trans (∘-cong ≈-refl
                   (∘-cong (pair-cong (≈-trans id-left (∘-cong ≈-refl (pair-cong ≈-refl id-left)))
                                      (≈-trans id-left (∘-cong ≈-refl (pair-cong ≈-refl id-left))))
                           (prod-m-cong ≈-refl (≈-sym (prod-m-comp _ _ _ _)))))
          (≈-trans (∘-cong ≈-refl (strong-prod-m-pre _ _ _ _ _))
            (≈-trans (strong-prod-m-post _ _ _ _)
              (strong-prod-m-cong (η-shape-fam R₁ x) (η-shape-fam R₂ y))))
      η-shape-fam (μ Q') x =
        ≈-trans (∘-cong (Fα.TA'.fib-trans* Q' _
                           {x = strong-fmor (μ Q') hs .idxf .PS._⇒_.func (γ , m')}
                           {y = Rcomb.ireindex (cmb-hs γ) m'}
                           {z = Fα.fold-reindex {Q = Q'} γ Fα.fbase x}
                           (htele-shape' (μ Q') hbase' x)
                           sym-fuse) ≈-refl)
          (≈-trans (assoc _ _ _)
            (≈-trans (∘-cong ≈-refl
                       (≈-trans (∘-cong ≈-refl (∘-cong ≈-refl (prod-m-cong ≈-refl id-left)))
                         (≈-trans (≈-sym (assoc _ _ _)) (∘-cong fuse-inv ≈-refl))))
              (htelef-shape (μ Q') hbase' x)))
        where
        m' = Rδ.reindex mor₀δ x
        fuse-pf = fuse-idx {n = suc n} {Γ = Γ} {sₛ = δ'} {sₜ = extend δ A} Q' cmb-hs hs corr-hs
                    (Γ .idx .isEquivalence .refl {γ}) {m'} {m'}
                    (μObj Q' δ' .idx .isEquivalence .refl {m'})
        sym-fuse = Fα.TA'.W-≈-sym
                     {x = Rcomb.ireindex (cmb-hs γ) m'}
                     {y = strong-fmor (μ Q') hs .idxf .PS._⇒_.func (γ , m')} fuse-pf

        fuse-inv : μObj Q' (extend δ A) .fam .subst
                      {x = strong-fmor (μ Q') hs .idxf .PS._⇒_.func (γ , m')}
                      {y = Rcomb.ireindex (cmb-hs γ) m'} sym-fuse
                    ∘ strong-fmor (μ Q') hs .famf ._⇒f_.transf (γ , m') ≈ FR.freindex-fam act-hs {m'}
        fuse-inv =
          ≈-trans (∘-cong ≈-refl (≈-sym (fuse-fam γ Q' cmb-hs act-hs hs corr-hs corr-hs-fam {m'})))
            (≈-trans (≈-sym (assoc _ _ _))
              (≈-trans (∘-cong (≈-trans (≈-sym (μObj Q' (extend δ A) .fam .trans*
                                                 {x = Rcomb.ireindex (cmb-hs γ) m'}
                                                 {y = strong-fmor (μ Q') hs .idxf .PS._⇒_.func (γ , m')}
                                                 {z = Rcomb.ireindex (cmb-hs γ) m'}
                                                 sym-fuse fuse-pf))
                                  (μObj Q' (extend δ A) .fam .refl* {Rcomb.ireindex (cmb-hs γ) m'})) ≈-refl)
                id-left))

        mutual
          -- Telescope with the fibre action carried alongside, mirroring the index telescope in η-shape's
          -- μ case clause by clause.
          data HRel' : ∀ {j} {ρD : Fin j → Fin n ⊎ Sort n} {ρX ρC : Fin j → Fin (suc n) ⊎ Sort (suc n)}
                       {dD : ∀ v → Fα.Tδ.DecoRes (ρD v)} {dX : ∀ v → Aα.TX.DecoRes (ρX v)}
                       {dC : ∀ v → Fα.TA'.DecoRes (ρC v)} →
                       Rδ.MorD ρD ρX dD dX → (mdc : Rcomb.IMorD ρX ρC) → Fα.FMor ρD ρC dD dC →
                       FR.FAct mdc dX dC → Set (o ⊔ m ⊔ e ⊔ lsuc os ⊔ lsuc es) where
            hbase' : HRel' mor₀δ (cmb-hs γ) Fα.fbase act-hs
            hbind' : ∀ {j} {ρD ρX ρC dD dX dC} {md : Rδ.MorD {j} ρD ρX dD dX} {mdc : Rcomb.IMorD ρX ρC}
                     {fm : Fα.FMor ρD ρC dD dC} {am : FR.FAct mdc dX dC} (S' : Poly (suc j)) →
                     HRel' md mdc fm am →
                     HRel' (Rδ.bind S' md) (Rcomb.ibind ∣ S' ∣ mdc) (Fα.fbind S' fm) (FR.abind S' mdc am)

          htele-shape' : ∀ {j} (S : Poly j) {ρD ρX ρC dD dX dC} {md : Rδ.MorD ρD ρX dD dX} {mdc : Rcomb.IMorD ρX ρC}
                         {fm : Fα.FMor ρD ρC dD dC} {am : FR.FAct mdc dX dC}
                         (rel : HRel' md mdc fm am) (z : Fα.Tδ.⟦ ∣ S ∣ ⟧shape ρD) →
                         Fα.TA'.shape≈ ∣ S ∣ ρC (Rcomb.ireindex-shape ∣ S ∣ mdc (Rδ.reindex-shape ∣ S ∣ md z))
                           (Fα.fold-reindex-shape γ S fm z)
          htele-shape' (const A') rel z = A' .idx .isEquivalence .refl
          htele-shape' (var v) rel z = htele-apply' rel v
          htele-shape' (S₁ + S₂) rel (inj₁ z) = htele-shape' S₁ rel z
          htele-shape' (S₁ + S₂) rel (inj₂ z) = htele-shape' S₂ rel z
          htele-shape' (S₁ × S₂) rel (z₁ , z₂) = htele-shape' S₁ rel z₁ , htele-shape' S₂ rel z₂
          htele-shape' (μ S') rel (Fα.Tδ.sup z) = htele-shape' S' (hbind' S' rel) z

          htele-apply' : ∀ {j} {ρD ρX ρC dD dX dC} {md : Rδ.MorD {j} ρD ρX dD dX} {mdc : Rcomb.IMorD ρX ρC}
                         {fm : Fα.FMor ρD ρC dD dC} {am : FR.FAct mdc dX dC}
                         (rel : HRel' md mdc fm am) (v : Fin j) {z} →
                         Fα.TA'.elEq (ρC v) (Rcomb.iapply mdc v (Rδ.apply md v z)) (Fα.fold-apply γ fm v z)
          htele-apply' hbase' Fin.zero {z} = η-idx (Γ .idx .isEquivalence .refl {γ}) (Fα.Tδ.W-≈-refl z)
          htele-apply' hbase' (Fin.suc i) {z} = δ i .idx .isEquivalence .refl
          htele-apply' (hbind' S' rel) Fin.zero {z} = htele-shape' (μ S') rel z
          htele-apply' (hbind' S' rel) (Fin.suc v) = htele-apply' rel v

          htelef-shape : ∀ {j} (S : Poly j) {ρD ρX ρC dD dX dC} {md : Rδ.MorD ρD ρX dD dX} {mdc : Rcomb.IMorD ρX ρC}
                         {fm : Fα.FMor ρD ρC dD dC} {am : FR.FAct mdc dX dC}
                         (rel : HRel' md mdc fm am) (z : Fα.Tδ.⟦ ∣ S ∣ ⟧shape ρD) →
                         Fα.TA'.fib-shape-subst S dC (htele-shape' S rel z)
                          ∘ (FR.freindex-shape-fam S am {Rδ.reindex-shape ∣ S ∣ md z}
                             ∘ prod-m (id _) (Rδ.reindex-fam S md {z})) ≈
                         Fα.fold-reindex-shape-fam γ S fm z
          htelef-shape (const A') rel z =
            ≈-trans (∘-cong (A' .fam .refl*) ≈-refl)
              (≈-trans id-left (≈-trans (pair-p₂ _ _) id-left))
          htelef-shape (var v) rel z = htelef-apply rel v
          htelef-shape (S₁ + S₂) rel (inj₁ z) = htelef-shape S₁ rel z
          htelef-shape (S₁ + S₂) rel (inj₂ z) = htelef-shape S₂ rel z
          htelef-shape (S₁ × S₂) rel (z₁ , z₂) =
            ≈-trans (∘-cong ≈-refl (strong-prod-m-pre _ _ _ _ _))
              (≈-trans (strong-prod-m-post _ _ _ _)
                (strong-prod-m-cong (htelef-shape S₁ rel z₁) (htelef-shape S₂ rel z₂)))
          htelef-shape (μ S') rel (Fα.Tδ.sup z) = htelef-shape S' (hbind' S' rel) z

          htelef-apply : ∀ {j} {ρD ρX ρC dD dX dC} {md : Rδ.MorD {j} ρD ρX dD dX} {mdc : Rcomb.IMorD ρX ρC}
                         {fm : Fα.FMor ρD ρC dD dC} {am : FR.FAct mdc dX dC}
                         (rel : HRel' md mdc fm am) (v : Fin j) {z} →
                         (Fα.TA'.fib-el-subst (ρC v) (dC v) (htele-apply' rel v {z})
                          ∘ (FR.aapply am v (Rδ.apply md v z) ∘ prod-m (id _) (Rδ.apply-fam md v z)))
                         ≈ Fα.fold-apply-fam γ fm v z
          htelef-apply hbase' Fin.zero {z} =
            ≈-trans (∘-cong ≈-refl (≈-trans (∘-cong ≈-refl prod-m-id) id-right)) (η-fam z)
          htelef-apply hbase' (Fin.suc i) {z} =
            ≈-trans (∘-cong (δ i .fam .refl*) ≈-refl)
              (≈-trans id-left (≈-trans (∘-cong ≈-refl prod-m-id) id-right))
          htelef-apply (hbind' S' rel) Fin.zero {z} = htelef-shape (μ S') rel z
          htelef-apply (hbind' S' rel) (Fin.suc v) = htelef-apply rel v

hasMuLaws : HasMuLaws hasMu
hasMuLaws .HasMuLaws.⦅⦆-β {P = P} alg ._≃_.idxf-eq .PS._≃m_.func-eq (γ≈ , m≈) =
  alg .idxf .PS._⇒_.func-resp-≈ (γ≈ , BetaDef.β-idx alg P γ≈ m≈)
hasMuLaws .HasMuLaws.⦅⦆-β {Γ = Γ} {P = P} {δ = δ} alg ._≃_.famf-eq .indexed-family._≃f_.transf-eq {γ , m} =
  ≈-trans (∘-cong ≈-refl id-left)
    (≈-trans (∘-cong ≈-refl (∘-cong ≈-refl (pair-cong ≈-refl id-left)))
      (≈-trans (∘-cong ≈-refl (assoc _ _ _))
        (≈-trans (∘-cong ≈-refl (∘-cong ≈-refl
                   (≈-trans (pair-natural _ _ _)
                     (pair-cong (pair-p₁ _ _) (∘-cong ≈-refl (pair-cong (≈-sym id-left) ≈-refl))))))
          (≈-trans (≈-sym (assoc _ _ _))
            (≈-trans (∘-cong (≈-sym (alg .famf ._⇒f_.natural
                                       (Γ .idx .isEquivalence .refl ,
                                        B.β-idx P (Γ .idx .isEquivalence .refl)
                                          (fobj μObj P B.δ' .idx .isEquivalence .refl)))) ≈-refl)
              (≈-trans (assoc _ _ _)
                (≈-trans (∘-cong ≈-refl (pair-compose _ _ _ _))
                  (≈-trans (∘-cong ≈-refl
                             (pair-cong (≈-trans (∘-cong (Γ .fam .refl*) ≈-refl) id-left) (B.β-fam P)))
                    (≈-sym id-left)))))))))
  where
    module B = BetaDef {P = P} {δ = δ} alg
hasMuLaws .HasMuLaws.⦅⦆-η {Γ = Γ} {P = P} {δ = δ} alg h eq ._≃_.idxf-eq .PS._≃m_.func-eq (γ≈ , t≈) =
  EtaDef.η-idx {P = P} {δ = δ} alg h eq γ≈ t≈
hasMuLaws .HasMuLaws.⦅⦆-η {Γ = Γ} {P = P} {δ = δ} alg h eq ._≃_.famf-eq .indexed-family._≃f_.transf-eq {γ , t} =
  EtaDef.EtaFam.η-fam {P = P} {δ = δ} alg h eq γ t
