{-# OPTIONS --prop --postfix-projections --safe #-}

------------------------------------------------------------------------------
-- Free-family fusion: a single index-only reindex along a pointwise family
-- equals the strong functorial action of the family, on indices (fuse-idx) and
-- fibres (fuse-fam). The workhorse naturality lemma for the nested-μ cases of
-- both initial-algebra laws.
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
open import indexed-family using (_⇒f_)
import fam-mu-types.in-map

import functor
module fam-mu-types.reindex-fusion {o m e} (os es : Level) {𝒞 : Category o m e}
    (T : HasTerminal 𝒞) (P : HasProducts 𝒞) (𝕃 : functor.StrongFunctor P) where

open fam-mu-types.in-map os es T P 𝕃 public

-- General free-family fusion: a single reindex (the collapsed double-reindex, via combine-lemma)
-- equals the functorial map. Families sₛ/sₜ are FREE so the nested-μ recursion's family fits.
fuse-idx : ∀ {n} {Γ : Obj} {sₛ sₜ : Fin n → Obj} (Q : Poly (suc n)) →
               let module Rs = Reindex sₛ sₜ in
               (cmb : Γ .idx .Carrier → Rs.IMorD (λ v → inj₁ v) (λ v → inj₁ v))
               (fsk : ∀ i → Mor (Fam𝒞-P.prod Γ (sₛ i)) (sₜ i))
               (corr : ∀ i {γ₁ γ₂} (γ≈ : _≈s_ (Γ .idx) γ₁ γ₂) {a₁ a₂} (a≈ : _≈s_ (sₛ i .idx) a₁ a₂) →
                       _≈s_ (sₜ i .idx) (Rs.iapply (cmb γ₁) i a₁) (fsk i .idxf .PS._⇒_.func (γ₂ , a₂))) →
               ∀ {γ₁ γ₂} (γ≈ : _≈s_ (Γ .idx) γ₁ γ₂) {m₁ m₂}
               (m≈ : _≈s_ (μObj Q sₛ .idx) m₁ m₂) →
               _≈s_ (μObj Q sₜ .idx) (Rs.ireindex (cmb γ₁) m₁) (HasMu.strong-fmor hasMu (μ Q) fsk .idxf .PS._⇒_.func (γ₂ , m₂))
fuse-shape : ∀ {n} {Γ : Obj} {sₛ sₜ : Fin n → Obj} (Q : Poly (suc n)) →
                 let module Rs = Reindex sₛ sₜ
                     module Ts = Tree sₛ
                     module Tt = Tree sₜ
                     module At = InMapDef Q sₜ in
                 (cmb : Γ .idx .Carrier → Rs.IMorD (λ v → inj₁ v) (λ v → inj₁ v))
                 (fsk : ∀ i → Mor (Fam𝒞-P.prod Γ (sₛ i)) (sₜ i))
                 (corr : ∀ i {γ₁ γ₂} (γ≈ : _≈s_ (Γ .idx) γ₁ γ₂) {a₁ a₂} (a≈ : _≈s_ (sₛ i .idx) a₁ a₂) →
                         _≈s_ (sₜ i .idx) (Rs.iapply (cmb γ₁) i a₁) (fsk i .idxf .PS._⇒_.func (γ₂ , a₂))) →
                 let module Ft = FoldDef {Γ = Γ} {A = μObj Q sₜ} {P = Q} {δ = sₛ}
                                   (Mor-∘ At.inMor (HasMu.strong-fmor hasMu Q (HasMu.strong-extend-mor hasMu fsk Fam𝒞-P.p₂))) in
                 (R : Poly (suc n)) →
                 ∀ {γ₁ γ₂} (γ≈ : _≈s_ (Γ .idx) γ₁ γ₂) {x₁ x₂}
                 (x≈ : Ts.shape≈ ∣ R ∣ (Sh.η₀ ∣ Q ∣) x₁ x₂) →
                 Tt.shape≈ ∣ R ∣ (Sh.η₀ ∣ Q ∣)
                   (Rs.ireindex-shape ∣ R ∣ (Rs.ibind ∣ Q ∣ (cmb γ₁)) x₁)
                   (At.R.reindex-shape ∣ R ∣ At.mor₀
                    (At.embed-idx R (HasMu.strong-fmor hasMu R (HasMu.strong-extend-mor hasMu fsk Fam𝒞-P.p₂) .idxf .PS._⇒_.func
                      (γ₂ , Ft.fold-shape-idx R γ₂ x₂))))

fuse-idx Q cmb fsk corr γ≈ {Tree.sup x₁} {Tree.sup x₂} m≈ = fuse-shape Q cmb fsk corr Q γ≈ {x₁} {x₂} m≈

fuse-shape Q cmb fsk corr (const A')                  γ≈ x≈ = x≈
fuse-shape Q cmb fsk corr (var Fin.zero)              γ≈ {x₁} {x₂} x≈ = fuse-idx Q cmb fsk corr γ≈ {x₁} {x₂} x≈
fuse-shape Q cmb fsk corr (var (Fin.suc i))           γ≈ x≈ = corr i γ≈ x≈
fuse-shape Q cmb fsk corr (R₁ + R₂) γ≈ {inj₁ _} {inj₁ _} x≈ = fuse-shape Q cmb fsk corr R₁ γ≈ x≈
fuse-shape Q cmb fsk corr (R₁ + R₂) γ≈ {inj₂ _} {inj₂ _} x≈ = fuse-shape Q cmb fsk corr R₂ γ≈ x≈
fuse-shape Q cmb fsk corr (R₁ × R₂) γ≈ {_ , _} {_ , _} (x≈₁ , x≈₂) =
  fuse-shape Q cmb fsk corr R₁ γ≈ x≈₁ , fuse-shape Q cmb fsk corr R₂ γ≈ x≈₂
fuse-shape {Γ = Γ} {sₛ = sₛ} {sₜ = sₜ} Q cmb fsk corr (μ R'') {γ₁} {γ₂} γ≈ {x₁} {x₂} x≈ =
  Tt.W-≈-trans {x = Rs.ireindex-shape ∣ μ R'' ∣ (Rs.ibind ∣ Q ∣ (cmb γ₁)) x₁}
               {z = At.R.reindex-shape ∣ μ R'' ∣ At.mor₀ (At.embed-idx (μ R'')
                      (HasMu.strong-fmor hasMu (μ R'') (HasMu.strong-extend-mor hasMu fsk Fam𝒞-P.p₂)
                        .idxf .PS._⇒_.func (γ₂ , w)))}
               telescope
               (At.R.reindex-resp At.mor₀
                 {t = Rs'.ireindex (cmb' γ₁) wm₁}
                 {t' = HasMu.strong-fmor hasMu (μ R'') (HasMu.strong-extend-mor hasMu fsk Fam𝒞-P.p₂) .idxf .PS._⇒_.func (γ₂ , w)}
                 rec)
  where
    module Tt = Tree sₜ
    module Ts = Tree sₛ
    module At = InMapDef Q sₜ
    module Rs = Reindex sₛ sₜ
    module Rs' = Reindex (extend sₛ (μObj Q sₜ)) (extend sₜ (μObj Q sₜ))
    module Ft = FoldDef {Γ = Γ} {A = μObj Q sₜ} {P = Q} {δ = sₛ}
                  (Mor-∘ At.inMor (HasMu.strong-fmor hasMu Q (HasMu.strong-extend-mor hasMu fsk Fam𝒞-P.p₂)))
    wm₁ = Ft.fold-reindex {Q = R''} γ₁ Ft.fbase x₁
    w   = Ft.fold-reindex {Q = R''} γ₂ Ft.fbase x₂
    cmb' : Γ .idx .Carrier → Rs'.IMorD (λ v → inj₁ v) (λ v → inj₁ v)
    cmb' γ = Rs'.ibase (λ { Fin.zero a → a ; (Fin.suc i) a → Rs.iapply (cmb γ) i a })
                       (λ { Fin.zero p → p ; (Fin.suc i) p → Rs.iapply-resp (cmb γ) i p })
    rec : _≈s_ (μObj R'' (extend sₜ (μObj Q sₜ)) .idx)
               (Rs'.ireindex (cmb' γ₁) wm₁)
               (HasMu.strong-fmor hasMu (μ R'') (HasMu.strong-extend-mor hasMu fsk Fam𝒞-P.p₂) .idxf .PS._⇒_.func (γ₂ , w))
    rec = fuse-idx R'' cmb' (HasMu.strong-extend-mor hasMu fsk Fam𝒞-P.p₂)
            (λ { Fin.zero γ≈ a≈ → a≈ ; (Fin.suc j) γ≈ a≈ → corr j γ≈ a≈ })
            γ≈ {m₁ = wm₁} {m₂ = w}  (Ft.fold-reindex-resp {Q = R''} γ≈ Ft.fbase {x₁} {x₂} x≈)
    mutual
      data TeleRel : ∀ {j} {ηA ηB ηC ηD}
                     {dA : ∀ v → Ts.DecoAssign (ηA v)} {dB : ∀ v → Tt.DecoAssign (ηB v)}
                     {dC : ∀ v → At.TX.DecoAssign (ηC v)} {dD : ∀ v → Ft.TA'.DecoAssign (ηD v)} →
                     Rs.IMorD {j} ηA ηB → At.R.MorD {j} ηC ηB dC dB → Rs'.IMorD {j} ηD ηC → Ft.FMor {j} ηA ηD dA dD →
                     Set (o ⊔ m ⊔ e ⊔ lsuc os ⊔ lsuc es) where
        tbase : TeleRel (Rs.ibind ∣ Q ∣ (cmb γ₁)) At.mor₀ (cmb' γ₁) Ft.fbase
        tbind : ∀ {j} {ηA ηB ηC ηD} {dA dB dC dD} {md mdA md' fm} (S' : Poly (suc j)) →
                TeleRel {j} {ηA} {ηB} {ηC} {ηD} {dA} {dB} {dC} {dD} md mdA md' fm →
                TeleRel (Rs.ibind ∣ S' ∣ md) (At.R.bind S' mdA) (Rs'.ibind ∣ S' ∣ md') (Ft.fbind S' fm)

      tele-shape : ∀ {j} (S : Poly j) {ηA ηB ηC ηD} {dA dB dC dD}
                   {md : Rs.IMorD ηA ηB} {mdA : At.R.MorD ηC ηB dC dB} {md' : Rs'.IMorD ηD ηC} {fm : Ft.FMor ηA ηD dA dD}
                   (rel : TeleRel md mdA md' fm) (z : Ft.Tδ.⟦ ∣ S ∣ ⟧shape ηA) →
                   Tt.shape≈ ∣ S ∣ ηB
                     (Rs.ireindex-shape ∣ S ∣ md z)
                     (At.R.reindex-shape ∣ S ∣ mdA (Rs'.ireindex-shape ∣ S ∣ md' (Ft.fold-reindex-shape γ₁ S fm z)))
      tele-shape (const A') rel z = A' .idx .isEquivalence .refl
      tele-shape (var v) rel z = tele-apply rel v
      tele-shape (S₁ + S₂) rel (inj₁ z) = tele-shape S₁ rel z
      tele-shape (S₁ + S₂) rel (inj₂ z) = tele-shape S₂ rel z
      tele-shape (S₁ × S₂) rel (z₁ , z₂) = tele-shape S₁ rel z₁ , tele-shape S₂ rel z₂
      tele-shape (μ S') rel (Ts.sup z') = tele-shape S' (tbind S' rel) z'

      tele-apply : ∀ {j} {ηA ηB ηC ηD} {dA dB dC dD}
                   {md : Rs.IMorD ηA ηB} {mdA : At.R.MorD ηC ηB dC dB} {md' : Rs'.IMorD ηD ηC} {fm : Ft.FMor ηA ηD dA dD}
                   (rel : TeleRel md mdA md' fm) (v : Fin j) {z} →
                   Tt.elEq (ηB v) (Rs.iapply md v z) (At.R.apply mdA v (Rs'.iapply md' v (Ft.fold-apply γ₁ fm v z)))
      tele-apply (tbind S' r) Fin.zero    {z} = tele-shape (μ S') r z
      tele-apply (tbind S' r) (Fin.suc v)     = tele-apply r v
      tele-apply tbase Fin.zero    {z} =
        fuse-idx Q cmb fsk corr (Γ .idx .isEquivalence .refl {γ₁}) {m₁ = z} {m₂ = z}
          (μObj Q sₛ .idx .isEquivalence .refl {z})
      tele-apply tbase (Fin.suc i) {z} = Tt.elEq-refl (inj₁ i) (Rs.iapply (cmb γ₁) i z)

    telescope : Tt.W-≈ (Rs.ireindex-shape ∣ μ R'' ∣ (Rs.ibind ∣ Q ∣ (cmb γ₁)) x₁)
                       (At.R.reindex At.mor₀ (Rs'.ireindex (cmb' γ₁) wm₁))
    telescope = tele-shape (μ R'') tbase x₁

-- Fibre analogue of `fuse-idx`: the fibre reindex (via the external fold action `act`) equals the strong
-- functorial action's fibre, transported along the index fusion. Mirrors `fuse-idx`'s interface so the
-- μ-recursion can build nested index equations, plus the fibre `act`/`corr-fam` (at the fixed `γ`).
fuse-fam : ∀ {n} {Γ : Obj} (γ : Γ .idx .Carrier) {sₛ sₜ : Fin n → Obj} (Q : Poly (suc n)) →
               let module Rs = Reindex sₛ sₜ
                   module FR = FReindex {δA = sₛ} {δB = sₜ} (Γ .fam .fm γ) in
               (cmb : Γ .idx .Carrier → Rs.IMorD (λ v → inj₁ v) (λ v → inj₁ v))
               (act : FR.FAct (cmb γ) (λ v → lift tt) (λ v → lift tt))
               (fsk : ∀ i → Mor (Fam𝒞-P.prod Γ (sₛ i)) (sₜ i))
               (corr : ∀ i {γ₁ γ₂} (γ≈ : _≈s_ (Γ .idx) γ₁ γ₂) {a₁ a₂} (a≈ : _≈s_ (sₛ i .idx) a₁ a₂) →
                       _≈s_ (sₜ i .idx) (Rs.iapply (cmb γ₁) i a₁) (fsk i .idxf .PS._⇒_.func (γ₂ , a₂)))
               (corr-fam : ∀ i {a} →
                  Category._≈_ 𝒞
                    (sₜ i .fam .subst (corr i (Γ .idx .isEquivalence .refl) (sₛ i .idx .isEquivalence .refl {a}))
                     ∘ FR.aapply act i a)
                    (fsk i .famf ._⇒f_.transf (γ , a))) →
               ∀ {m} →
               Category._≈_ 𝒞
                 (μObj Q sₜ .fam .subst {x = Rs.ireindex (cmb γ) m}
                    (fuse-idx Q cmb fsk corr (Γ .idx .isEquivalence .refl)
                      {m} {m} (μObj Q sₛ .idx .isEquivalence .refl {m}))
                  ∘ FR.freindex-fam act {m})
                 (HasMu.strong-fmor hasMu (μ Q) fsk .famf ._⇒f_.transf (γ , m))

-- Shape-level recursion for `fuse-fam` (mirrors `fuse-shape`): the fibre reindex of
-- the μ-body sub-poly `R` equals the embed ∘ reindex ∘ strong ∘ fold fibre composite.
fuse-shape-fam : ∀ {n} {Γ : Obj} (γ : Γ .idx .Carrier) {sₛ sₜ : Fin n → Obj} (Q : Poly (suc n)) →
                     let module Rs = Reindex sₛ sₜ
                         module Ts = Tree sₛ
                         module Tt = Tree sₜ
                         module At = InMapDef Q sₜ
                         module FR = FReindex {δA = sₛ} {δB = sₜ} (Γ .fam .fm γ) in
                     (cmb : Γ .idx .Carrier → Rs.IMorD (λ v → inj₁ v) (λ v → inj₁ v))
                     (act : FR.FAct (cmb γ) (λ v → lift tt) (λ v → lift tt))
                     (fsk : ∀ i → Mor (Fam𝒞-P.prod Γ (sₛ i)) (sₜ i))
                     (corr : ∀ i {γ₁ γ₂} (γ≈ : _≈s_ (Γ .idx) γ₁ γ₂) {a₁ a₂} (a≈ : _≈s_ (sₛ i .idx) a₁ a₂) →
                             _≈s_ (sₜ i .idx) (Rs.iapply (cmb γ₁) i a₁) (fsk i .idxf .PS._⇒_.func (γ₂ , a₂)))
                     (corr-fam : ∀ i {a} →
                        Category._≈_ 𝒞
                          (sₜ i .fam .subst (corr i (Γ .idx .isEquivalence .refl) (sₛ i .idx .isEquivalence .refl {a}))
                           ∘ FR.aapply act i a)
                          (fsk i .famf ._⇒f_.transf (γ , a))) →
                     let module Ft = FoldDef {Γ = Γ} {A = μObj Q sₜ} {P = Q} {δ = sₛ}
                                       (Mor-∘ At.inMor (HasMu.strong-fmor hasMu Q (HasMu.strong-extend-mor hasMu fsk Fam𝒞-P.p₂)))
                         fsk' = HasMu.strong-extend-mor hasMu fsk Fam𝒞-P.p₂ in
                     (R : Poly (suc n))
                     {x : Ts.⟦ ∣ R ∣ ⟧shape (Sh.η₀ ∣ Q ∣)} →
                     Category._≈_ 𝒞
                       (Tt.fib-shape-subst R (Tt.deco-ext Q (λ i → lift tt))
                          (fuse-shape Q cmb fsk corr R (Γ .idx .isEquivalence .refl) (Ts.shape≈-refl ∣ R ∣ (Sh.η₀ ∣ Q ∣) x))
                        ∘ FR.freindex-shape-fam R (FR.abind Q (cmb γ) act) {x})
                       (At.R.reindex-fam R At.mor₀
                        ∘ (At.embed-fam R (HasMu.strong-fmor hasMu R fsk' .idxf .PS._⇒_.func (γ , Ft.fold-shape-idx R γ x))
                           ∘ (HasMu.strong-fmor hasMu R fsk' .famf ._⇒f_.transf (γ , Ft.fold-shape-idx R γ x)
                              ∘ pair p₁ (Ft.fold-shape-fam R γ x))))

fuse-fam γ Q cmb act fsk corr corr-fam {Tree.sup x} =
  ≈-trans (fuse-shape-fam γ Q cmb act fsk corr corr-fam Q {x})
    (≈-sym (≈-trans (∘-cong id-left ≈-refl) (≈-trans (assoc _ _ _) (assoc _ _ _))))
fuse-shape-fam γ Q cmb act fsk corr corr-fam (const A') =
  ≈-trans (∘-cong (A' .fam .refl*) ≈-refl)
    (≈-trans id-left (≈-sym (≈-trans id-left (≈-trans id-left (pair-p₂ _ _)))))
fuse-shape-fam γ Q cmb act fsk corr corr-fam (var Fin.zero) {x} =
  ≈-trans (fuse-fam γ Q cmb act fsk corr corr-fam {x})
    (≈-sym (≈-trans id-left (≈-trans id-left (pair-p₂ _ _))))
fuse-shape-fam γ Q cmb act fsk corr corr-fam (var (Fin.suc i)) {x} =
  ≈-trans (corr-fam i)
    (≈-sym (≈-trans id-left (≈-trans id-left (≈-trans (∘-cong ≈-refl pair-ext0) id-right))))
fuse-shape-fam γ Q cmb act fsk corr corr-fam (R₁ + R₂) {inj₁ a} =
  ≈-trans (fuse-shape-fam γ Q cmb act fsk corr corr-fam R₁ {a})
    (∘-cong ≈-refl (∘-cong ≈-refl (∘-cong (≈-sym (≈-trans id-left id-left)) ≈-refl)))
fuse-shape-fam γ Q cmb act fsk corr corr-fam (R₁ + R₂) {inj₂ b} =
  ≈-trans (fuse-shape-fam γ Q cmb act fsk corr corr-fam R₂ {b})
    (∘-cong ≈-refl (∘-cong ≈-refl (∘-cong (≈-sym (≈-trans id-left id-left)) ≈-refl)))
fuse-shape-fam γ Q cmb act fsk corr corr-fam (R₁ × R₂) {a , b} =
  ≈-trans (pair-compose _ _ _ _)
    (≈-trans (pair-cong
               (≈-trans (≈-sym (assoc _ _ _))
                 (≈-trans (∘-cong (fuse-shape-fam γ Q cmb act fsk corr corr-fam R₁ {a}) ≈-refl)
                   (≈-trans (assoc _ _ _)
                     (∘-cong ≈-refl
                       (≈-trans (assoc _ _ _)
                         (∘-cong ≈-refl
                           (≈-trans (assoc _ _ _)
                             (≈-trans (∘-cong ≈-refl (≈-trans (pair-natural _ _ _) (pair-cong (pair-p₁ _ _) ≈-refl)))
                               (≈-sym
                                 (≈-trans (∘-cong id-left ≈-refl)
                                   (≈-trans (assoc _ _ _)
                                     (∘-cong ≈-refl
                                       (≈-trans (pair-natural _ _ _)
                                         (pair-cong (pair-p₁ _ _)
                                           (≈-trans (∘-cong id-left ≈-refl)
                                             (≈-trans (assoc _ _ _)
                                               (≈-trans (∘-cong ≈-refl (pair-p₂ _ _)) (pair-p₁ _ _))))))))))))))))))
               (≈-trans (≈-sym (assoc _ _ _))
                 (≈-trans (∘-cong (fuse-shape-fam γ Q cmb act fsk corr corr-fam R₂ {b}) ≈-refl)
                   (≈-trans (assoc _ _ _)
                     (∘-cong ≈-refl
                       (≈-trans (assoc _ _ _)
                         (∘-cong ≈-refl
                           (≈-trans (assoc _ _ _)
                             (≈-trans (∘-cong ≈-refl (≈-trans (pair-natural _ _ _) (pair-cong (pair-p₁ _ _) ≈-refl)))
                               (≈-sym
                                 (≈-trans (∘-cong id-left ≈-refl)
                                   (≈-trans (assoc _ _ _)
                                     (∘-cong ≈-refl
                                       (≈-trans (pair-natural _ _ _)
                                         (pair-cong (pair-p₁ _ _)
                                           (≈-trans (∘-cong id-left ≈-refl)
                                             (≈-trans (assoc _ _ _)
                                               (≈-trans (∘-cong ≈-refl (pair-p₂ _ _)) (pair-p₂ _ _)))))))))))))))))))
      (≈-sym (≈-trans (∘-cong ≈-refl (∘-cong ≈-refl (pair-natural _ _ _)))
                (≈-trans (∘-cong ≈-refl (pair-compose _ _ _ _))
                  (pair-compose _ _ _ _)))))
fuse-shape-fam {Γ = Γ} γ {sₛ = sₛ} {sₜ = sₜ} Q cmb act fsk corr corr-fam (μ R'') {x} =
  ≈-trans (∘-cong (Tt.fib-trans* R'' (Tt.deco-ext Q (λ i → lift tt))
                     {x = Rs.ireindex-shape ∣ μ R'' ∣ (Rs.ibind ∣ Q ∣ (cmb γ)) x}
                     {y = At.R.reindex At.mor₀ (Rs'.ireindex (cmb' γ) wm₁)}
                     {z = At.R.reindex At.mor₀ (HasMu.strong-fmor hasMu (μ R'') fsk' .idxf .PS._⇒_.func (γ , wm₁))}
                     (At.R.reindex-resp At.mor₀
                        {t = Rs'.ireindex (cmb' γ) wm₁}
                        {t' = HasMu.strong-fmor hasMu (μ R'') fsk' .idxf .PS._⇒_.func (γ , wm₁)}
                        rec-idx)
                     (tele-shape (μ R'') tbase x)) ≈-refl)
    (≈-trans (assoc _ _ _)
      (≈-trans (∘-cong ≈-refl (tele-shape-fam (μ R'') tbase x))
        (≈-trans (≈-sym (assoc _ _ _))
          (≈-trans (∘-cong (≈-sym (At.R.reindex-fam-W-natural {Q = R''} At.mor₀
                                     {t = Rs'.ireindex (cmb' γ) wm₁}
                                     {t' = HasMu.strong-fmor hasMu (μ R'') fsk' .idxf .PS._⇒_.func (γ , wm₁)}
                                     rec-idx)) ≈-refl)
            (≈-trans (assoc _ _ _)
              (∘-cong ≈-refl
                (≈-trans (≈-sym (assoc _ _ _))
                  (≈-trans (∘-cong rec-fam ≈-refl) (≈-sym id-left)))))))))
  where
    module Tt = Tree sₜ
    module Ts = Tree sₛ
    module At = InMapDef Q sₜ
    module Rs = Reindex sₛ sₜ
    module Rs' = Reindex (extend sₛ (μObj Q sₜ)) (extend sₜ (μObj Q sₜ))
    module FR = FReindex {δA = sₛ} {δB = sₜ} (Γ .fam .fm γ)
    module FR' = FReindex {δA = extend sₛ (μObj Q sₜ)} {δB = extend sₜ (μObj Q sₜ)} (Γ .fam .fm γ)
    module Ft = FoldDef {Γ = Γ} {A = μObj Q sₜ} {P = Q} {δ = sₛ}
                  (Mor-∘ At.inMor (HasMu.strong-fmor hasMu Q (HasMu.strong-extend-mor hasMu fsk Fam𝒞-P.p₂)))
    fsk' = HasMu.strong-extend-mor hasMu fsk Fam𝒞-P.p₂
    wm₁ = Ft.fold-reindex {Q = R''} γ Ft.fbase x
    cmb' : Γ .idx .Carrier → Rs'.IMorD (λ v → inj₁ v) (λ v → inj₁ v)
    cmb' γ' = Rs'.ibase (λ { Fin.zero a → a ; (Fin.suc i) a → Rs.iapply (cmb γ') i a })
                        (λ { Fin.zero p → p ; (Fin.suc i) p → Rs.iapply-resp (cmb γ') i p })
    act' : FR'.FAct (cmb' γ) (λ v → lift tt) (λ v → lift tt)
    act' = FR'.abase (λ { Fin.zero a → p₂ ; (Fin.suc i) a → FR.aapply act i a })
    corr' : ∀ i {γ₁ γ₂} (γ≈ : _≈s_ (Γ .idx) γ₁ γ₂) {a₁ a₂} (a≈ : _≈s_ (extend sₛ (μObj Q sₜ) i .idx) a₁ a₂) →
            _≈s_ (extend sₜ (μObj Q sₜ) i .idx) (Rs'.iapply (cmb' γ₁) i a₁) (fsk' i .idxf .PS._⇒_.func (γ₂ , a₂))
    corr' Fin.zero    γ≈ a≈ = a≈
    corr' (Fin.suc j) γ≈ a≈ = corr j γ≈ a≈
    corr-fam' : ∀ i {a} → Category._≈_ 𝒞
                  (extend sₜ (μObj Q sₜ) i .fam .subst
                     (corr' i (Γ .idx .isEquivalence .refl) (extend sₛ (μObj Q sₜ) i .idx .isEquivalence .refl {a}))
                   ∘ FR'.aapply act' i a)
                  (fsk' i .famf ._⇒f_.transf (γ , a))
    corr-fam' Fin.zero {a} = ≈-trans (∘-cong (μObj Q sₜ .fam .refl* {a}) ≈-refl) id-left
    corr-fam' (Fin.suc j) = corr-fam j
    rec-fam : Category._≈_ 𝒞
                (μObj R'' (extend sₜ (μObj Q sₜ)) .fam .subst {x = Rs'.ireindex (cmb' γ) wm₁}
                   (fuse-idx R'' cmb' fsk' corr' (Γ .idx .isEquivalence .refl)
                     {wm₁} {wm₁} (μObj R'' (extend sₛ (μObj Q sₜ)) .idx .isEquivalence .refl {wm₁}))
                 ∘ FR'.freindex-fam act' {wm₁})
                (HasMu.strong-fmor hasMu (μ R'') fsk' .famf ._⇒f_.transf (γ , wm₁))
    rec-fam = fuse-fam γ R'' cmb' act' fsk' corr' corr-fam' {wm₁}
    rec-idx = fuse-idx R'' cmb' fsk' corr' (Γ .idx .isEquivalence .refl)
                {wm₁} {wm₁} (μObj R'' (extend sₛ (μObj Q sₜ)) .idx .isEquivalence .refl {wm₁})
    mutual
      data TeleRel : ∀ {j} {ηA ηB ηC ηD}
                     {dA : ∀ v → Ts.DecoAssign (ηA v)} {dB : ∀ v → Tt.DecoAssign (ηB v)}
                     {dC : ∀ v → At.TX.DecoAssign (ηC v)} {dD : ∀ v → Ft.TA'.DecoAssign (ηD v)}
                     (md : Rs.IMorD {j} ηA ηB) (mdA : At.R.MorD {j} ηC ηB dC dB) (md' : Rs'.IMorD {j} ηD ηC) (fm : Ft.FMor {j} ηA ηD dA dD) →
                     FR.FAct md dA dB → FR'.FAct md' dD dC → Set (o ⊔ m ⊔ e ⊔ lsuc os ⊔ lsuc es) where
        tbase : TeleRel (Rs.ibind ∣ Q ∣ (cmb γ)) At.mor₀ (cmb' γ) Ft.fbase (FR.abind Q (cmb γ) act) act'
        tbind : ∀ {j} {ηA ηB ηC ηD} {dA dB dC dD} {md : Rs.IMorD ηA ηB} {mdA : At.R.MorD ηC ηB dC dB} {md' : Rs'.IMorD ηD ηC} {fm : Ft.FMor ηA ηD dA dD}
                {am : FR.FAct md dA dB} {am' : FR'.FAct md' dD dC} (S' : Poly (suc j)) →
                TeleRel md mdA md' fm am am' →
                TeleRel (Rs.ibind ∣ S' ∣ md) (At.R.bind S' mdA) (Rs'.ibind ∣ S' ∣ md') (Ft.fbind S' fm)
                        (FR.abind S' md am) (FR'.abind S' md' am')

      tele-shape : ∀ {j} (S : Poly j) {ηA ηB ηC ηD} {dA dB dC dD}
                   {md : Rs.IMorD ηA ηB} {mdA : At.R.MorD ηC ηB dC dB} {md' : Rs'.IMorD ηD ηC} {fm : Ft.FMor ηA ηD dA dD}
                   {am : FR.FAct md dA dB} {am' : FR'.FAct md' dD dC}
                   (rel : TeleRel md mdA md' fm am am') (z : Ft.Tδ.⟦ ∣ S ∣ ⟧shape ηA) →
                   Tt.shape≈ ∣ S ∣ ηB
                     (Rs.ireindex-shape ∣ S ∣ md z)
                     (At.R.reindex-shape ∣ S ∣ mdA (Rs'.ireindex-shape ∣ S ∣ md' (Ft.fold-reindex-shape γ S fm z)))
      tele-shape (const A') rel z = A' .idx .isEquivalence .refl
      tele-shape (var v) rel z = tele-apply rel v
      tele-shape (S₁ + S₂) rel (inj₁ z) = tele-shape S₁ rel z
      tele-shape (S₁ + S₂) rel (inj₂ z) = tele-shape S₂ rel z
      tele-shape (S₁ × S₂) rel (z₁ , z₂) = tele-shape S₁ rel z₁ , tele-shape S₂ rel z₂
      tele-shape (μ S') rel (Ts.sup z') = tele-shape S' (tbind S' rel) z'

      tele-apply : ∀ {j} {ηA ηB ηC ηD} {dA dB dC dD}
                   {md : Rs.IMorD ηA ηB} {mdA : At.R.MorD ηC ηB dC dB} {md' : Rs'.IMorD ηD ηC} {fm : Ft.FMor ηA ηD dA dD}
                   {am : FR.FAct md dA dB} {am' : FR'.FAct md' dD dC}
                   (rel : TeleRel md mdA md' fm am am') (v : Fin j) {z} →
                   Tt.elEq (ηB v) (Rs.iapply md v z) (At.R.apply mdA v (Rs'.iapply md' v (Ft.fold-apply γ fm v z)))
      tele-apply (tbind S' r) Fin.zero    {z} = tele-shape (μ S') r z
      tele-apply (tbind S' r) (Fin.suc v)     = tele-apply r v
      tele-apply tbase Fin.zero    {z} =
        fuse-idx Q cmb fsk corr (Γ .idx .isEquivalence .refl {γ}) {m₁ = z} {m₂ = z}
          (μObj Q sₛ .idx .isEquivalence .refl {z})
      tele-apply tbase (Fin.suc i) {z} = Tt.elEq-refl (inj₁ i) (Rs.iapply (cmb γ) i z)

      tele-shape-fam : ∀ {j} (S : Poly j) {ηA ηB ηC ηD} {dA dB dC dD}
                       {md : Rs.IMorD ηA ηB} {mdA : At.R.MorD ηC ηB dC dB} {md' : Rs'.IMorD ηD ηC} {fm : Ft.FMor ηA ηD dA dD}
                       {am : FR.FAct md dA dB} {am' : FR'.FAct md' dD dC}
                       (rel : TeleRel md mdA md' fm am am') (z : Ft.Tδ.⟦ ∣ S ∣ ⟧shape ηA) →
                       (Tt.fib-shape-subst S dB (tele-shape S rel z) ∘ FR.freindex-shape-fam S am {z})
                       ≈ (At.R.reindex-fam S mdA
                          ∘ (FR'.freindex-shape-fam S am' {Ft.fold-reindex-shape γ S fm z}
                             ∘ pair p₁ (Ft.fold-reindex-shape-fam γ S fm z)))
      tele-shape-fam (const A') rel z =
        ≈-trans (∘-cong (A' .fam .refl*) ≈-refl) (≈-trans id-left (≈-sym (≈-trans id-left (pair-p₂ _ _))))
      tele-shape-fam (var v) rel z = tele-apply-fam rel v
      tele-shape-fam (S₁ + S₂) rel (inj₁ z) = tele-shape-fam S₁ rel z
      tele-shape-fam (S₁ + S₂) rel (inj₂ z) = tele-shape-fam S₂ rel z
      tele-shape-fam (S₁ × S₂) rel (z₁ , z₂) =
        ≈-trans (strong-prod-m-post _ _ _ _)
          (≈-trans (strong-prod-m-cong (tele-shape-fam S₁ rel z₁) (tele-shape-fam S₂ rel z₂))
            (≈-sym (≈-trans (∘-cong ≈-refl (strong-prod-m-comp _ _ _ _)) (strong-prod-m-post _ _ _ _))))
      tele-shape-fam (μ S') rel (Ts.sup z') = tele-shape-fam S' (tbind S' rel) z'

      tele-apply-fam : ∀ {j} {ηA ηB ηC ηD} {dA dB dC dD}
                       {md : Rs.IMorD ηA ηB} {mdA : At.R.MorD ηC ηB dC dB} {md' : Rs'.IMorD ηD ηC} {fm : Ft.FMor ηA ηD dA dD}
                       {am : FR.FAct md dA dB} {am' : FR'.FAct md' dD dC}
                       (rel : TeleRel md mdA md' fm am am') (v : Fin j) {z} →
                       (Tt.fib-el-subst (ηB v) (dB v) (tele-apply rel v {z}) ∘ FR.aapply am v z)
                       ≈ (At.R.apply-fam mdA v (Rs'.iapply md' v (Ft.fold-apply γ fm v z))
                          ∘ (FR'.aapply am' v (Ft.fold-apply γ fm v z)
                             ∘ pair p₁ (Ft.fold-apply-fam γ fm v z)))
      tele-apply-fam (tbind S' r) Fin.zero    {z} = tele-shape-fam (μ S') r z
      tele-apply-fam (tbind S' r) (Fin.suc v)     = tele-apply-fam r v
      tele-apply-fam tbase Fin.zero    {z} =
        ≈-trans (fuse-fam γ Q cmb act fsk corr corr-fam {z}) (≈-sym (≈-trans id-left (pair-p₂ _ _)))
      tele-apply-fam tbase (Fin.suc i) {z} =
        ≈-trans (∘-cong (sₜ i .fam .refl*) ≈-refl)
          (≈-trans id-left (≈-sym (≈-trans id-left (≈-trans (∘-cong ≈-refl pair-ext0) id-right))))
