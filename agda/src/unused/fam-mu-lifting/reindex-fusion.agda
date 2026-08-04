{-# OPTIONS --prop --postfix-projections --safe #-}

------------------------------------------------------------------------------
-- Free-family fusion for the rooted interpretation, index level: a single
-- index-only reindex along a pointwise family equals the strong functorial
-- action of the family on indices. The lifting keeps every index, so this half
-- is untouched by the roots; the fibre half follows separately.
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
open import cmon-enriched using (CMonEnriched; Biproduct)
open import lifting using (Lifting)
open import prop-setoid as PS using ()
open import indexed-family using (_⇒f_)
import fam-mu-lifting.in-map

module unused.fam-mu-lifting.reindex-fusion {o m e} (os es : Level) {𝒞 : Category o m e}
    (T : HasTerminal 𝒞) (CM : CMonEnriched 𝒞) (BP : ∀ x y → Biproduct CM x y)
    {𝟙c : Category.obj 𝒞} (Lft : Lifting CM 𝟙c) where

open fam-mu-lifting.in-map os es T CM BP Lft public

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

