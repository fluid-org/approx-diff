{-# OPTIONS --prop --postfix-projections --safe #-}

------------------------------------------------------------------------------
-- Comparison of the fibre glued objects across a context reindexing: a
-- reindex morphism whose leaves carry glued inclusions extends to every
-- fibre, by the reindexing's own recursion, with the functorial actions of
-- the glued lifting and product at the nodes. The leaf inclusions decorate
-- the reindex morphism, one constructor per former, each required compatible
-- with the morphism's fibre map through the carrier inclusions so that the
-- extension tracks the fibre reindex.
------------------------------------------------------------------------------

open import Level using (Level; 0ℓ; Lift; lift; _⊔_) renaming (suc to lsuc)
open import Data.Nat using (ℕ; suc)
import Data.Fin as Fin
open Fin using (Fin)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import Data.Unit using (⊤; tt)
open import prop using (_,_)
open import prop-setoid as PS using ()
open import categories using (Category; HasTerminal; HasProducts)
open import cmon-enriched using (CMonEnriched; Biproduct)
open import lifting using (Lifting)
open import functor using (Functor)
open import predicate-system using (PredicateSystem; ClosureOp)
open import indexed-family using (_⇒f_)
import fam-mu-lifting.laws
import fam-mu-lifting.glued-mu

module fam-mu-lifting.glued-reindex {o m e} {𝒞 : Category o m e}
  (T : HasTerminal 𝒞) (CM : CMonEnriched 𝒞) (BP : ∀ x y → Biproduct CM x y)
  {𝟙c : Category.obj 𝒞} (Lft : Lifting CM 𝟙c)
  (let module R = fam-mu-lifting.laws 0ℓ 0ℓ T CM BP Lft)
  {o₂ m₂ e₂} (𝒫 : Category o₂ m₂ e₂) (𝒫P : HasProducts 𝒫)
  (system : PredicateSystem 𝒫 𝒫P)
  (G : Functor R.cat 𝒫)
  (let open PredicateSystem system)
  (Rt : ∀ (C : R.Obj) → Predicate (Functor.fobj G (R.Lf C)))
  (Cl : ClosureOp 𝒫 𝒫P system)
  where

open Functor

open fam-mu-lifting.glued-mu T CM BP Lft 𝒫 𝒫P system G Rt Cl public

open R hiding (fobj)
open Gl.Obj
open Gl._=>_

private
  ℓP : Level
  ℓP = o ⊔ m ⊔ e ⊔ lsuc 0ℓ ⊔ lsuc o₂ ⊔ lsuc m₂ ⊔ lsuc e₂

module GlReindex {nA nB}
    (δA : Fin nA → Obj) (δPA : ∀ i → Predicate (G .fobj (δA i)))
    (δB : Fin nB → Obj) (δPB : ∀ i → Predicate (G .fobj (δB i)))
    (Rt-iso : ∀ {C D : Obj} (h : Mor C D)
              (hinv : ∀ x → D .fam .fm (h .idxf .PS._⇒_.func x) ⇒ C .fam .fm x) →
              (∀ x → (h .famf ._⇒f_.transf x ∘ hinv x) ≈ id _) →
              (∀ x → (hinv x ∘ h .famf ._⇒f_.transf x) ≈ id _) →
              Rt C ⊑ (Rt D [ G .fmor (Lf-map h) ]))
    where

  private
    module MA = MuPred δA δPA
    module MB = MuPred δB δPB
    module TA = Tree δA
    module TB = Tree δB
  open Reindex δA δB

  -- Leaf data over a reindex morphism: a glued inclusion with fibrewise
  -- inverses at every element of every leaf, compatible with the morphism's
  -- fibre map through the carrier inclusions.
  data PredD : ∀ {k} {ρA : Fin k → Fin nA ⊎ Sort nA} {ρB : Fin k → Fin nB ⊎ Sort nB}
               {dA : ∀ v → TA.DecoAssign (ρA v)} {dB : ∀ v → TB.DecoAssign (ρB v)} →
               MorD ρA ρB dA dB →
               (∀ v → MA.DecoAssignPred (ρA v) (dA v)) →
               (∀ v → MB.DecoAssignPred (ρB v) (dB v)) → Set ℓP where
    pbase : ∀ {k} {ρA : Fin k → Fin nA ⊎ Sort nA} {ρB : Fin k → Fin nB ⊎ Sort nB}
            {dA : ∀ v → TA.DecoAssign (ρA v)} {dB : ∀ v → TB.DecoAssign (ρB v)}
            {f : ∀ v → TA.El (ρA v) → TB.El (ρB v)}
            {f-resp : ∀ v {a a'} → TA.elEq (ρA v) a a' → TB.elEq (ρB v) (f v a) (f v a')}
            {ffam : ∀ v a → TA.fib-el (ρA v) (dA v) a ⇒ TB.fib-el (ρB v) (dB v) (f v a)}
            {ffam-natural : ∀ v {a a'} (p : TA.elEq (ρA v) a a') →
                            (ffam v a' ∘ TA.fib-el-subst (ρA v) (dA v) p)
                              ≈ (TB.fib-el-subst (ρB v) (dB v) (f-resp v p) ∘ ffam v a)}
            {pdA : ∀ v → MA.DecoAssignPred (ρA v) (dA v)}
            {pdB : ∀ v → MB.DecoAssignPred (ρB v) (dB v)}
            (pel : ∀ v (a : TA.El (ρA v)) →
                   MA.fib-el-Gl (ρA v) (dA v) (pdA v) a
                     =>ᵢ MB.fib-el-Gl (ρB v) (dB v) (pdB v) (f v a))
            (pel-in : ∀ v (a : TA.El (ρA v))
                      (ι : MA.fib-el-Gl (ρA v) (dA v) (pdA v) a .carrier .idx .Carrier) →
                      (MB.in-el (ρB v) (dB v) (pdB v) (f v a)
                         (pel v a .mor .morph .idxf .PS._⇒_.func ι)
                        ∘ pel v a .mor .morph .famf ._⇒f_.transf ι)
                      ≈ (ffam v a ∘ MA.in-el (ρA v) (dA v) (pdA v) a ι)) →
            PredD (base {ρA = ρA} {ρB = ρB} {dA = dA} {dB = dB} f f-resp ffam ffam-natural)
                  pdA pdB
    pbind : ∀ {k} {ρA ρB} {dA : ∀ v → TA.DecoAssign (ρA v)} {dB : ∀ v → TB.DecoAssign (ρB v)}
            {md : MorD {k} ρA ρB dA dB} {pdA pdB} (Q : Poly (suc k)) (pQ : PolyPred Q) →
            PredD md pdA pdB →
            PredD (bind Q md) (MA.deco-ext-pred Q pQ pdA) (MB.deco-ext-pred Q pQ pdB)

  private
    Lf-Glᵢ' : ∀ {X Y} → X =>ᵢ Y → Lf-Gl X =>ᵢ Lf-Gl Y
    Lf-Glᵢ' f = Lf-Glᵢ f (Rt-iso (f .mor .morph) (f .inv) (f .inv₁) (f .inv₂))

  -- The glued comparison at each fibre, by the reindexing's recursion.
  mutual
    reindex-Gl : ∀ {k} (Q : Poly (suc k)) {ρA ρB}
                 {dA : ∀ v → TA.DecoAssign (ρA v)} {dB : ∀ v → TB.DecoAssign (ρB v)}
                 {md : MorD ρA ρB dA dB} (pQ : PolyPred Q) {pdA pdB}
                 (pmd : PredD md pdA pdB) (t : TA.W ∣ Q ∣ ρA) →
                 MA.fib-Gl Q dA pQ pdA t =>ᵢ MB.fib-Gl Q dB pQ pdB (reindex md t)
    reindex-Gl Q pQ pmd (TA.sup x) = reindex-shape-Gl Q pQ (pbind Q pQ pmd) x

    reindex-shape-Gl : ∀ {j} (Q : Poly j) {ηA ηB}
                       {dA : ∀ v → TA.DecoAssign (ηA v)} {dB : ∀ v → TB.DecoAssign (ηB v)}
                       {md : MorD ηA ηB dA dB} (pQ : PolyPred Q) {pdA pdB}
                       (pmd : PredD md pdA pdB) (a : TA.⟦ ∣ Q ∣ ⟧shape ηA) →
                       MA.fib-shape-Gl Q dA pQ pdA a
                         =>ᵢ MB.fib-shape-Gl Q dB pQ pdB (reindex-shape ∣ Q ∣ md a)
    reindex-shape-Gl (const A) pA pmd a = idᵢ
    reindex-shape-Gl (var i)   pQ pmd a = papply pmd i a
    reindex-shape-Gl (P' + Q') (pP , pQ) pmd (inj₁ x) = Lf-Glᵢ' (reindex-shape-Gl P' pP pmd x)
    reindex-shape-Gl (P' + Q') (pP , pQ) pmd (inj₂ y) = Lf-Glᵢ' (reindex-shape-Gl Q' pQ pmd y)
    reindex-shape-Gl (P' × Q') (pP , pQ) pmd (x , y) =
      Lf-Glᵢ' ([×]ᵢ (reindex-shape-Gl P' pP pmd x) (reindex-shape-Gl Q' pQ pmd y))
    reindex-shape-Gl (μ Q')    pQ' pmd t = reindex-Gl Q' pQ' pmd t

    papply : ∀ {k} {ρA ρB}
             {dA : ∀ v → TA.DecoAssign (ρA v)} {dB : ∀ v → TB.DecoAssign (ρB v)}
             {md : MorD {k} ρA ρB dA dB} {pdA pdB}
             (pmd : PredD md pdA pdB) (v : Fin k) (a : TA.El (ρA v)) →
             MA.fib-el-Gl (ρA v) (dA v) (pdA v) a
               =>ᵢ MB.fib-el-Gl (ρB v) (dB v) (pdB v) (apply md v a)
    papply (pbase pel pel-in)  v           a = pel v a
    papply (pbind Q pQ pmd)    Fin.zero    a = reindex-Gl Q pQ pmd a
    papply (pbind Q pQ pmd)    (Fin.suc v) a = papply pmd v a

  -- The comparison intertwines the carrier inclusions with the fibre reindex.
  mutual
    reindex-Gl-in : ∀ {k} (Q : Poly (suc k)) {ρA ρB}
                    {dA : ∀ v → TA.DecoAssign (ρA v)} {dB : ∀ v → TB.DecoAssign (ρB v)}
                    {md : MorD ρA ρB dA dB} (pQ : PolyPred Q) {pdA pdB}
                    (pmd : PredD md pdA pdB) (t : TA.W ∣ Q ∣ ρA)
                    (ι : MA.fib-Gl Q dA pQ pdA t .carrier .idx .Carrier) →
                    (MB.in-fib Q dB pQ pdB (reindex md t)
                       (reindex-Gl Q pQ pmd t .mor .morph .idxf .PS._⇒_.func ι)
                      ∘ reindex-Gl Q pQ pmd t .mor .morph .famf ._⇒f_.transf ι)
                    ≈ (reindex-fam-W md {t = t} ∘ MA.in-fib Q dA pQ pdA t ι)
    reindex-Gl-in Q pQ pmd (TA.sup x) ι = reindex-shape-Gl-in Q pQ (pbind Q pQ pmd) x ι

    reindex-shape-Gl-in : ∀ {j} (Q : Poly j) {ηA ηB}
                          {dA : ∀ v → TA.DecoAssign (ηA v)} {dB : ∀ v → TB.DecoAssign (ηB v)}
                          {md : MorD ηA ηB dA dB} (pQ : PolyPred Q) {pdA pdB}
                          (pmd : PredD md pdA pdB) (a : TA.⟦ ∣ Q ∣ ⟧shape ηA)
                          (ι : MA.fib-shape-Gl Q dA pQ pdA a .carrier .idx .Carrier) →
                          (MB.in-shape Q dB pQ pdB (reindex-shape ∣ Q ∣ md a)
                             (reindex-shape-Gl Q pQ pmd a .mor .morph .idxf .PS._⇒_.func ι)
                            ∘ reindex-shape-Gl Q pQ pmd a .mor .morph .famf ._⇒f_.transf ι)
                          ≈ (reindex-fam Q md {a = a} ∘ MA.in-shape Q dA pQ pdA a ι)
    reindex-shape-Gl-in (const A) pA pmd a ι = ≈-refl
    reindex-shape-Gl-in (var i)   pQ pmd a ι = papply-in pmd i a ι
    reindex-shape-Gl-in (P' + Q') (pP , pQ) pmd (inj₁ x) ι =
      ≈-trans (≈-sym (Lmap-comp _ _))
      (≈-trans (Lmap-cong (reindex-shape-Gl-in P' pP pmd x ι)) (Lmap-comp _ _))
    reindex-shape-Gl-in (P' + Q') (pP , pQ) pmd (inj₂ y) ι =
      ≈-trans (≈-sym (Lmap-comp _ _))
      (≈-trans (Lmap-cong (reindex-shape-Gl-in Q' pQ pmd y ι)) (Lmap-comp _ _))
    reindex-shape-Gl-in (P' × Q') (pP , pQ) pmd (x , y) (ι₁ , ι₂) =
      ≈-trans (∘-cong ≈-refl (Lmap-cong (pair-cong id-left id-left)))
      (≈-trans (≈-sym (Lmap-comp _ _))
      (≈-trans (Lmap-cong
                 (≈-trans (≈-sym (prod-m-comp _ _ _ _))
                  (≈-trans (prod-m-cong (reindex-shape-Gl-in P' pP pmd x ι₁)
                                        (reindex-shape-Gl-in Q' pQ pmd y ι₂))
                           (prod-m-comp _ _ _ _))))
               (Lmap-comp _ _)))
    reindex-shape-Gl-in (μ Q')    pQ' pmd t ι = reindex-Gl-in Q' pQ' pmd t ι

    papply-in : ∀ {k} {ρA ρB}
                {dA : ∀ v → TA.DecoAssign (ρA v)} {dB : ∀ v → TB.DecoAssign (ρB v)}
                {md : MorD {k} ρA ρB dA dB} {pdA pdB}
                (pmd : PredD md pdA pdB) (v : Fin k) (a : TA.El (ρA v))
                (ι : MA.fib-el-Gl (ρA v) (dA v) (pdA v) a .carrier .idx .Carrier) →
                (MB.in-el (ρB v) (dB v) (pdB v) (apply md v a)
                   (papply pmd v a .mor .morph .idxf .PS._⇒_.func ι)
                  ∘ papply pmd v a .mor .morph .famf ._⇒f_.transf ι)
                ≈ (apply-fam md v a ∘ MA.in-el (ρA v) (dA v) (pdA v) a ι)
    papply-in (pbase pel pel-in)  v           a ι = pel-in v a ι
    papply-in (pbind Q pQ pmd)    Fin.zero    a ι = reindex-Gl-in Q pQ pmd a ι
    papply-in (pbind Q pQ pmd)    (Fin.suc v) a ι = papply-in pmd v a ι
