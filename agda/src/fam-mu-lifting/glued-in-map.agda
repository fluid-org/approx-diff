{-# OPTIONS --prop --postfix-projections --safe #-}

------------------------------------------------------------------------------
-- The glued algebra map: comparison of the one-step glued interpretation with
-- the decorated μ-carrier over the algebra map inMor. The one-step object is
-- split into its singletons; each singleton embeds into the corresponding
-- fibre glued object by structural recursion on the polynomial, with the
-- factorisations of the singleton inclusions through the coproduct, lifting
-- and product formers at the nodes. The singleton morphisms and their
-- factorisation laws are independent of the μ-polynomial and live at the top
-- level.
------------------------------------------------------------------------------

open import Level using (Level; 0ℓ; Lift; lift; _⊔_) renaming (suc to lsuc)
open import Data.Nat using (ℕ; suc)
import Data.Fin as Fin
open Fin using (Fin)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import Data.Unit using (⊤; tt)
open import prop using (_,_)
open import basics using (IsJoin; IsMeet; IsBigJoin; IsClosureOp)
open import prop-setoid as PS using ()
open import categories using (Category; HasTerminal; HasProducts; HasCoproducts)
open import cmon-enriched using (CMonEnriched; Biproduct)
open import lifting using (Lifting)
open import functor using (Functor)
open import predicate-system using (PredicateSystem; ClosureOp)
open import indexed-family using (_⇒f_)
import fam-mu-lifting.laws
import fam-mu-lifting.glued-reindex

module fam-mu-lifting.glued-in-map {o m e} {𝒞 : Category o m e}
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

open fam-mu-lifting.glued-reindex T CM BP Lft 𝒫 𝒫P system G Rt Cl public

open R hiding (fobj)
open Gl.Obj
open Gl._=>_
open ClosureOp Cl

private
  module 𝒫C = Category 𝒫
  module CP = HasCoproducts coproducts

-- The singleton inclusions interact with the value formers through a family
-- of fibrewise-identity comparisons: the injection into a lifted singleton,
-- the lifted singleton as the singleton at a lifted fibre, the projections
-- and pairing at a product fibre.
sing-inj : (C : Obj) (x : C .idx .Carrier) →
           Mor simple[ PS.𝟙 , C .fam .fm x ] simple[ PS.𝟙 , L (C .fam .fm x) ]
sing-inj C x .idxf = PS.idS PS.𝟙
sing-inj C x .famf ._⇒f_.transf _ = inj
sing-inj C x .famf ._⇒f_.natural _ = ≈-trans id-right (≈-sym id-left)

sing-Lf : (C : Obj) (x : C .idx .Carrier) →
          Mor simple[ PS.𝟙 , L (C .fam .fm x) ] (Lf simple[ PS.𝟙 , C .fam .fm x ])
sing-Lf C x .idxf = PS.idS PS.𝟙
sing-Lf C x .famf ._⇒f_.transf _ = id _
sing-Lf C x .famf ._⇒f_.natural _ = ≈-trans id-left (≈-sym (≈-trans id-right Lmap-id))

sing-pair : (C D : Obj) (x : C .idx .Carrier) (y : D .idx .Carrier) →
            Mor simple[ PS.𝟙 , prod (C .fam .fm x) (D .fam .fm y) ]
                (Fam𝒞-P.prod simple[ PS.𝟙 , C .fam .fm x ] simple[ PS.𝟙 , D .fam .fm y ])
sing-pair C D x y .idxf .PS._⇒_.func t = t , t
sing-pair C D x y .idxf .PS._⇒_.func-resp-≈ e = e , e
sing-pair C D x y .famf ._⇒f_.transf _ = id _
sing-pair C D x y .famf ._⇒f_.natural _ =
  ≈-trans id-left (≈-sym (≈-trans id-right prod-m-id))

sing-p₁ : (C D : Obj) (x : C .idx .Carrier) (y : D .idx .Carrier) →
          Mor simple[ PS.𝟙 , prod (C .fam .fm x) (D .fam .fm y) ]
              simple[ PS.𝟙 , C .fam .fm x ]
sing-p₁ C D x y .idxf = PS.idS PS.𝟙
sing-p₁ C D x y .famf ._⇒f_.transf _ = p₁
sing-p₁ C D x y .famf ._⇒f_.natural _ = ≈-trans id-right (≈-sym id-left)

sing-p₂ : (C D : Obj) (x : C .idx .Carrier) (y : D .idx .Carrier) →
          Mor simple[ PS.𝟙 , prod (C .fam .fm x) (D .fam .fm y) ]
              simple[ PS.𝟙 , D .fam .fm y ]
sing-p₂ C D x y .idxf = PS.idS PS.𝟙
sing-p₂ C D x y .famf ._⇒f_.transf _ = p₂
sing-p₂ C D x y .famf ._⇒f_.natural _ = ≈-trans id-right (≈-sym id-left)

-- The singleton inclusion factors through each former.
elem-in-inj₁ : ∀ (X Y : Obj) (x : X .idx .Carrier) →
               Fam𝒞._≈_ (elem-in (CP.coprod X Y) (inj₁ x))
                        (Fam𝒞._∘_ (CP.in₁ {X} {Y}) (elem-in X x))
elem-in-inj₁ X Y x ._≃_.idxf-eq .PS._≃m_.func-eq _ = X .idx .isEquivalence .refl
elem-in-inj₁ X Y x ._≃_.famf-eq .indexed-family._≃f_.transf-eq =
  ≈-trans id-right (≈-trans (X .fam .refl*) (≈-sym (≈-trans id-left id-left)))

elem-in-inj₂ : ∀ (X Y : Obj) (y : Y .idx .Carrier) →
               Fam𝒞._≈_ (elem-in (CP.coprod X Y) (inj₂ y))
                        (Fam𝒞._∘_ (CP.in₂ {X} {Y}) (elem-in Y y))
elem-in-inj₂ X Y y ._≃_.idxf-eq .PS._≃m_.func-eq _ = Y .idx .isEquivalence .refl
elem-in-inj₂ X Y y ._≃_.famf-eq .indexed-family._≃f_.transf-eq =
  ≈-trans id-right (≈-trans (Y .fam .refl*) (≈-sym (≈-trans id-left id-left)))

elem-in-Lf : ∀ (C : Obj) (x : C .idx .Carrier) →
             Fam𝒞._≈_ (elem-in (Lf C) x)
                      (Fam𝒞._∘_ (Lf-map (elem-in C x)) (sing-Lf C x))
elem-in-Lf C x ._≃_.idxf-eq .PS._≃m_.func-eq _ = C .idx .isEquivalence .refl
elem-in-Lf C x ._≃_.famf-eq .indexed-family._≃f_.transf-eq =
  ≈-trans id-right
  (≈-trans (≈-trans (Lmap-cong (C .fam .refl*)) Lmap-id)
           (≈-sym (≈-trans id-left (≈-trans id-right Lmap-id))))

elem-in-pair : ∀ (C D : Obj) (x : C .idx .Carrier) (y : D .idx .Carrier) →
               Fam𝒞._≈_ (elem-in (Fam𝒞-P.prod C D) (x , y))
                        (Fam𝒞._∘_ (Fam𝒞-P.prod-m (elem-in C x) (elem-in D y))
                                  (sing-pair C D x y))
elem-in-pair C D x y ._≃_.idxf-eq .PS._≃m_.func-eq _ =
  C .idx .isEquivalence .refl , D .idx .isEquivalence .refl
elem-in-pair C D x y ._≃_.famf-eq .indexed-family._≃f_.transf-eq =
  ≈-trans id-right
  (≈-trans (≈-trans (prod-m-cong (C .fam .refl*) (D .fam .refl*)) prod-m-id)
  (≈-sym (≈-trans id-left
         (≈-trans id-right
         (≈-trans (pair-cong (≈-trans id-left id-left) (≈-trans id-left id-left))
         (≈-trans (≈-sym (pair-cong id-right id-right)) (pair-ext (id _))))))))

injF-sing : ∀ (C : Obj) (x : C .idx .Carrier) →
            Fam𝒞._≈_ (Fam𝒞._∘_ (sing-Lf C x) (sing-inj C x))
                     (injF {simple[ PS.𝟙 , C .fam .fm x ]})
injF-sing C x ._≃_.idxf-eq .PS._≃m_.func-eq e = e
injF-sing C x ._≃_.famf-eq .indexed-family._≃f_.transf-eq =
  ≈-trans (∘-cong Lmap-id (≈-trans id-left id-left)) id-left

p₁-sing : ∀ (C D : Obj) (x : C .idx .Carrier) (y : D .idx .Carrier) →
          Fam𝒞._≈_ (Fam𝒞._∘_ (Fam𝒞-P.p₁ {C} {D}) (elem-in (Fam𝒞-P.prod C D) (x , y)))
                   (Fam𝒞._∘_ (elem-in C x) (sing-p₁ C D x y))
p₁-sing C D x y ._≃_.idxf-eq .PS._≃m_.func-eq _ = C .idx .isEquivalence .refl
p₁-sing C D x y ._≃_.famf-eq .indexed-family._≃f_.transf-eq =
  ≈-trans (∘-cong (C .fam .refl*) (≈-trans id-left id-right))
          (≈-trans id-left (≈-sym (≈-trans id-left id-left)))

p₂-sing : ∀ (C D : Obj) (x : C .idx .Carrier) (y : D .idx .Carrier) →
          Fam𝒞._≈_ (Fam𝒞._∘_ (Fam𝒞-P.p₂ {C} {D}) (elem-in (Fam𝒞-P.prod C D) (x , y)))
                   (Fam𝒞._∘_ (elem-in D y) (sing-p₂ C D x y))
p₂-sing C D x y ._≃_.idxf-eq .PS._≃m_.func-eq _ = D .idx .isEquivalence .refl
p₂-sing C D x y ._≃_.famf-eq .indexed-family._≃f_.transf-eq =
  ≈-trans (∘-cong (D .fam .refl*) (≈-trans id-left id-right))
          (≈-trans id-left (≈-sym (≈-trans id-left id-left)))

p₁-pair : ∀ (C D : Obj) (x : C .idx .Carrier) (y : D .idx .Carrier) →
          Fam𝒞._≈_ (Fam𝒞._∘_ (Fam𝒞-P.p₁ {simple[ PS.𝟙 , C .fam .fm x ]}
                                         {simple[ PS.𝟙 , D .fam .fm y ]})
                             (sing-pair C D x y))
                   (sing-p₁ C D x y)
p₁-pair C D x y ._≃_.idxf-eq .PS._≃m_.func-eq e = e
p₁-pair C D x y ._≃_.famf-eq .indexed-family._≃f_.transf-eq =
  ≈-trans id-left (≈-trans id-left id-right)

p₂-pair : ∀ (C D : Obj) (x : C .idx .Carrier) (y : D .idx .Carrier) →
          Fam𝒞._≈_ (Fam𝒞._∘_ (Fam𝒞-P.p₂ {simple[ PS.𝟙 , C .fam .fm x ]}
                                         {simple[ PS.𝟙 , D .fam .fm y ]})
                             (sing-pair C D x y))
                   (sing-p₂ C D x y)
p₂-pair C D x y ._≃_.idxf-eq .PS._≃m_.func-eq e = e
p₂-pair C D x y ._≃_.famf-eq .indexed-family._≃f_.transf-eq =
  ≈-trans id-left (≈-trans id-left id-right)

injF-pair : ∀ (C D : Obj) (x : C .idx .Carrier) (y : D .idx .Carrier) →
            Fam𝒞._≈_ (Fam𝒞._∘_ (Fam𝒞._∘_ (Lf-map (sing-pair C D x y))
                                          (sing-Lf (Fam𝒞-P.prod C D) (x , y)))
                               (sing-inj (Fam𝒞-P.prod C D) (x , y)))
                     (Fam𝒞._∘_ (injF {Fam𝒞-P.prod simple[ PS.𝟙 , C .fam .fm x ]
                                                  simple[ PS.𝟙 , D .fam .fm y ]})
                               (sing-pair C D x y))
injF-pair C D x y ._≃_.idxf-eq .PS._≃m_.func-eq e = e , e
injF-pair C D x y ._≃_.famf-eq .indexed-family._≃f_.transf-eq =
  ≈-trans (∘-cong (≈-trans (Lmap-cong prod-m-id) Lmap-id)
                  (≈-trans id-left
                           (≈-trans (∘-cong (≈-trans id-left (≈-trans id-right Lmap-id))
                                            ≈-refl)
                                    id-left)))
          (≈-trans id-left (≈-sym (≈-trans id-left id-right)))

-- A direct image transports across a commuting square, by the unit and the
-- reindexing laws alone.
img-square : ∀ {C₁ C₂ D₁ D₂ : Obj} (h₁ : Mor D₁ D₂) (h₂ : Mor C₁ D₁)
             (h₃ : Mor C₂ D₂) (h₄ : Mor C₁ C₂) {Tp : Predicate (G .fobj C₂)} →
             Fam𝒞._≈_ (Fam𝒞._∘_ h₁ h₂) (Fam𝒞._∘_ h₃ h₄) →
             ((Tp [ G .fmor h₄ ]) ⟨ G .fmor h₂ ⟩) ⊑ ((Tp ⟨ G .fmor h₃ ⟩) [ G .fmor h₁ ])
img-square h₁ h₂ h₃ h₄ sq =
  adjoint₂ (⊑-trans ((unit (G .fmor h₃)) [ G .fmor h₄ ]m)
           (⊑-trans ([]-comp _ _)
           (⊑-trans ([]-cong (𝒫C.≈-sym (G .fmor-comp _ _)))
           (⊑-trans ([]-cong (G .fmor-cong (Fam𝒞.≈-sym sq)))
           (⊑-trans ([]-cong (G .fmor-comp _ _))
                    ([]-comp⁻¹ _ _))))))

img-square-id : ∀ {C D₁ D₂ : Obj} (h₁ : Mor D₁ D₂) (h₂ : Mor C D₁) (h₃ : Mor C D₂)
                {Tp : Predicate (G .fobj C)} →
                Fam𝒞._≈_ (Fam𝒞._∘_ h₁ h₂) h₃ →
                (Tp ⟨ G .fmor h₂ ⟩) ⊑ ((Tp ⟨ G .fmor h₃ ⟩) [ G .fmor h₁ ])
img-square-id h₁ h₂ h₃ sq =
  ⊑-trans ((⊑-trans []-id ([]-cong (𝒫C.≈-sym (G .fmor-id)))) ⟨ G .fmor h₂ ⟩m)
          (img-square h₁ h₂ h₃ (Fam𝒞.id _)
                      (Fam𝒞.≈-trans sq (Fam𝒞.≈-sym Fam𝒞.id-right)))

-- The comparison of the one-step glued interpretation with the decorated
-- μ-carrier, at a fixed μ-polynomial and environment. The instance squares
-- are parameters: the two-sided transport of the root predicate along
-- fibrewise isomorphisms, extraction of a direct image along its own
-- injection, disjointness of the two coproduct images over a singleton,
-- Beck-Chevalley for the payload injection at a singleton, and extraction of
-- the closed join at a singleton tree.
module GlInMap {n} (P : Poly (suc n)) (pP : PolyPred P)
    (δ : Fin n → Obj) (δP : ∀ i → Predicate (G .fobj (δ i)))
    (Rt-iso : ∀ {C D : Obj} (h : Mor C D)
              (hinv : ∀ x → D .fam .fm (h .idxf .PS._⇒_.func x) ⇒ C .fam .fm x) →
              (∀ x → (h .famf ._⇒f_.transf x ∘ hinv x) ≈ id _) →
              (∀ x → (hinv x ∘ h .famf ._⇒f_.transf x) ≈ id _) →
              Rt C ⊑ (Rt D [ G .fmor (Lf-map h) ]))
    (Rt-iso⁻ : ∀ {C D : Obj} (h : Mor C D)
               (hinv : ∀ x → D .fam .fm (h .idxf .PS._⇒_.func x) ⇒ C .fam .fm x) →
               (∀ x → (h .famf ._⇒f_.transf x ∘ hinv x) ≈ id _) →
               (∀ x → (hinv x ∘ h .famf ._⇒f_.transf x) ≈ id _) →
               (Rt D [ G .fmor (Lf-map h) ]) ⊑ Rt C)
    (in₁-extract : ∀ {X Y : Obj} {Q : Predicate (G .fobj X)} →
                   ((Q ⟨ G .fmor (CP.in₁ {X} {Y}) ⟩) [ G .fmor (CP.in₁ {X} {Y}) ]) ⊑ Q)
    (in₂-extract : ∀ {X Y : Obj} {Q : Predicate (G .fobj Y)} →
                   ((Q ⟨ G .fmor (CP.in₂ {X} {Y}) ⟩) [ G .fmor (CP.in₂ {X} {Y}) ]) ⊑ Q)
    (disjoint₁ : ∀ {X Y : Obj} {Q : Predicate (G .fobj Y)} (x : X .idx .Carrier)
                 {C : Obj} (h : Mor simple[ PS.𝟙 , X .fam .fm x ] (Lf C)) →
                 ((Q ⟨ G .fmor (CP.in₂ {X} {Y}) ⟩)
                    [ G .fmor (elem-in (CP.coprod X Y) (inj₁ x)) ]) ⊑ (Rt C [ G .fmor h ]))
    (disjoint₂ : ∀ {X Y : Obj} {Q : Predicate (G .fobj X)} (y : Y .idx .Carrier)
                 {C : Obj} (h : Mor simple[ PS.𝟙 , Y .fam .fm y ] (Lf C)) →
                 ((Q ⟨ G .fmor (CP.in₁ {X} {Y}) ⟩)
                    [ G .fmor (elem-in (CP.coprod X Y) (inj₂ y)) ]) ⊑ (Rt C [ G .fmor h ]))
    (BC-injF : ∀ {C : Obj} {Qp : Predicate (G .fobj C)} (x : C .idx .Carrier) →
               ((Qp ⟨ G .fmor (injF {C}) ⟩) [ G .fmor (elem-in (Lf C) x) ])
                 ⊑ ((Qp [ G .fmor (elem-in C x) ]) ⟨ G .fmor (sing-inj C x) ⟩))
    (sing-extract : ∀ {k} (δ₀ : Fin k → Obj) (δP₀ : ∀ i → Predicate (G .fobj (δ₀ i)))
                    (Q : Poly (suc k)) (pQ : PolyPred Q)
                    (t : Tree.W δ₀ ∣ Q ∣ (λ i → inj₁ i)) →
                    (MuPred.μ-Gl δ₀ δP₀ Q pQ .pred [ G .fmor (elem-in (μObj Q δ₀) t) ])
                      ⊑ (MuPred.fib-Gl δ₀ δP₀ Q (λ i → lift tt) pQ (λ i → lift tt) t .pred
                           [ G .fmor (MuPred.tree-out δ₀ δP₀ Q pQ t) ]))
    (sing-split : ∀ {X : Obj} {Q : Predicate (G .fobj X)} →
                  Q ⊑ 𝐂 (⋁ (X .idx .Carrier)
                          (λ x → (Q [ G .fmor (elem-in X x) ]) ⟨ G .fmor (elem-in X x) ⟩)))
    where

  open InMapDef P δ renaming (module R to RX)

  δP⁺ : ∀ i → Predicate (G .fobj (δ' i))
  δP⁺ Fin.zero    = MuPred.μ-Gl δ δP P pP .pred
  δP⁺ (Fin.suc i) = δP i

  private
    module M⁺ = MuPred δ' δP⁺
    module Mδ = MuPred δ δP
    module GR = GlReindex δ' δP⁺ δ δP Rt-iso

  -- The singleton at a tree includes into the tree's fibre glued object; the
  -- predicate part is the join extraction.
  sing-μ : ∀ {k} (δ₀ : Fin k → Obj) (δP₀ : ∀ i → Predicate (G .fobj (δ₀ i)))
           (Q : Poly (suc k)) (pQ : PolyPred Q)
           (t : Tree.W δ₀ ∣ Q ∣ (λ i → inj₁ i)) →
           glue simple[ PS.𝟙 , μObj Q δ₀ .fam .fm t ]
                (MuPred.μ-Gl δ₀ δP₀ Q pQ .pred [ G .fmor (elem-in (μObj Q δ₀) t) ])
             =>ᵢ MuPred.fib-Gl δ₀ δP₀ Q (λ i → lift tt) pQ (λ i → lift tt) t
  sing-μ δ₀ δP₀ Q pQ t .mor .morph = MuPred.tree-out δ₀ δP₀ Q pQ t
  sing-μ δ₀ δP₀ Q pQ t .mor .presv = sing-extract δ₀ δP₀ Q pQ t
  sing-μ δ₀ δP₀ Q pQ t .inv _ =
    MuPred.in-fib δ₀ δP₀ Q (λ i → lift tt) pQ (λ i → lift tt) t
                  (MuPred.fib-ix δ₀ δP₀ Q (λ i → lift tt) pQ (λ i → lift tt) t)
  sing-μ δ₀ δP₀ Q pQ t .inv₁ _ =
    MuPred.out-in-fib δ₀ δP₀ Q (λ i → lift tt) pQ (λ i → lift tt) t _
  sing-μ δ₀ δP₀ Q pQ t .inv₂ _ =
    MuPred.in-out-fib δ₀ δP₀ Q (λ i → lift tt) pQ (λ i → lift tt) t _

  -- The leaf data of the base reindexing: the environment leaves are
  -- definitional, the μ-leaf extracts the join at the singleton.
  pel₀ : ∀ v (a : TX.El (inj₁ v)) →
         M⁺.fib-el-Gl (inj₁ v) (lift tt) (lift tt) a
           =>ᵢ Mδ.fib-el-Gl (Sh.η₀ ∣ P ∣ v) (Tδ.deco-ext P (λ i → lift tt) v)
                            (Mδ.deco-ext-pred P pP (λ i → lift tt) v) (m₀ v a)
  pel₀ Fin.zero    a = sing-μ δ δP P pP a
  pel₀ (Fin.suc i) a = idᵢ

  pel-in₀ : ∀ v (a : TX.El (inj₁ v))
            (ι : M⁺.fib-el-Gl (inj₁ v) (lift tt) (lift tt) a .carrier .idx .Carrier) →
            (Mδ.in-el (Sh.η₀ ∣ P ∣ v) (Tδ.deco-ext P (λ i → lift tt) v)
                      (Mδ.deco-ext-pred P pP (λ i → lift tt) v) (m₀ v a)
                      (pel₀ v a .mor .morph .idxf .PS._⇒_.func ι)
              ∘ pel₀ v a .mor .morph .famf ._⇒f_.transf ι)
            ≈ (m₀-fam v a ∘ M⁺.in-el (inj₁ v) (lift tt) (lift tt) a ι)
  pel-in₀ Fin.zero    a ι =
    ≈-trans (Mδ.in-out-fib P (λ i → lift tt) pP (λ i → lift tt) a _) (≈-sym id-left)
  pel-in₀ (Fin.suc i) a ι = ≈-refl

  -- The leaf decoration of the base reindexing.
  pmd₀ : GR.PredD mor₀ (λ v → lift tt) (Mδ.deco-ext-pred P pP (λ i → lift tt))
  pmd₀ = GR.pbase pel₀ pel-in₀

  private
    Lf-Glᵢ' : ∀ {X Y} → X =>ᵢ Y → Lf-Gl X =>ᵢ Lf-Gl Y
    Lf-Glᵢ' f = Lf-Glᵢ f (Rt-iso (f .mor .morph) (f .inv) (f .inv₁) (f .inv₂))

    -- The node step at a sum: the singleton at an inj₁ index becomes the
    -- lifted singleton at the left summand. The live branch extracts along
    -- its own injection, the dead branch is discharged by disjointness, and
    -- the root transports along the fibrewise isomorphisms.
    node-inj₁ : ∀ (F₁ F₂ : Gl.Obj) (x : F₁ .carrier .idx .Carrier) →
                glue simple[ PS.𝟙 , L (F₁ .carrier .fam .fm x) ]
                     (((Lf-Gl F₁ .pred
                          ⟨ G .fmor (CP.in₁ {Lf (F₁ .carrier)} {Lf (F₂ .carrier)}) ⟩)
                        ++ (Lf-Gl F₂ .pred ⟨ G .fmor CP.in₂ ⟩))
                        [ G .fmor (elem-in (CP.coprod (Lf (F₁ .carrier)) (Lf (F₂ .carrier)))
                                           (inj₁ x)) ])
                  =>ᵢ Lf-Gl (glue simple[ PS.𝟙 , F₁ .carrier .fam .fm x ]
                                  (F₁ .pred [ G .fmor (elem-in (F₁ .carrier) x) ]))
    node-inj₁ F₁ F₂ x .mor .morph = sing-Lf (F₁ .carrier) x
    node-inj₁ F₁ F₂ x .mor .presv =
      ⊑-trans []-++
      (++-isJoin .IsJoin.[_,_]
        (⊑-trans ([]-cong (G .fmor-cong (elem-in-inj₁ (Lf (F₁ .carrier)) (Lf (F₂ .carrier)) x)))
        (⊑-trans ([]-cong (G .fmor-comp _ _))
        (⊑-trans ([]-comp⁻¹ _ _)
        (⊑-trans (in₁-extract [ G .fmor (elem-in (Lf (F₁ .carrier)) x) ]m)
        (⊑-trans []-++
        (++-isJoin .IsJoin.[_,_]
          (⊑-trans (BC-injF x)
          (⊑-trans (img-square-id (sing-Lf (F₁ .carrier) x) (sing-inj (F₁ .carrier) x)
                                  injF (injF-sing (F₁ .carrier) x))
                   ((++-isJoin .IsJoin.inl) [ G .fmor (sing-Lf (F₁ .carrier) x) ]m)))
          (⊑-trans ([]-cong (G .fmor-cong (elem-in-Lf (F₁ .carrier) x)))
          (⊑-trans ([]-cong (G .fmor-comp _ _))
          (⊑-trans ([]-comp⁻¹ _ _)
          (⊑-trans ((Rt-iso⁻ (elem-in (F₁ .carrier) x)
                             (λ _ → id _) (λ _ → id-left) (λ _ → id-left))
                      [ G .fmor (sing-Lf (F₁ .carrier) x) ]m)
                   ((++-isJoin .IsJoin.inr) [ G .fmor (sing-Lf (F₁ .carrier) x) ]m)))))))))))
        (⊑-trans (disjoint₁ x (sing-Lf (F₁ .carrier) x))
                 ((++-isJoin .IsJoin.inr) [ G .fmor (sing-Lf (F₁ .carrier) x) ]m)))
    node-inj₁ F₁ F₂ x .inv _ = id _
    node-inj₁ F₁ F₂ x .inv₁ _ = id-left
    node-inj₁ F₁ F₂ x .inv₂ _ = id-left

    node-inj₂ : ∀ (F₁ F₂ : Gl.Obj) (y : F₂ .carrier .idx .Carrier) →
                glue simple[ PS.𝟙 , L (F₂ .carrier .fam .fm y) ]
                     (((Lf-Gl F₁ .pred
                          ⟨ G .fmor (CP.in₁ {Lf (F₁ .carrier)} {Lf (F₂ .carrier)}) ⟩)
                        ++ (Lf-Gl F₂ .pred ⟨ G .fmor CP.in₂ ⟩))
                        [ G .fmor (elem-in (CP.coprod (Lf (F₁ .carrier)) (Lf (F₂ .carrier)))
                                           (inj₂ y)) ])
                  =>ᵢ Lf-Gl (glue simple[ PS.𝟙 , F₂ .carrier .fam .fm y ]
                                  (F₂ .pred [ G .fmor (elem-in (F₂ .carrier) y) ]))
    node-inj₂ F₁ F₂ y .mor .morph = sing-Lf (F₂ .carrier) y
    node-inj₂ F₁ F₂ y .mor .presv =
      ⊑-trans []-++
      (++-isJoin .IsJoin.[_,_]
        (⊑-trans (disjoint₂ y (sing-Lf (F₂ .carrier) y))
                 ((++-isJoin .IsJoin.inr) [ G .fmor (sing-Lf (F₂ .carrier) y) ]m))
        (⊑-trans ([]-cong (G .fmor-cong (elem-in-inj₂ (Lf (F₁ .carrier)) (Lf (F₂ .carrier)) y)))
        (⊑-trans ([]-cong (G .fmor-comp _ _))
        (⊑-trans ([]-comp⁻¹ _ _)
        (⊑-trans (in₂-extract [ G .fmor (elem-in (Lf (F₂ .carrier)) y) ]m)
        (⊑-trans []-++
        (++-isJoin .IsJoin.[_,_]
          (⊑-trans (BC-injF y)
          (⊑-trans (img-square-id (sing-Lf (F₂ .carrier) y) (sing-inj (F₂ .carrier) y)
                                  injF (injF-sing (F₂ .carrier) y))
                   ((++-isJoin .IsJoin.inl) [ G .fmor (sing-Lf (F₂ .carrier) y) ]m)))
          (⊑-trans ([]-cong (G .fmor-cong (elem-in-Lf (F₂ .carrier) y)))
          (⊑-trans ([]-cong (G .fmor-comp _ _))
          (⊑-trans ([]-comp⁻¹ _ _)
          (⊑-trans ((Rt-iso⁻ (elem-in (F₂ .carrier) y)
                             (λ _ → id _) (λ _ → id-left) (λ _ → id-left))
                      [ G .fmor (sing-Lf (F₂ .carrier) y) ]m)
                   ((++-isJoin .IsJoin.inr) [ G .fmor (sing-Lf (F₂ .carrier) y) ]m))))))))))))
    node-inj₂ F₁ F₂ y .inv _ = id _
    node-inj₂ F₁ F₂ y .inv₁ _ = id-left
    node-inj₂ F₁ F₂ y .inv₂ _ = id-left

    -- The node step at a product: the singleton at a pair index becomes the
    -- lifted product of the two singletons, through the pairing of the
    -- singleton inclusions under the payload injection.
    node-pair-mor : ∀ (F₁ F₂ : Gl.Obj) (x : F₁ .carrier .idx .Carrier)
                    (y : F₂ .carrier .idx .Carrier) →
                    Mor simple[ PS.𝟙 , L (prod (F₁ .carrier .fam .fm x)
                                               (F₂ .carrier .fam .fm y)) ]
                        (Lf (Fam𝒞-P.prod simple[ PS.𝟙 , F₁ .carrier .fam .fm x ]
                                         simple[ PS.𝟙 , F₂ .carrier .fam .fm y ]))
    node-pair-mor F₁ F₂ x y =
      Fam𝒞._∘_ (Lf-map (sing-pair (F₁ .carrier) (F₂ .carrier) x y))
               (sing-Lf (Fam𝒞-P.prod (F₁ .carrier) (F₂ .carrier)) (x , y))

    node-pair : ∀ (F₁ F₂ : Gl.Obj) (x : F₁ .carrier .idx .Carrier)
                (y : F₂ .carrier .idx .Carrier) →
                glue simple[ PS.𝟙 , L (prod (F₁ .carrier .fam .fm x) (F₂ .carrier .fam .fm y)) ]
                     ((((F₁ [×] F₂) .pred
                          ⟨ G .fmor (injF {Fam𝒞-P.prod (F₁ .carrier) (F₂ .carrier)}) ⟩)
                        ++ Rt (Fam𝒞-P.prod (F₁ .carrier) (F₂ .carrier)))
                        [ G .fmor (elem-in (Lf (Fam𝒞-P.prod (F₁ .carrier) (F₂ .carrier)))
                                           (x , y)) ])
                  =>ᵢ Lf-Gl (glue simple[ PS.𝟙 , F₁ .carrier .fam .fm x ]
                                  (F₁ .pred [ G .fmor (elem-in (F₁ .carrier) x) ])
                             [×] glue simple[ PS.𝟙 , F₂ .carrier .fam .fm y ]
                                  (F₂ .pred [ G .fmor (elem-in (F₂ .carrier) y) ]))
    node-pair F₁ F₂ x y .mor .morph = node-pair-mor F₁ F₂ x y
    node-pair F₁ F₂ x y .mor .presv =
      ⊑-trans []-++
      (++-isJoin .IsJoin.[_,_]
        (⊑-trans (BC-injF (x , y))
        (⊑-trans ((⊑-trans (&&-isMeet .IsMeet.⟨_,_⟩
                    (⊑-trans ((&&-isMeet .IsMeet.π₁)
                                [ G .fmor (elem-in (Fam𝒞-P.prod (F₁ .carrier) (F₂ .carrier))
                                                   (x , y)) ]m)
                    (⊑-trans ([]-comp _ _)
                    (⊑-trans ([]-cong (𝒫C.≈-sym (G .fmor-comp _ _)))
                    (⊑-trans ([]-cong (G .fmor-cong (p₁-sing (F₁ .carrier) (F₂ .carrier) x y)))
                    (⊑-trans ([]-cong (G .fmor-cong
                                (Fam𝒞.∘-cong Fam𝒞.≈-refl
                                  (Fam𝒞.≈-sym (p₁-pair (F₁ .carrier) (F₂ .carrier) x y)))))
                    (⊑-trans ([]-cong (G .fmor-comp _ _))
                    (⊑-trans ([]-comp⁻¹ _ _)
                    (⊑-trans ([]-cong (G .fmor-comp _ _))
                             ([]-comp⁻¹ _ _)))))))))
                    (⊑-trans ((&&-isMeet .IsMeet.π₂)
                                [ G .fmor (elem-in (Fam𝒞-P.prod (F₁ .carrier) (F₂ .carrier))
                                                   (x , y)) ]m)
                    (⊑-trans ([]-comp _ _)
                    (⊑-trans ([]-cong (𝒫C.≈-sym (G .fmor-comp _ _)))
                    (⊑-trans ([]-cong (G .fmor-cong (p₂-sing (F₁ .carrier) (F₂ .carrier) x y)))
                    (⊑-trans ([]-cong (G .fmor-cong
                                (Fam𝒞.∘-cong Fam𝒞.≈-refl
                                  (Fam𝒞.≈-sym (p₂-pair (F₁ .carrier) (F₂ .carrier) x y)))))
                    (⊑-trans ([]-cong (G .fmor-comp _ _))
                    (⊑-trans ([]-comp⁻¹ _ _)
                    (⊑-trans ([]-cong (G .fmor-comp _ _))
                             ([]-comp⁻¹ _ _))))))))))
                    []-&&)
                   ⟨ G .fmor (sing-inj (Fam𝒞-P.prod (F₁ .carrier) (F₂ .carrier)) (x , y)) ⟩m)
        (⊑-trans (img-square (node-pair-mor F₁ F₂ x y)
                             (sing-inj (Fam𝒞-P.prod (F₁ .carrier) (F₂ .carrier)) (x , y))
                             injF (sing-pair (F₁ .carrier) (F₂ .carrier) x y)
                             (injF-pair (F₁ .carrier) (F₂ .carrier) x y))
                 ((++-isJoin .IsJoin.inl) [ G .fmor (node-pair-mor F₁ F₂ x y) ]m))))
        (⊑-trans ([]-cong (G .fmor-cong
                    (elem-in-Lf (Fam𝒞-P.prod (F₁ .carrier) (F₂ .carrier)) (x , y))))
        (⊑-trans ([]-cong (G .fmor-comp _ _))
        (⊑-trans ([]-comp⁻¹ _ _)
        (⊑-trans ((Rt-iso⁻ (elem-in (Fam𝒞-P.prod (F₁ .carrier) (F₂ .carrier)) (x , y))
                           (λ _ → id _) (λ _ → id-left) (λ _ → id-left))
                    [ G .fmor (sing-Lf (Fam𝒞-P.prod (F₁ .carrier) (F₂ .carrier)) (x , y)) ]m)
        (⊑-trans ((Rt-iso (sing-pair (F₁ .carrier) (F₂ .carrier) x y)
                          (λ _ → id _) (λ _ → id-left) (λ _ → id-left))
                    [ G .fmor (sing-Lf (Fam𝒞-P.prod (F₁ .carrier) (F₂ .carrier)) (x , y)) ]m)
        (⊑-trans ([]-comp _ _)
        (⊑-trans ([]-cong (𝒫C.≈-sym (G .fmor-comp _ _)))
                 ((++-isJoin .IsJoin.inr)
                    [ G .fmor (node-pair-mor F₁ F₂ x y) ]m)))))))))
    node-pair F₁ F₂ x y .inv _ = id _
    node-pair F₁ F₂ x y .inv₁ _ =
      ≈-trans id-right (≈-trans id-left (≈-trans id-right Lmap-id))
    node-pair F₁ F₂ x y .inv₂ _ =
      ≈-trans id-left (≈-trans id-left (≈-trans id-right Lmap-id))

  -- The singleton of the one-step object at each index embeds into the fibre
  -- glued object at the embedded shape.
  embed-Gl : ∀ (Q : Poly (suc n)) (pQ : PolyPred Q)
             (i : R.fobj μObj Q δ' .idx .Carrier) →
             glue simple[ PS.𝟙 , R.fobj μObj Q δ' .fam .fm i ]
                  (fobj-Gl Q pQ δ' δP⁺ .pred
                     [ G .fmor (elem-in (R.fobj μObj Q δ') i) ])
               =>ᵢ M⁺.fib-shape-Gl Q (λ v → lift tt) pQ (λ v → lift tt) (embed-idx Q i)
  embed-Gl (const A) pA i = idᵢ
  embed-Gl (var v)   pQ i = idᵢ
  embed-Gl (Q₁ + Q₂) (pQ₁ , pQ₂) (inj₁ x) =
    Lf-Glᵢ' (embed-Gl Q₁ pQ₁ x)
      ∘ᵢ node-inj₁ (fobj-Gl Q₁ pQ₁ δ' δP⁺) (fobj-Gl Q₂ pQ₂ δ' δP⁺) x
  embed-Gl (Q₁ + Q₂) (pQ₁ , pQ₂) (inj₂ y) =
    Lf-Glᵢ' (embed-Gl Q₂ pQ₂ y)
      ∘ᵢ node-inj₂ (fobj-Gl Q₁ pQ₁ δ' δP⁺) (fobj-Gl Q₂ pQ₂ δ' δP⁺) y
  embed-Gl (Q₁ × Q₂) (pQ₁ , pQ₂) (x , y) =
    Lf-Glᵢ' ([×]ᵢ (embed-Gl Q₁ pQ₁ x) (embed-Gl Q₂ pQ₂ y))
      ∘ᵢ node-pair (fobj-Gl Q₁ pQ₁ δ' δP⁺) (fobj-Gl Q₂ pQ₂ δ' δP⁺) x y
  embed-Gl (μ Q')    pQ' t = sing-μ δ' δP⁺ Q' pQ' t

  -- The singleton embedding intertwines the carrier inclusions with the fibre
  -- bridge of the algebra map.
  embed-Gl-in : ∀ (Q : Poly (suc n)) (pQ : PolyPred Q)
                (i : R.fobj μObj Q δ' .idx .Carrier) (ι : PS.𝟙 {0ℓ} {0ℓ} .Carrier) →
                (M⁺.in-shape Q (λ v → lift tt) pQ (λ v → lift tt) (embed-idx Q i)
                   (embed-Gl Q pQ i .mor .morph .idxf .PS._⇒_.func ι)
                  ∘ embed-Gl Q pQ i .mor .morph .famf ._⇒f_.transf ι)
                ≈ embed-fam Q i
  embed-Gl-in (const A) pA i ι = id-left
  embed-Gl-in (var v)   pQ i ι = id-left
  embed-Gl-in (Q₁ + Q₂) (pQ₁ , pQ₂) (inj₁ x) ι =
    ≈-trans (∘-cong ≈-refl (≈-trans id-left id-right))
    (≈-trans (≈-sym (Lmap-comp _ _)) (Lmap-cong (embed-Gl-in Q₁ pQ₁ x ι)))
  embed-Gl-in (Q₁ + Q₂) (pQ₁ , pQ₂) (inj₂ y) ι =
    ≈-trans (∘-cong ≈-refl (≈-trans id-left id-right))
    (≈-trans (≈-sym (Lmap-comp _ _)) (Lmap-cong (embed-Gl-in Q₂ pQ₂ y ι)))
  embed-Gl-in (Q₁ × Q₂) (pQ₁ , pQ₂) (x , y) ι =
    ≈-trans (∘-cong ≈-refl
              (≈-trans id-left
                (≈-trans (∘-cong ≈-refl (≈-trans id-left (≈-trans id-right Lmap-id)))
                         id-right)))
    (≈-trans (∘-cong ≈-refl (Lmap-cong (pair-cong id-left id-left)))
    (≈-trans (≈-sym (Lmap-comp _ _))
             (Lmap-cong (≈-trans (≈-sym (prod-m-comp _ _ _ _))
                                 (prod-m-cong (embed-Gl-in Q₁ pQ₁ x ι)
                                              (embed-Gl-in Q₂ pQ₂ y ι))))))
  embed-Gl-in (μ Q')    pQ' t ι =
    M⁺.in-out-fib Q' (λ v → lift tt) pQ' (λ v → lift tt) t _

  -- The algebra map carries the one-step glued interpretation into the
  -- decorated μ-carrier: split into singletons, embed each singleton into its
  -- one-step fibre, reindex to the corresponding tree fibre, and land in that
  -- tree's disjunct of the closed join.
  inMap-Gl : fobj-Gl P pP δ' δP⁺ .pred ⊑ (Mδ.μ-Gl P pP .pred [ G .fmor inMor ])
  inMap-Gl =
    ⊑-trans sing-split
    (⊑-trans (𝐂-isClosure .IsClosureOp.mono
               (⋁-isJoin .IsBigJoin.least _ _ _
                 (λ i → ⊑-trans ((step i) ⟨ G .fmor (elem-in X₀ i) ⟩m)
                                (counit (G .fmor (elem-in X₀ i))))))
    (⊑-trans (𝐂-isClosure .IsClosureOp.mono 𝐂-[]⁻¹)
    (⊑-trans (𝐂-isClosure .IsClosureOp.closed) 𝐂-[])))
    where
      X₀ : Obj
      X₀ = R.fobj μObj P δ'

      t[_] : X₀ .idx .Carrier → Tδ.W ∣ P ∣ (λ i → inj₁ i)
      t[ i ] = Tδ.sup (RX.reindex-shape ∣ P ∣ mor₀ (embed-idx P i))

      re : ∀ (i : X₀ .idx .Carrier) →
           Mor simple[ PS.𝟙 , X₀ .fam .fm i ]
               (Mδ.fib-Gl P (λ v → lift tt) pP (λ v → lift tt) t[ i ] .carrier)
      re i = Fam𝒞._∘_ (GR.reindex-shape-Gl P pP pmd₀ (embed-idx P i) .mor .morph)
                      (embed-Gl P pP i .mor .morph)

      sq : ∀ (i : X₀ .idx .Carrier) →
           Fam𝒞._≈_ (Fam𝒞._∘_ (Mδ.tree-in P pP t[ i ]) (re i))
                    (Fam𝒞._∘_ inMor (elem-in X₀ i))
      sq i ._≃_.idxf-eq .PS._≃m_.func-eq _ = Tδ.W-≈-refl t[ i ]
      sq i ._≃_.famf-eq .indexed-family._≃f_.transf-eq {ι} =
        ≈-trans (∘-cong (Tδ.fib-refl* P (λ v → lift tt) t[ i ])
                        (≈-trans id-left (∘-cong ≈-refl id-left)))
        (≈-trans id-left
        (≈-trans (≈-sym (assoc _ _ _))
        (≈-trans (∘-cong (GR.reindex-shape-Gl-in P pP pmd₀ (embed-idx P i)
                            (embed-Gl P pP i .mor .morph .idxf .PS._⇒_.func ι))
                         ≈-refl)
        (≈-trans (assoc _ _ _)
        (≈-trans (∘-cong ≈-refl (embed-Gl-in P pP i ι))
                 (≈-sym (≈-trans id-left id-right)))))))

      step : ∀ (i : X₀ .idx .Carrier) →
             (fobj-Gl P pP δ' δP⁺ .pred [ G .fmor (elem-in X₀ i) ])
               ⊑ ((Mδ.μ-Gl P pP .pred [ G .fmor inMor ]) [ G .fmor (elem-in X₀ i) ])
      step i =
        ⊑-trans (embed-Gl P pP i .mor .presv)
        (⊑-trans ((GR.reindex-shape-Gl P pP pmd₀ (embed-idx P i) .mor .presv)
                    [ G .fmor (embed-Gl P pP i .mor .morph) ]m)
        (⊑-trans ([]-comp _ _)
        (⊑-trans ([]-cong (𝒫C.≈-sym (G .fmor-comp _ _)))
        (⊑-trans ((unit (G .fmor (Mδ.tree-in P pP t[ i ]))) [ G .fmor (re i) ]m)
        (⊑-trans ([]-comp _ _)
        (⊑-trans ([]-cong (𝒫C.≈-sym (G .fmor-comp _ _)))
        (⊑-trans ([]-cong (G .fmor-cong (sq i)))
        (⊑-trans ((⊑-trans (⋁-isJoin .IsBigJoin.upper _ _ t[ i ])
                           (𝐂-isClosure .IsClosureOp.unit))
                    [ G .fmor (Fam𝒞._∘_ inMor (elem-in X₀ i)) ]m)
        (⊑-trans ([]-cong (G .fmor-comp _ _))
                 ([]-comp⁻¹ _ _))))))))))
