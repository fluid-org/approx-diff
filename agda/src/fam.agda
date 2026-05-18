{-# OPTIONS --prop --postfix-projections --safe #-}

module fam where

open import Level using (_⊔_; suc; lift)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; Σ-syntax)
open import prop using (_,_; tt; ∃ₚ; ⟪_⟫)
open import prop-setoid
  using (IsEquivalence; Setoid; 𝟙; +-setoid; ⊗-setoid; idS; _∘S_; module ≈-Reasoning)
  renaming (_⇒_ to _⇒s_; _≃m_ to _≈s_; ≃m-isEquivalence to ≈s-isEquivalence)
open import categories
  using (Category; HasTerminal; IsTerminal; HasCoproducts; HasProducts; HasStrongCoproducts; setoid→category)
open import polynomial-functor using (Poly; HasMu; poly-obj)
open import setoid-cat using (Setoid-products)
open import indexed-family
  using (Fam; _⇒f_; idf; _∘f_; ∘f-cong; _≃f_; ≃f-isEquivalence; ≃f-id-left; ≃f-assoc;
         _[_]; reindex-≈; reindex-≈-refl; reindex-≈-trans; reindex-id; reindex-comp; reindex-f;
         reindex-comp-≈; reindex-f-comp; reindex-f-cong; reindex-sq;
         reindex-id-left; reindex-id-right; reindex-id-natural; reindex-assoc; reindex-comp-natural;
         constantFam)

open IsEquivalence

-- Categories of Families, a special case of the Grothendieck
-- construction
--
-- FIXME: re-do this in terms of displayed categories
--
-- FIXME: try to re-do as much as possible in terms of reindexing, so
-- it can be used for any indexed category
module CategoryOfFamilies {o m e} os es (𝒞 : Category o m e) where

  open Fam public

  record Obj : Set (o ⊔ m ⊔ e ⊔ suc es ⊔ suc os) where
    no-eta-equality
    field
      idx : Setoid os es
      fam : Fam idx 𝒞
  open Obj

  record Mor (X Y : Obj) : Set (os ⊔ es ⊔ m ⊔ e) where
    no-eta-equality
    field
      idxf : X .idx ⇒s Y .idx
      famf : X .fam ⇒f (Y .fam [ idxf ])
  open Mor

  record _≃_ {X Y : Obj} (f g : Mor X Y) : Prop (os ⊔ es ⊔ m ⊔ e) where
    no-eta-equality
    field
      idxf-eq : f .idxf ≈s g .idxf
      famf-eq : (reindex-≈ _ _ idxf-eq ∘f f .famf) ≃f g .famf
  open _≃_

  ≃f-refl : ∀ {A : Setoid os es} {x y : Fam A 𝒞} {f : x ⇒f y} → f ≃f f
  ≃f-refl = ≃f-isEquivalence .refl

  ≃-isEquivalence : ∀ {X Y} → IsEquivalence (_≃_ {X} {Y})
  ≃-isEquivalence .refl .idxf-eq = ≈s-isEquivalence .refl
  ≃-isEquivalence {X} {Y} .refl {f} .famf-eq =
    begin
      reindex-≈ (f .idxf) (f .idxf) (≈s-isEquivalence .refl) ∘f f .famf
    ≈⟨ ∘f-cong (reindex-≈-refl (f .idxf)) ≃f-refl ⟩
      idf (Y .fam [ f .idxf ]) ∘f f .famf
    ≈⟨ ≃f-id-left ⟩
      f .famf
    ∎ where open ≈-Reasoning ≃f-isEquivalence
  ≃-isEquivalence .sym f≈g .idxf-eq = ≈s-isEquivalence .sym (f≈g .idxf-eq)
  ≃-isEquivalence {X} {Y} .sym {f}{g} f≈g .famf-eq =
    begin
      reindex-≈ (g .idxf) (f .idxf) (≈s-isEquivalence .sym (f≈g .idxf-eq)) ∘f g .famf
    ≈⟨ ∘f-cong (≃f-isEquivalence .refl {reindex-≈ (g .idxf) (f .idxf) (≈s-isEquivalence .sym (f≈g .idxf-eq))}) (≃f-isEquivalence .sym (f≈g .famf-eq)) ⟩
      reindex-≈ (g .idxf) (f .idxf) (≈s-isEquivalence .sym (f≈g .idxf-eq)) ∘f (reindex-≈ (f .idxf) (g .idxf) (f≈g .idxf-eq) ∘f f .famf)
    ≈⟨ ≃f-isEquivalence .sym (≃f-assoc _ _ _) ⟩
      (reindex-≈ (g .idxf) (f .idxf) (≈s-isEquivalence .sym (f≈g .idxf-eq)) ∘f reindex-≈ (f .idxf) (g .idxf) (f≈g .idxf-eq)) ∘f f .famf
    ≈⟨ ∘f-cong (≃f-isEquivalence .sym (reindex-≈-trans _ _)) ≃f-refl ⟩
      reindex-≈ (f .idxf) _ (≈s-isEquivalence .refl) ∘f f .famf
    ≈⟨ ∘f-cong (reindex-≈-refl (f .idxf)) ≃f-refl ⟩
      idf (Y .fam [ f .idxf ]) ∘f f .famf
    ≈⟨ ≃f-id-left ⟩
      f .famf
    ∎ where open ≈-Reasoning ≃f-isEquivalence
  ≃-isEquivalence .trans f≈g g≈h .idxf-eq = ≈s-isEquivalence .trans (f≈g .idxf-eq) (g≈h .idxf-eq)
  ≃-isEquivalence {X} {Y} .trans {f}{g}{h} f≈g g≈h .famf-eq =
    begin
      reindex-≈ (f .idxf) (h .idxf) _ ∘f f .famf
    ≈⟨ ∘f-cong (reindex-≈-trans (f≈g .idxf-eq) (g≈h .idxf-eq)) ≃f-refl ⟩
      (reindex-≈ _ _ (g≈h .idxf-eq) ∘f reindex-≈ _ _ (f≈g .idxf-eq)) ∘f f .famf
    ≈⟨ ≃f-assoc _ _ _ ⟩
      reindex-≈ _ _ (g≈h .idxf-eq) ∘f (reindex-≈ _ _ (f≈g .idxf-eq) ∘f f .famf)
    ≈⟨ ∘f-cong ≃f-refl (f≈g .famf-eq) ⟩
      reindex-≈ _ _ (g≈h .idxf-eq) ∘f g .famf
    ≈⟨ g≈h .famf-eq ⟩
      h .famf
    ∎ where open ≈-Reasoning ≃f-isEquivalence

  module _ where

    open Category 𝒞

    Mor-id : ∀ X → Mor X X
    Mor-id X .idxf = idS _
    Mor-id X .famf = reindex-id

    Mor-∘ : ∀ {X Y Z} → Mor Y Z → Mor X Y → Mor X Z
    Mor-∘ f g .idxf = f .idxf ∘S g .idxf
    Mor-∘ f g .famf = reindex-comp ∘f (reindex-f (g .idxf) (f .famf) ∘f (g .famf))

    open _≃_

    Mor-∘-cong : ∀ {X Y Z}{f₁ f₂ : Mor Y Z}{g₁ g₂ : Mor X Y} → f₁ ≃ f₂ → g₁ ≃ g₂ → Mor-∘ f₁ g₁ ≃ Mor-∘ f₂ g₂
    Mor-∘-cong f₁≃f₂ g₁≃g₂ .idxf-eq = prop-setoid.∘S-cong (f₁≃f₂ .idxf-eq) (g₁≃g₂ .idxf-eq)
    Mor-∘-cong {X}{Y}{Z} {f₁}{f₂}{g₁}{g₂} f₁≃f₂ g₁≃g₂ .famf-eq =
      begin
        reindex-≈ _ _ _ ∘f (reindex-comp ∘f (reindex-f (g₁ .idxf) (f₁ .famf) ∘f g₁ .famf))
      ≈˘⟨ ≃f-assoc _ _ _ ⟩
        (reindex-≈ _ _ _ ∘f reindex-comp) ∘f (reindex-f (g₁ .idxf) (f₁ .famf) ∘f g₁ .famf)
      ≈⟨ ∘f-cong (reindex-comp-≈ (Z .fam) (f₁≃f₂ .idxf-eq) (g₁≃g₂ .idxf-eq)) ≃f-refl ⟩
        (reindex-comp ∘f (reindex-≈ _ _ _ ∘f reindex-f _ (reindex-≈ _ _ _))) ∘f (reindex-f (g₁ .idxf) (f₁ .famf) ∘f g₁ .famf)
      ≈⟨ ≃f-assoc _ _ _ ⟩
        reindex-comp ∘f ((reindex-≈ _ _ (g₁≃g₂ .idxf-eq) ∘f reindex-f _ (reindex-≈ _ _ (f₁≃f₂ .idxf-eq))) ∘f (reindex-f (g₁ .idxf) (f₁ .famf) ∘f g₁ .famf))
      ≈⟨ ∘f-cong ≃f-refl (≃f-assoc _ _ _) ⟩
        reindex-comp ∘f (reindex-≈ _ _ (g₁≃g₂ .idxf-eq) ∘f (reindex-f _ (reindex-≈ _ _ (f₁≃f₂ .idxf-eq)) ∘f (reindex-f (g₁ .idxf) (f₁ .famf) ∘f g₁ .famf)))
      ≈˘⟨ ∘f-cong ≃f-refl (∘f-cong ≃f-refl (≃f-assoc _ _ _)) ⟩
        reindex-comp ∘f (reindex-≈ _ _ (g₁≃g₂ .idxf-eq) ∘f ((reindex-f _ (reindex-≈ _ _ (f₁≃f₂ .idxf-eq)) ∘f reindex-f (g₁ .idxf) (f₁ .famf)) ∘f g₁ .famf))
      ≈⟨ ∘f-cong ≃f-refl (∘f-cong ≃f-refl (∘f-cong (reindex-f-comp _ _) ≃f-refl)) ⟩
        reindex-comp ∘f (reindex-≈ _ _ (g₁≃g₂ .idxf-eq) ∘f (reindex-f _ (reindex-≈ _ _ (f₁≃f₂ .idxf-eq) ∘f f₁ .famf) ∘f g₁ .famf))
      ≈⟨ ∘f-cong ≃f-refl (∘f-cong ≃f-refl (∘f-cong (reindex-f-cong (f₁≃f₂ .famf-eq)) ≃f-refl)) ⟩
        reindex-comp ∘f (reindex-≈ _ _ (g₁≃g₂ .idxf-eq) ∘f (reindex-f _ (f₂ .famf) ∘f g₁ .famf))
      ≈˘⟨ ∘f-cong ≃f-refl (≃f-assoc _ _ _) ⟩
        reindex-comp ∘f ((reindex-≈ _ _ (g₁≃g₂ .idxf-eq) ∘f reindex-f _ (f₂ .famf)) ∘f g₁ .famf)
      ≈˘⟨ ∘f-cong ≃f-refl (∘f-cong (reindex-sq _ _) ≃f-refl) ⟩
        reindex-comp ∘f ((reindex-f _ (f₂ .famf) ∘f reindex-≈ _ _ (g₁≃g₂ .idxf-eq)) ∘f g₁ .famf)
      ≈⟨ ∘f-cong ≃f-refl (≃f-assoc _ _ _) ⟩
        reindex-comp ∘f (reindex-f _ (f₂ .famf) ∘f (reindex-≈ _ _ (g₁≃g₂ .idxf-eq) ∘f g₁ .famf))
      ≈⟨ ∘f-cong ≃f-refl (∘f-cong ≃f-refl (g₁≃g₂ .famf-eq)) ⟩
        reindex-comp ∘f (reindex-f (g₂ .idxf) (f₂ .famf) ∘f g₂ .famf)
      ∎
      where open ≈-Reasoning ≃f-isEquivalence

  module _ where
    open Category
    open IsEquivalence
    private module 𝒞 = Category 𝒞

    cat : Category (o ⊔ m ⊔ e ⊔ suc es ⊔ suc os) (os ⊔ es ⊔ m ⊔ e) (e ⊔ es ⊔ m ⊔ os)
    cat .obj = Obj
    cat ._⇒_ = Mor
    cat ._≈_ = _≃_
    cat .isEquiv = ≃-isEquivalence
    cat .id = Mor-id
    cat ._∘_ = Mor-∘
    cat .∘-cong = Mor-∘-cong
    cat .id-left .idxf-eq = prop-setoid.id-left
    cat .id-left {X} {Y} {f} .famf-eq = begin
        reindex-≈ (idS (Y .idx) ∘S f .idxf) (f .idxf) _ ∘f (reindex-comp ∘f (reindex-f (f .idxf) reindex-id ∘f f .famf))
      ≈˘⟨ ≃f-assoc _ _ _ ⟩
        (reindex-≈ (idS (Y .idx) ∘S f .idxf) (f .idxf) _ ∘f reindex-comp) ∘f (reindex-f (f .idxf) reindex-id ∘f f .famf)
      ≈˘⟨ ≃f-assoc _ _ _ ⟩
        ((reindex-≈ (idS (Y .idx) ∘S f .idxf) (f .idxf) _ ∘f reindex-comp) ∘f reindex-f (f .idxf) reindex-id) ∘f f .famf
      ≈⟨ ∘f-cong (reindex-id-left (f .idxf)) ≃f-refl ⟩
        idf _ ∘f f .famf
      ≈⟨ ≃f-id-left ⟩
        f .famf
      ∎
      where open ≈-Reasoning ≃f-isEquivalence
    cat .id-right .idxf-eq = prop-setoid.id-right
    cat .id-right {X}{Y}{f} .famf-eq = begin
        reindex-≈ (f .idxf ∘S idS (X .idx)) (f .idxf) _ ∘f (reindex-comp ∘f (reindex-f (idS (X .idx)) (f .famf) ∘f reindex-id))
      ≈⟨ ∘f-cong ≃f-refl (∘f-cong ≃f-refl (reindex-id-natural (f .famf))) ⟩
        reindex-≈ (f .idxf ∘S idS (X .idx)) (f .idxf) _ ∘f (reindex-comp ∘f (reindex-id ∘f f .famf))
      ≈˘⟨ ≃f-assoc _ _ _ ⟩
        (reindex-≈ (f .idxf ∘S idS (X .idx)) (f .idxf) _ ∘f reindex-comp) ∘f (reindex-id ∘f f .famf)
      ≈˘⟨ ≃f-assoc _ _ _ ⟩
        ((reindex-≈ (f .idxf ∘S idS (X .idx)) (f .idxf) _ ∘f reindex-comp) ∘f reindex-id) ∘f f .famf
      ≈⟨ ∘f-cong (reindex-id-right (f .idxf)) ≃f-refl ⟩
        idf _ ∘f f .famf
      ≈⟨ ≃f-id-left ⟩
        f .famf
      ∎ where open ≈-Reasoning ≃f-isEquivalence
    cat .assoc f g h .idxf-eq = prop-setoid.assoc (f .idxf) (g .idxf) (h .idxf)
    cat .assoc {W}{X}{Y}{Z} f g h .famf-eq = begin
        reindex-≈ ((f .idxf ∘S g .idxf) ∘S h .idxf) (f .idxf ∘S (g .idxf ∘S h .idxf)) _ ∘f (reindex-comp ∘f (reindex-f (h .idxf) (reindex-comp ∘f (reindex-f (g .idxf) (f .famf) ∘f g .famf)) ∘f h .famf))
      ≈˘⟨ ≃f-assoc _ _ _ ⟩
        (reindex-≈ ((f .idxf ∘S g .idxf) ∘S h .idxf) (f .idxf ∘S (g .idxf ∘S h .idxf)) _ ∘f reindex-comp) ∘f ((reindex-f (h .idxf) (reindex-comp ∘f (reindex-f (g .idxf) (f .famf) ∘f g .famf))) ∘f h .famf)
      ≈˘⟨ ≃f-assoc _ _ _ ⟩
        ((reindex-≈ ((f .idxf ∘S g .idxf) ∘S h .idxf) (f .idxf ∘S (g .idxf ∘S h .idxf)) _ ∘f reindex-comp) ∘f (reindex-f (h .idxf) (reindex-comp ∘f (reindex-f (g .idxf) (f .famf) ∘f g .famf)))) ∘f h .famf
      ≈˘⟨ ∘f-cong (∘f-cong ≃f-refl (reindex-f-comp _ _)) ≃f-refl ⟩
        ((reindex-≈ ((f .idxf ∘S g .idxf) ∘S h .idxf) (f .idxf ∘S (g .idxf ∘S h .idxf)) _ ∘f reindex-comp) ∘f (reindex-f (h .idxf) reindex-comp ∘f reindex-f (h .idxf) (reindex-f (g .idxf) (f .famf) ∘f g .famf))) ∘f h .famf
      ≈˘⟨ ∘f-cong (≃f-assoc _ _ _) ≃f-refl ⟩
        (((reindex-≈ ((f .idxf ∘S g .idxf) ∘S h .idxf) (f .idxf ∘S (g .idxf ∘S h .idxf)) _ ∘f reindex-comp) ∘f reindex-f (h .idxf) reindex-comp) ∘f reindex-f (h .idxf) (reindex-f (g .idxf) (f .famf) ∘f g .famf)) ∘f h .famf
      ≈⟨ ∘f-cong (∘f-cong (reindex-assoc _ _ _) ≃f-refl) ≃f-refl ⟩
        ((reindex-comp ∘f reindex-comp) ∘f reindex-f (h .idxf) (reindex-f (g .idxf) (f .famf) ∘f g .famf)) ∘f h .famf
      ≈˘⟨ ∘f-cong (∘f-cong ≃f-refl (reindex-f-comp _ _)) ≃f-refl ⟩
        ((reindex-comp ∘f reindex-comp) ∘f (reindex-f (h .idxf) (reindex-f (g .idxf) (f .famf)) ∘f reindex-f (h .idxf) (g .famf))) ∘f h .famf
      ≈⟨ ∘f-cong (≃f-assoc _ _ _) ≃f-refl ⟩
        (reindex-comp ∘f (reindex-comp ∘f (reindex-f (h .idxf) (reindex-f (g .idxf) (f .famf)) ∘f reindex-f (h .idxf) (g .famf)))) ∘f h .famf
      ≈⟨ ≃f-assoc _ _ _ ⟩
        reindex-comp ∘f (((reindex-comp ∘f (reindex-f (h .idxf) (reindex-f (g .idxf) (f .famf)) ∘f reindex-f (h .idxf) (g .famf)))) ∘f h .famf)
      ≈˘⟨ ∘f-cong ≃f-refl (∘f-cong (≃f-assoc _ _ _) ≃f-refl) ⟩
        reindex-comp ∘f (((reindex-comp ∘f reindex-f (h .idxf) (reindex-f (g .idxf) (f .famf))) ∘f reindex-f (h .idxf) (g .famf)) ∘f h .famf)
      ≈⟨ ∘f-cong ≃f-refl (∘f-cong (∘f-cong (reindex-comp-natural _ _ _) ≃f-refl) ≃f-refl) ⟩
        reindex-comp ∘f (((reindex-f (g .idxf ∘S h .idxf) (f .famf) ∘f reindex-comp) ∘f reindex-f (h .idxf) (g .famf)) ∘f h .famf)
      ≈⟨ ∘f-cong ≃f-refl (≃f-assoc _ _ _) ⟩
        reindex-comp ∘f ((reindex-f (g .idxf ∘S h .idxf) (f .famf) ∘f reindex-comp) ∘f (reindex-f (h .idxf) (g .famf) ∘f h .famf))
      ≈⟨ ∘f-cong ≃f-refl (≃f-assoc _ _ _) ⟩
        reindex-comp ∘f (reindex-f (g .idxf ∘S h .idxf) (f .famf) ∘f (reindex-comp ∘f (reindex-f (h .idxf) (g .famf) ∘f h .famf)))
      ∎  where open ≈-Reasoning ≃f-isEquivalence

  -- Simple objects, where there is no dependency
  module _ where
    open Category 𝒞

    simple[_,_] : Setoid _ _ → obj → Obj
    simple[ A , x ] .idx = A
    simple[ A , x ] .fam = constantFam A 𝒞 x

    simplef[_,_] : ∀ {A B x y} → A ⇒s B → x ⇒ y → Mor simple[ A , x ] simple[ B , y ]
    simplef[ f , g ] .idxf = f
    simplef[ f , g ] .famf ._⇒f_.transf x = g
    simplef[ f , g ] .famf ._⇒f_.natural _ = ≈-sym id-swap

    -- FIXME: simple is a functor and preserves products

  -- If 𝒞 has a terminal object, then so does the category of families
  module _ (T : HasTerminal 𝒞) where
    open HasTerminal hiding (to-terminal-unique)
    open IsTerminal
    open IsEquivalence

    -- FIXME: try to do this without breaking the abstraction of
    -- Fam(X). Need to know that every fibre of the indexed category
    -- has a terminal object, and that reindexing preserves them.
    terminal : HasTerminal cat
    terminal .witness = simple[ 𝟙 , T .witness ]
    terminal .is-terminal .to-terminal .idxf = prop-setoid.to-𝟙
    terminal .is-terminal .to-terminal .famf ._⇒f_.transf _ = T .is-terminal .to-terminal
    terminal .is-terminal .to-terminal .famf ._⇒f_.natural _ = to-terminal-unique (T .is-terminal) _ _
    terminal .is-terminal .to-terminal-ext f .idxf-eq = prop-setoid.to-𝟙-unique _ _
    terminal .is-terminal .to-terminal-ext f .famf-eq ._≃f_.transf-eq = to-terminal-unique (T .is-terminal) _ _

  -- This category always has coproducts, because it is the free
  -- co-product completion.
  module _ where

    open Category 𝒞
    open HasCoproducts
    open IsEquivalence
    open _⇒f_
    open _≃f_

    coproducts : HasCoproducts cat
    coproducts .coprod X Y .idx = +-setoid (X .idx) (Y .idx)
    coproducts .coprod X Y .fam .fm (inj₁ x) = X .fam .fm x
    coproducts .coprod X Y .fam .fm (inj₂ y) = Y .fam .fm y
    coproducts .coprod X Y .fam .subst {inj₁ x} {inj₁ x₁} = X .fam .subst
    coproducts .coprod X Y .fam .subst {inj₂ y} {inj₂ y₁} = Y .fam .subst
    coproducts .coprod X Y .fam .refl* {inj₁ x} = X .fam .refl*
    coproducts .coprod X Y .fam .refl* {inj₂ y} = Y .fam .refl*
    coproducts .coprod X Y .fam .trans* {inj₁ x} {inj₁ x₁} {inj₁ x₂} = X .fam .trans*
    coproducts .coprod X Y .fam .trans* {inj₂ y} {inj₂ y₁} {inj₂ y₂} = Y .fam .trans*
    coproducts .in₁ .idxf = prop-setoid.inject₁
    coproducts .in₁ .famf .transf x = id _
    coproducts .in₁ .famf .natural e = isEquiv .trans id-left (≈-sym id-right)
    coproducts .in₂ .idxf = prop-setoid.inject₂
    coproducts .in₂ .famf .transf x = id _
    coproducts .in₂ .famf .natural e = isEquiv .trans id-left (≈-sym id-right)
    coproducts .copair f g .idxf = prop-setoid.copair (f .idxf) (g .idxf)
    coproducts .copair f g .famf .transf (inj₁ x) = f .famf .transf x
    coproducts .copair f g .famf .transf (inj₂ y) = g .famf .transf y
    coproducts .copair f g .famf .natural {inj₁ x} {inj₁ x₁} = f .famf .natural
    coproducts .copair f g .famf .natural {inj₂ y} {inj₂ y₁} = g .famf .natural
    coproducts .copair-cong f₁≈f₂ g₁≈g₂ .idxf-eq = prop-setoid.copair-cong (f₁≈f₂ .idxf-eq) (g₁≈g₂ .idxf-eq)
    coproducts .copair-cong f₁≈f₂ g₁≈g₂ .famf-eq .transf-eq {inj₁ x} = f₁≈f₂ .famf-eq .transf-eq
    coproducts .copair-cong f₁≈f₂ g₁≈g₂ .famf-eq .transf-eq {inj₂ y} = g₁≈g₂ .famf-eq .transf-eq
    coproducts .copair-in₁ f g .idxf-eq = prop-setoid.copair-in₁ (f .idxf) (g .idxf)
    coproducts .copair-in₁ {X} {Y} {Z} f g .famf-eq .transf-eq {x} =
      begin
        Z .fam .subst _ ∘ (id _ ∘ (f .famf .transf x ∘ id _))
      ≈⟨ ∘-cong ≈-refl id-left ⟩
        Z .fam .subst _ ∘ (f .famf .transf x ∘ id _)
      ≈⟨ ∘-cong (Z .fam .refl*) id-right ⟩
        id _ ∘ f .famf .transf x
      ≈⟨ id-left ⟩
        f .famf .transf x
      ∎ where open ≈-Reasoning isEquiv
    coproducts .copair-in₂ f g .idxf-eq = prop-setoid.copair-in₂ (f .idxf) (g .idxf)
    coproducts .copair-in₂ {X} {Y} {Z} f g .famf-eq .transf-eq {x} =
      begin
        Z .fam .subst _ ∘ (id _ ∘ (g .famf .transf x ∘ id _))
      ≈⟨ ∘-cong ≈-refl id-left ⟩
        Z .fam .subst _ ∘ (g .famf .transf x ∘ id _)
      ≈⟨ ∘-cong (Z .fam .refl*) id-right ⟩
        id _ ∘ g .famf .transf x
      ≈⟨ id-left ⟩
        g .famf .transf x
      ∎ where open ≈-Reasoning isEquiv
    coproducts .copair-ext f .idxf-eq = prop-setoid.copair-ext (f .idxf)
    coproducts .copair-ext {X} {Y} {Z} f .famf-eq .transf-eq {inj₁ x} =
      isEquiv .trans (∘-cong (Z .fam .refl*) id-left) (isEquiv .trans id-left id-right)
    coproducts .copair-ext {X} {Y} {Z} f .famf-eq .transf-eq {inj₂ y} =
      isEquiv .trans (∘-cong (Z .fam .refl*) id-left) (isEquiv .trans id-left id-right)

  -- Fam(𝒞) is discretely cocomplete
  module _ where

    open import functor using (Functor; Colimit; HasColimits; IsColimit; NatTrans; ≃-NatTrans)
    open Category 𝒞
    open Functor
    open NatTrans
    open ≃-NatTrans
    open Colimit
    open IsColimit
    open Setoid
    open _⇒s_
    open _⇒f_
    open _≈s_
    open _≃f_
    open Mor

    bigCoproducts : ∀ (S : Setoid os es) → HasColimits (setoid→category S) cat
    bigCoproducts S D .apex .idx .Setoid.Carrier = Σ[ s ∈ S .Carrier ] D .fobj s .idx .Setoid.Carrier
    bigCoproducts S D .apex .idx ._≈_ (s₁ , x₁) (s₂ , x₂) =
      ∃ₚ (S ._≈_ s₁ s₂) λ s₁≈s₂ → D .fobj s₂ .idx ._≈_ (D .fmor ⟪ s₁≈s₂ ⟫ .idxf .func x₁) x₂
    bigCoproducts S D .apex .idx .isEquivalence .refl {s , x} =
      S .refl ,
      D .fmor-id .idxf-eq .func-eq (D .fobj s .idx .refl)
    bigCoproducts S D .apex .idx .isEquivalence .sym {s₁ , x₁} {s₂ , x₂} (s₁≈s₂ , x₁≈x₂) =
      S .sym s₁≈s₂ ,
      (begin
        D .fmor ⟪ _ ⟫ .idxf .func x₂
      ≈⟨ D .fmor ⟪ S .sym s₁≈s₂ ⟫ .idxf .func-resp-≈ (D .fobj s₂ .idx .sym x₁≈x₂) ⟩
        D .fmor ⟪ _ ⟫ .idxf .func (D .fmor ⟪ _ ⟫ .idxf .func x₁)
      ≈˘⟨ D .fmor-comp _ _ .idxf-eq .func-eq (D .fobj s₁ .idx .refl) ⟩
        D .fmor ⟪ _ ⟫ .idxf .func x₁
      ≈⟨ D .fmor-id .idxf-eq .func-eq (D .fobj s₁ .idx .refl) ⟩
        x₁
      ∎)
      where open ≈-Reasoning (D .fobj s₁ .idx .isEquivalence)
    bigCoproducts S D .apex .idx .isEquivalence .trans {s₁ , x₁} {s₂ , x₂} {s₃ , x₃} (s₁≈s₂ , x₁≈x₂) (s₂≈s₃ , x₂≈x₃) =
      S .trans s₁≈s₂ s₂≈s₃ ,
      (begin
        D .fmor ⟪ _ ⟫ .idxf .func x₁
      ≈⟨ D .fmor-comp _ _ .idxf-eq .func-eq (D .fobj s₁ .idx .refl) ⟩
        D .fmor ⟪ _ ⟫ .idxf .func (D .fmor ⟪ _ ⟫ .idxf .func x₁)
      ≈⟨ D .fmor ⟪ _ ⟫ .idxf .func-resp-≈ x₁≈x₂ ⟩
        D .fmor ⟪ _ ⟫ .idxf .func x₂
      ≈⟨ x₂≈x₃ ⟩
        x₃
      ∎)
      where open ≈-Reasoning (D .fobj s₃ .idx .isEquivalence)
    bigCoproducts S D .apex .fam .fm (s , x) = D .fobj s .fam .fm x
    bigCoproducts S D .apex .fam .subst {s₁ , x₁} {s₂ , x₂} (s₁≈s₂ , x₁≈x₂) =
      D .fobj s₂ .fam .subst x₁≈x₂ ∘ D .fmor ⟪ s₁≈s₂ ⟫ .famf .transf x₁
    bigCoproducts S D .apex .fam .refl* {s , x} = D .fmor-id {s} .famf-eq .transf-eq {x}
    bigCoproducts S D .apex .fam .trans* {s₁ , x₁} {s₂ , x₂} {s₃ , x₃} (s₂≈s₃ , x₂≈x₃) (s₁≈s₂ , x₁≈x₂) =
      begin
        D .fobj s₃ .fam .subst _ ∘ D .fmor ⟪ _ ⟫ .famf .transf x₁
      ≈⟨ ∘-cong (D .fobj s₃ .fam .trans* x₂≈x₃ (D .fobj s₃ .idx .trans (D .fmor-comp _ _ .idxf-eq .func-eq (D .fobj s₁ .idx .refl)) (D .fmor ⟪ s₂≈s₃ ⟫ .idxf .func-resp-≈ x₁≈x₂))) ≈-refl ⟩
        (D .fobj s₃ .fam .subst _ ∘ D .fobj s₃ .fam .subst _) ∘ D .fmor ⟪ _ ⟫ .famf .transf x₁
      ≈⟨ assoc _ _ _  ⟩
        D .fobj s₃ .fam .subst _ ∘ (D .fobj s₃ .fam .subst _ ∘ D .fmor ⟪ _ ⟫ .famf .transf x₁)
      ≈⟨ ∘-cong ≈-refl (∘-cong (D .fobj s₃ .fam .trans* _ _) ≈-refl) ⟩
        D .fobj s₃ .fam .subst _ ∘ ((D .fobj s₃ .fam .subst _ ∘ D .fobj s₃ .fam .subst _) ∘ D .fmor ⟪ _ ⟫ .famf .transf x₁)
      ≈⟨ ∘-cong ≈-refl (assoc _ _ _) ⟩
        D .fobj s₃ .fam .subst _ ∘ (D .fobj s₃ .fam .subst _ ∘ (D .fobj s₃ .fam .subst _ ∘ D .fmor ⟪ _ ⟫ .famf .transf x₁))
      ≈⟨ ∘-cong ≈-refl (∘-cong ≈-refl (D .fmor-comp ⟪ s₂≈s₃ ⟫ ⟪ s₁≈s₂ ⟫ .famf-eq .transf-eq {x₁})) ⟩
        D .fobj s₃ .fam .subst _ ∘ (D .fobj s₃ .fam .subst _ ∘ (id _ ∘ (D .fmor ⟪ _ ⟫ .famf .transf (D .fmor ⟪ _ ⟫ .idxf .func x₁) ∘ D .fmor ⟪ _ ⟫ .famf .transf x₁)))
      ≈⟨ ∘-cong ≈-refl (∘-cong ≈-refl id-left) ⟩
        D .fobj s₃ .fam .subst _ ∘ (D .fobj s₃ .fam .subst _ ∘ (D .fmor ⟪ _ ⟫ .famf .transf (D .fmor ⟪ _ ⟫ .idxf .func x₁) ∘ D .fmor ⟪ _ ⟫ .famf .transf x₁))
      ≈˘⟨ ∘-cong ≈-refl (assoc _ _ _) ⟩
        D .fobj s₃ .fam .subst _ ∘ ((D .fobj s₃ .fam .subst _ ∘ D .fmor ⟪ _ ⟫ .famf .transf (D .fmor ⟪ _ ⟫ .idxf .func x₁)) ∘ D .fmor ⟪ _ ⟫ .famf .transf x₁)
      ≈˘⟨ ∘-cong ≈-refl (∘-cong (D .fmor ⟪ s₂≈s₃ ⟫ .famf .natural x₁≈x₂) ≈-refl) ⟩
        D .fobj s₃ .fam .subst _ ∘ ((D .fmor ⟪ _ ⟫ .famf .transf x₂ ∘ D .fobj s₂ .fam .subst _) ∘ D .fmor ⟪ _ ⟫ .famf .transf x₁)
      ≈⟨ ∘-cong ≈-refl (assoc _ _ _) ⟩
        D .fobj s₃ .fam .subst _ ∘ (D .fmor ⟪ _ ⟫ .famf .transf x₂ ∘ (D .fobj s₂ .fam .subst _ ∘ D .fmor ⟪ _ ⟫ .famf .transf x₁))
      ≈˘⟨ assoc _ _ _ ⟩
        (D .fobj s₃ .fam .subst _ ∘ D .fmor ⟪ _ ⟫ .famf .transf x₂) ∘ (D .fobj s₂ .fam .subst _ ∘ D .fmor ⟪ _ ⟫ .famf .transf x₁)
      ∎
      where open ≈-Reasoning isEquiv
    bigCoproducts S D .cocone .transf s .idxf .func x = s , x
    bigCoproducts S D .cocone .transf s .idxf .func-resp-≈ x₁≈x₂ =
      S .refl , D .fmor-id .idxf-eq .func-eq x₁≈x₂
    bigCoproducts S D .cocone .transf s .famf .transf x = id _
    bigCoproducts S D .cocone .transf s .famf .natural {x₁} {x₂} x₁≈x₂ = begin
        id _ ∘ D .fobj s .fam .subst x₁≈x₂
      ≈˘⟨ ∘-cong (D .fmor-id {s} .famf-eq .transf-eq {x₂}) ≈-refl ⟩
        (D .fobj s .fam. subst _ ∘ D .fmor ⟪ _ ⟫ .famf .transf x₂) ∘ D .fobj s .fam .subst x₁≈x₂
      ≈⟨ assoc _ _ _ ⟩
        D .fobj s .fam. subst _ ∘ (D .fmor ⟪ _ ⟫ .famf .transf x₂ ∘ D .fobj s .fam .subst x₁≈x₂)
      ≈⟨ ∘-cong ≈-refl (D .fmor ⟪ S .refl ⟫ .famf .natural x₁≈x₂) ⟩
        D .fobj s .fam .subst _ ∘ (D .fobj s .fam .subst _ ∘ D .fmor ⟪ S .refl ⟫ .famf .transf x₁)
      ≈˘⟨ assoc _ _ _ ⟩
        (D .fobj s .fam .subst _ ∘ D .fobj s .fam .subst _) ∘ D .fmor ⟪ S .refl ⟫ .famf .transf x₁
      ≈˘⟨ ∘-cong (D .fobj s .fam .trans* _ _) ≈-refl ⟩
        D .fobj s .fam .subst (D .fmor-id .idxf-eq .func-eq x₁≈x₂) ∘ D .fmor ⟪ S .refl ⟫ .famf .transf x₁
      ≈˘⟨ id-right ⟩
        (D .fobj s .fam .subst _ ∘ D .fmor ⟪ _ ⟫ .famf .transf x₁) ∘ id _
      ∎
      where open ≈-Reasoning isEquiv
    bigCoproducts S D .cocone .natural ⟪ s₁≈s₂ ⟫ .idxf-eq .func-eq x₁≈x₂ =
      s₁≈s₂ , D .fmor ⟪ s₁≈s₂ ⟫ .idxf .func-resp-≈ x₁≈x₂
    bigCoproducts S D .cocone .natural {s₁} {s₂} ⟪ s₁≈s₂ ⟫ .famf-eq .transf-eq {x} = begin
        (D .fobj s₂ .fam .subst _ ∘ D .fmor ⟪ _ ⟫ .famf .transf x) ∘ (id _ ∘ (id _ ∘ id _))
      ≈⟨ ∘-cong (∘-cong (D .fobj s₂ .fam .refl*) ≈-refl) id-left ⟩
        (id _ ∘ D .fmor ⟪ _ ⟫ .famf .transf x) ∘ (id _ ∘ id _)
      ≈⟨ ∘-cong (∘-cong ≈-refl (≈-sym id-left)) id-left ⟩
        (id _ ∘ (id _ ∘ D .fmor ⟪ _ ⟫ .famf .transf x)) ∘ id _
      ≈⟨ id-right ⟩
        id _ ∘ (id _ ∘ D .fmor ⟪ _ ⟫ .famf .transf x)
      ∎
      where open ≈-Reasoning isEquiv
    bigCoproducts S D .isColimit .colambda X α .idxf .func (s , x) = α .transf s .idxf .func x
    bigCoproducts S D .isColimit .colambda X α .idxf .func-resp-≈ {s₁ , x₁} {s₂ , x₂} (s₁≈s₂ , x₁≈x₂) =
      X .idx .trans (α .natural ⟪ s₁≈s₂ ⟫ .idxf-eq .func-eq (D .fobj s₁ .idx .refl))
                    (α .transf s₂ .idxf .func-resp-≈ x₁≈x₂)
    bigCoproducts S D .isColimit .colambda X α .famf .transf (s , x) = α .transf s .famf .transf x
    bigCoproducts S D .isColimit .colambda X α .famf .natural {s₁ , x₁} {s₂ , x₂} (s₁≈s₂ , x₁≈x₂) =
      begin
        α .transf s₂ .famf .transf x₂ ∘ (D .fobj s₂ .fam .subst _ ∘ D .fmor ⟪ _ ⟫ .famf .transf x₁)
      ≈˘⟨ assoc _ _ _ ⟩
        (α .transf s₂ .famf .transf x₂ ∘ D .fobj s₂ .fam .subst _) ∘ D .fmor ⟪ _ ⟫ .famf .transf x₁
      ≈⟨ ∘-cong (α .transf s₂ .famf .natural x₁≈x₂) ≈-refl ⟩
        (X .fam .subst _ ∘ α .transf s₂ .famf .transf (D .fmor ⟪ _ ⟫ .idxf .func x₁)) ∘ D .fmor ⟪ _ ⟫ .famf .transf x₁
      ≈⟨ assoc _ _ _ ⟩
        X .fam .subst _ ∘ (α .transf s₂ .famf .transf (D .fmor ⟪ _ ⟫ .idxf .func x₁) ∘ D .fmor ⟪ _ ⟫ .famf .transf x₁)
      ≈˘⟨ ∘-cong ≈-refl id-left ⟩
        X .fam .subst _ ∘ (id _ ∘ (α .transf s₂ .famf .transf (D .fmor ⟪ _ ⟫ .idxf .func x₁) ∘ D .fmor ⟪ _ ⟫ .famf .transf x₁))
      ≈˘⟨ ∘-cong ≈-refl (α .natural ⟪ s₁≈s₂ ⟫ .famf-eq .transf-eq {x₁}) ⟩
        X .fam .subst _ ∘ (X .fam .subst _ ∘ (id _ ∘ (id _ ∘ α .transf s₁ .famf .transf x₁)))
      ≈˘⟨ assoc _ _ _ ⟩
        (X .fam .subst _ ∘ X .fam .subst _) ∘ (id _ ∘ (id _ ∘ α .transf s₁ .famf .transf x₁))
      ≈⟨ ∘-cong ≈-refl id-left ⟩
        (X .fam .subst _ ∘ X .fam .subst _) ∘ (id _ ∘ α .transf s₁ .famf .transf x₁)
      ≈⟨ ∘-cong (≈-sym (X .fam .trans* _ _)) id-left ⟩
        X .fam .subst _ ∘ α .transf s₁ .famf .transf x₁
      ∎
      where open ≈-Reasoning isEquiv
    bigCoproducts S D .isColimit .colambda-cong {X} {α} {β} α≃β .idxf-eq .func-eq {s₁ , x₁} {s₂ , x₂} (s₁≈s₂ , x₁≈x₂) =
      begin
        α .transf s₁ .idxf .func x₁
      ≈⟨ α .natural ⟪ s₁≈s₂ ⟫ .idxf-eq .func-eq (D .fobj s₁ .idx .refl) ⟩
        α .transf s₂ .idxf .func (D .fmor ⟪ _ ⟫ .idxf .func x₁)
      ≈⟨ α≃β .transf-eq s₂ .idxf-eq .func-eq (D .fobj s₂ .idx .refl) ⟩
        β .transf s₂ .idxf .func (D .fmor ⟪ _ ⟫ .idxf .func x₁)
      ≈⟨ β .transf s₂ .idxf .func-resp-≈ x₁≈x₂ ⟩
        β .transf s₂ .idxf .func x₂
      ∎
      where open ≈-Reasoning (X .idx .isEquivalence)
    bigCoproducts S D .isColimit .colambda-cong {X} {α} {β} α≃β .famf-eq .transf-eq {s , x} =
      α≃β .transf-eq s .famf-eq .transf-eq {x}
    bigCoproducts S D .isColimit .colambda-coeval X α .transf-eq s .idxf-eq .func-eq = α .transf s .idxf .func-resp-≈
    bigCoproducts S D .isColimit .colambda-coeval X α .transf-eq s .famf-eq .transf-eq {x} = begin
        X .fam .subst _ ∘ (id _ ∘ (α .transf s .famf .transf x ∘ id _))
      ≈⟨ ∘-cong (X .fam .refl*) (∘-cong ≈-refl id-right) ⟩
        id _ ∘ (id _ ∘ α .transf s .famf .transf x)
      ≈⟨ id-left ⟩
        id _ ∘ α .transf s .famf .transf x
      ≈⟨ id-left ⟩
        α .transf s .famf .transf x
      ∎
      where open ≈-Reasoning isEquiv
    bigCoproducts S D .isColimit .colambda-ext X f .idxf-eq .func-eq = f .idxf .func-resp-≈
    bigCoproducts S D .isColimit .colambda-ext X f .famf-eq .transf-eq {s , x} = begin
        X .fam .subst _ ∘ (id _ ∘ (f .famf .transf (s , x) ∘ id _))
      ≈⟨ ∘-cong (X .fam .refl*) (∘-cong ≈-refl id-right) ⟩
        id _ ∘ (id _ ∘ f .famf .transf (s , x))
      ≈⟨ id-left ⟩
        id _ ∘ f .famf .transf (s , x)
      ≈⟨ id-left ⟩
        f .famf .transf (s , x)
      ∎
      where open ≈-Reasoning isEquiv

  -- If 𝒞 has products, then so does the category of families. FIXME:
  -- redo the core of this to just get monoidal products from monoidal
  -- products. Even better, if we have monoidal products in each fibre
  -- and reindexing preserves them, then we get monoidal products in
  -- the total category.
  --
  -- FIXME: could this be generalised to all limits?
  module products (P : HasProducts 𝒞) where

    open Category 𝒞
    open HasProducts
    open IsEquivalence
    open _⇒f_

    _⊗_ : Obj → Obj → Obj
    (X ⊗ Y) .idx = ⊗-setoid (X .idx) (Y .idx)
    (X ⊗ Y) .fam .fm (x , y) = P .prod (X .fam .fm x) (Y .fam .fm y)
    (X ⊗ Y) .fam .subst (e₁ , e₂) =
      prod-m P (X .fam .subst e₁) (Y .fam .subst e₂)
    (X ⊗ Y) .fam .refl* =
      begin
        prod-m P (X .fam .subst _) (Y .fam .subst _)
      ≈⟨ prod-m-cong P (X .fam .refl*) (Y .fam .refl*) ⟩
        prod-m P (id _) (id _)
      ≈⟨ prod-m-id P ⟩
        id _
      ∎ where open ≈-Reasoning isEquiv
    (X ⊗ Y) .fam .trans* {x₁ , y₁} {x₂ , y₂} {x₃ , y₃} (x₂≈x₃ , y₂≈y₃) (x₁≈x₂ , y₁≈y₂) =
      begin
        prod-m P (X .fam .subst _) (Y .fam .subst _)
      ≈⟨ prod-m-cong P (X .fam .trans* _ _) (Y .fam .trans* _ _) ⟩
        prod-m P (X .fam .subst _ ∘ X .fam .subst _) (Y .fam .subst _ ∘ Y .fam .subst _)
      ≈⟨ pair-functorial P _ _ _ _ ⟩
        prod-m P (X .fam .subst _) (Y .fam .subst _) ∘ prod-m P (X .fam .subst _) (Y .fam .subst _)
      ∎ where open ≈-Reasoning isEquiv

    products : HasProducts cat
    products .prod = _⊗_
    products .p₁ .idxf = prop-setoid.project₁
    products .p₁ .famf .transf (x , y) = P .p₁
    products .p₁ {X} {Y} .famf .natural (e₁ , e₂) =
      begin
        P .p₁ ∘ P .pair (X .fam .subst _ ∘ P .p₁) (Y .fam .subst _ ∘ P .p₂)
      ≈⟨ P .pair-p₁ _ _ ⟩
        X .fam .subst _ ∘ P .p₁
      ∎ where open ≈-Reasoning isEquiv
    products .p₂ .idxf = prop-setoid.project₂
    products .p₂ .famf .transf (x , y) = P .p₂
    products .p₂ {X} {Y} .famf .natural (e₁ , e₂) =
      begin
        P .p₂ ∘ P .pair (X .fam .subst _ ∘ P .p₁) (Y .fam .subst _ ∘ P .p₂)
      ≈⟨ P .pair-p₂ _ _ ⟩
        Y .fam .subst _ ∘ P .p₂
      ∎ where open ≈-Reasoning isEquiv
    products .pair f g .idxf = prop-setoid.pair (f .idxf) (g .idxf)
    products .pair f g .famf .transf x = P .pair (f .famf .transf x) (g .famf .transf x)
    products .pair {X} {Y} {Z} f g .famf .natural {x₁} {x₂} x₁≈x₂ =
      begin
        P .pair (f .famf .transf x₂) (g .famf .transf x₂) ∘ X .fam .subst _
      ≈⟨ pair-natural P _ _ _ ⟩
        P .pair (f .famf .transf x₂ ∘ X .fam .subst _) (g .famf .transf x₂ ∘ X .fam .subst _)
      ≈⟨ P .pair-cong (f .famf .natural x₁≈x₂) (g .famf .natural x₁≈x₂) ⟩
        P .pair (Y .fam .subst _ ∘ f .famf .transf x₁) (Z .fam .subst _ ∘ g .famf .transf x₁)
      ≈⟨ ≈-sym (P .pair-cong (∘-cong ≈-refl (P .pair-p₁ _ _)) (∘-cong ≈-refl (P .pair-p₂ _ _))) ⟩
        P .pair (Y .fam .subst _ ∘ (P .p₁ ∘ P .pair (f .famf .transf x₁) (g .famf .transf x₁))) (Z .fam .subst _ ∘ (P .p₂ ∘ P .pair (f .famf .transf x₁) (g .famf .transf x₁)))
      ≈⟨ ≈-sym (P .pair-cong (assoc _ _ _) (assoc _ _ _)) ⟩
        P .pair ((Y .fam .subst _ ∘ P .p₁) ∘ P .pair (f .famf .transf x₁) (g .famf .transf x₁)) ((Z .fam .subst _ ∘ P .p₂) ∘ P .pair (f .famf .transf x₁) (g .famf .transf x₁))
      ≈⟨ ≈-sym (pair-natural P _ _ _) ⟩
        P .pair (Y .fam .subst _ ∘ P .p₁) (Z .fam .subst _ ∘ P .p₂) ∘ P .pair (f .famf .transf x₁) (g .famf .transf x₁)
      ∎ where open ≈-Reasoning isEquiv
    products .pair-cong f₁≈f₂ g₁≈g₂ .idxf-eq = prop-setoid.pair-cong (f₁≈f₂ .idxf-eq) (g₁≈g₂ .idxf-eq)
    products .pair-cong {X}{Y}{Z} {f₁}{f₂}{g₁}{g₂} f₁≈f₂ g₁≈g₂ .famf-eq ._≃f_.transf-eq {x} =
      begin
        P .pair (Y .fam .subst _ ∘ P .p₁) (Z .fam .subst _ ∘ P .p₂) ∘ P .pair (f₁ .famf .transf x) (g₁ .famf .transf x)
      ≈⟨ pair-compose P _ _ _ _ ⟩
        P .pair (Y .fam .subst _ ∘ f₁ .famf .transf x) (Z .fam .subst _ ∘ g₁ .famf .transf x)
      ≈⟨ P .pair-cong (f₁≈f₂ .famf-eq ._≃f_.transf-eq) (g₁≈g₂ .famf-eq ._≃f_.transf-eq) ⟩
        P .pair (f₂ .famf .transf x) (g₂ .famf .transf x)
      ∎ where open ≈-Reasoning isEquiv
    products .pair-p₁ {X} {Y} {Z} f g .idxf-eq = Setoid-products _ _ .pair-p₁ _ _
    products .pair-p₁ {X} {Y} {Z} f g .famf-eq ._≃f_.transf-eq {x} =
      begin
        Y .fam .subst _ ∘ (id _ ∘ (P .p₁ ∘ P .pair (f .famf .transf x) (g .famf .transf x)))
      ≈⟨ ∘-cong ≈-refl id-left ⟩
        Y .fam .subst _ ∘ (P .p₁ ∘ P .pair (f .famf .transf x) (g .famf .transf x))
      ≈⟨ ∘-cong (Y .fam .refl*) (P .pair-p₁ _ _) ⟩
        id _ ∘ f .famf .transf x
      ≈⟨ id-left ⟩
        f .famf .transf x
      ∎ where open ≈-Reasoning isEquiv
    products .pair-p₂ {X} {Y} {Z} f g .idxf-eq = Setoid-products _ _ .pair-p₂ _ _
    products .pair-p₂ {X} {Y} {Z} f g .famf-eq ._≃f_.transf-eq {x} =
      begin
        Z .fam .subst _ ∘ (id _ ∘ (P .p₂ ∘ P .pair (f .famf .transf x) (g .famf .transf x)))
      ≈⟨ ∘-cong ≈-refl id-left ⟩
        Z .fam .subst _ ∘ (P .p₂ ∘ P .pair (f .famf .transf x) (g .famf .transf x))
      ≈⟨ ∘-cong (Z .fam .refl*) (P .pair-p₂ _ _) ⟩
        id _ ∘ g .famf .transf x
      ≈⟨ id-left ⟩
        g .famf .transf x
      ∎ where open ≈-Reasoning isEquiv
    products .pair-ext f .idxf-eq = Setoid-products _ _ .pair-ext _
    products .pair-ext {X}{Y}{Z} f .famf-eq ._≃f_.transf-eq {x} =
      begin
        P .pair (Y .fam .subst _ ∘ P .p₁) (Z .fam .subst _ ∘ P .p₂) ∘ P .pair (id _ ∘ (P .p₁ ∘ f .famf .transf x)) (id _ ∘ (P .p₂ ∘ f .famf .transf x))
      ≈⟨ ∘-cong ≈-refl (pair-cong P id-left id-left) ⟩
        P .pair (Y .fam .subst _ ∘ P .p₁) (Z .fam .subst _ ∘ P .p₂) ∘ P .pair (P .p₁ ∘ f .famf .transf x) (P .p₂ ∘ f .famf .transf x)
      ≈⟨ pair-compose P _ _ _ _ ⟩
        P .pair (Y .fam .subst _ ∘ (P .p₁ ∘ f .famf .transf x)) (Z .fam .subst _ ∘ (P .p₂ ∘ f .famf .transf x))
      ≈⟨ P .pair-cong (∘-cong (Y .fam .refl*) ≈-refl) (∘-cong (Z .fam .refl*) ≈-refl) ⟩
        P .pair (id _ ∘ (P .p₁ ∘ f .famf .transf x)) (id _ ∘ (P .p₂ ∘ f .famf .transf x))
      ≈⟨ P .pair-cong id-left id-left ⟩
        P .pair (P .p₁ ∘ f .famf .transf x) (P .p₂ ∘ f .famf .transf x)
      ≈⟨ P .pair-ext _ ⟩
        f .famf .transf x
      ∎ where open ≈-Reasoning isEquiv

    simple-monoidal : ∀ {X Y x y} → Mor (simple[ X , x ] ⊗ simple[ Y , y ]) simple[ ⊗-setoid X Y , P .prod x y ]
    simple-monoidal .idxf = idS _
    simple-monoidal .famf .transf _ = id _
    simple-monoidal .famf .natural (_ , _) = ∘-cong ≈-refl (prod-m-id P)

    open HasStrongCoproducts

    strongCoproducts : HasStrongCoproducts cat products
    strongCoproducts .coprod = coproducts .HasCoproducts.coprod
    strongCoproducts .in₁ = coproducts .HasCoproducts.in₁
    strongCoproducts .in₂ = coproducts .HasCoproducts.in₂
    strongCoproducts .copair f g .idxf = prop-setoid.case (f .idxf) (g .idxf)
    strongCoproducts .copair f g .famf .transf (w , inj₁ x) = f .famf .transf (w , x)
    strongCoproducts .copair f g .famf .transf (w , inj₂ y) = g .famf .transf (w , y)
    strongCoproducts .copair {W}{X}{Y}{Z} f g .famf .natural {w₁ , inj₁ x₁} {w₂ , inj₁ x₂} (w₁≈w₂ , e) =
      f .famf .natural (w₁≈w₂ , e)
    strongCoproducts .copair f g .famf .natural {w₁ , inj₂ y} {w₂ , inj₂ y₁} (w₁≈w₂ , e) =
      g .famf .natural (w₁≈w₂ , e)

-- FIXME: every functor 𝒞 ⇒ 𝒟 gives a functor Fam(𝒞) ⇒ Fam(𝒟), and
-- this carries over to natural transformations. So we have functors:
--    F : Functor [ 𝒞 ⇒ 𝒟 ] [ Fam 𝒞 ⇒ Fam 𝒟 ]
{-
  module monad (Mon : Monad 𝒞) where

    open Category 𝒞
    open IsEquivalence
    open Monad
    open _⇒f_
    open _≃f_

    monad : Monad cat
    monad .M X .idx = X .idx
    monad .M X .fam .fm x = Mon .M (X .fam .fm x)
    monad .M X .fam .subst x≈y = Mon .map (X .fam .subst x≈y)
    monad .M X .fam .refl* =
      begin
        Mon .map (X .fam .subst _)
      ≈⟨ Mon .map-cong (X .fam .refl*) ⟩
        Mon .map (id _)
      ≈⟨ Mon .map-id ⟩
        id _
      ∎ where open ≈-Reasoning isEquiv
    monad .M X .fam .trans* y≈z x≈y =
      begin
        Mon .map (X .fam .subst _)
      ≈⟨ Mon .map-cong (X .fam .trans* _ _) ⟩
        Mon .map (X .fam .subst _ ∘ X .fam .subst _)
      ≈⟨ Mon .map-comp _ _ ⟩
        Mon .map (X .fam .subst _) ∘ Mon .map (X .fam .subst _)
      ∎ where open ≈-Reasoning isEquiv
    monad .map f .idxf = f .idxf
    monad .map f .famf .transf x = Mon .map (f .famf .transf x)
    monad .map {X} {Y} f .famf .natural x₁≈x₂ =
      begin
        Mon .map (f .famf .transf _) ∘ Mon .map (X .fam .subst _)
      ≈⟨ ≈-sym (Mon .map-comp _ _) ⟩
        Mon .map (f .famf .transf _ ∘ X .fam .subst _)
      ≈⟨ Mon .map-cong (f .famf .natural _) ⟩
        Mon .map (Y .fam .subst _ ∘ f .famf .transf _)
      ≈⟨ Mon .map-comp _ _ ⟩
        Mon .map (Y .fam .subst _) ∘ Mon .map (f .famf .transf _)
      ∎ where open ≈-Reasoning isEquiv
    monad .unit .idxf = idS _
    monad .unit .famf .transf x = Mon .unit
    monad .unit .famf .natural e = Mon .unit-natural _
    monad .join .idxf = idS _
    monad .join .famf .transf x = Mon .join
    monad .join .famf .natural e = Mon .join-natural _
    monad .map-cong eq .idxf-eq = eq .idxf-eq
    monad .map-cong eq .famf-eq .transf-eq {x} =
      isEquiv .trans (≈-sym (Mon .map-comp _ _))
                     (Mon .map-cong (eq .famf-eq .transf-eq))
    monad .map-id .idxf-eq = ≈s-isEquivalence .refl
    monad .map-id {X} .famf-eq .transf-eq {x} =
      begin
        Mon .map (X .fam .subst _) ∘ Mon .map (id _)
      ≈⟨ ∘-cong (Mon .map-cong (X .fam .refl*)) ≈-refl ⟩
        Mon .map (id _) ∘ Mon .map (id _)
      ≈⟨ ∘-cong (Mon .map-id) (Mon .map-id) ⟩
        id _ ∘ id _
      ≈⟨ id-left ⟩
        id _
      ∎
      where open ≈-Reasoning isEquiv
    monad .map-comp f g .idxf-eq = ≈s-isEquivalence .refl
    monad .map-comp {X} {Y} {Z} f g .famf-eq .transf-eq {x} =
      begin
        Mon .map (Z .fam .subst _) ∘ Mon .map (f .famf .transf _ ∘ g .famf .transf x)
      ≈⟨ ∘-cong (Mon .map-cong (Z .fam .refl*)) ≈-refl ⟩
        Mon .map (id _) ∘ Mon .map (f .famf .transf _ ∘ g .famf .transf x)
      ≈⟨ ∘-cong (Mon .map-id) (Mon .map-comp _ _) ⟩
        id _ ∘ (Mon .map (f .famf .transf _) ∘ Mon .map (g .famf .transf x))
      ≈⟨ id-left ⟩
        Mon .map (f .famf .transf _) ∘ Mon .map (g .famf .transf x)
      ∎
      where open ≈-Reasoning isEquiv
    monad .unit-natural f .idxf-eq =
      ≈s-isEquivalence .trans prop-setoid.id-left (≈s-isEquivalence .sym prop-setoid.id-right)
    monad .unit-natural {X}{Y} f .famf-eq .transf-eq {x} =
      begin
        Mon .map (Y .fam .subst _) ∘ (Mon .unit ∘ f .famf .transf x)
      ≈⟨ ∘-cong (Mon .map-cong (Y .fam .refl*)) (Mon .unit-natural (f .famf .transf x)) ⟩
        Mon .map (id _) ∘ (Mon .map (f .famf .transf x) ∘ Mon .unit)
      ≈⟨ ∘-cong (Mon .map-id) ≈-refl ⟩
        id _ ∘ (Mon .map (f .famf .transf x) ∘ Mon .unit)
      ≈⟨ id-left ⟩
        Mon .map (f .famf .transf x) ∘ Mon .unit
      ∎
      where open ≈-Reasoning isEquiv
    monad .join-natural f .idxf-eq =
      ≈s-isEquivalence .trans prop-setoid.id-left (≈s-isEquivalence .sym prop-setoid.id-right)
    monad .join-natural {X} {Y} f .famf-eq .transf-eq {x} =
      begin
        Mon .map (Y .fam .subst _) ∘ (Mon .join ∘ Mon .map (Mon .map (f .famf .transf x)))
      ≈⟨ ∘-cong (Mon .map-cong (Y .fam .refl*)) (Mon .join-natural _) ⟩
        Mon .map (id _) ∘ (Mon .map (f .famf .transf x) ∘ Mon .join)
      ≈⟨ ∘-cong (Mon .map-id) ≈-refl ⟩
        id _ ∘ (Mon .map (f .famf .transf x) ∘ Mon .join)
      ≈⟨ id-left ⟩
        Mon .map (f .famf .transf x) ∘ Mon .join
      ∎
      where open ≈-Reasoning isEquiv
-}
  module _ (T : HasTerminal 𝒞) (P : HasProducts 𝒞) where

    open import Data.List using ([]; _∷_)
    open Category 𝒞
    open IsEquivalence
    open HasTerminal
    open HasProducts P
    open products P  -- brings Fam-level `products` into scope
    open _⇒f_

    ----------------------------------------------------------------------
    -- Generic μ-types in Fam(𝒞), one per polynomial Q : Poly cat. The
    -- idx side is prop-setoid.WSetoid of poly Q (projecting param
    -- slots from Fam-objs to their idx setoids); the fibre side is
    -- built recursively over Q using 𝒞's products.
    module W-types (Q : Poly cat) where
      open import Data.Sum using (inj₁; inj₂)
      open import Data.Product using (_,_)
      open _⇒s_
      open _⇒f_

      idx-of : Poly cat → prop-setoid.IdxPoly
      idx-of Poly.one        = prop-setoid.one
      idx-of (Poly.const A)  = prop-setoid.param (A .idx)
      idx-of Poly.var        = prop-setoid.var
      idx-of (P₁ Poly.+ P₂)  = idx-of P₁ prop-setoid.+ᵖ idx-of P₂
      idx-of (P₁ Poly.× P₂)  = idx-of P₁ prop-setoid.×ᵖ idx-of P₂

      poly : prop-setoid.IdxPoly
      poly = idx-of Q

      -- Fibre as a single recursive function on (P : Poly cat) and the
      -- corresponding WIdx-of value. At the var case, the W argument is
      -- destructed via sup, exposing a structurally smaller WIdx-of value
      -- (passed back at the outer Q). This is well-founded on the
      -- WIdx-of/W structure (decreases at var via sup destruction);
      -- Agda's termination checker should accept it.
      WFam-of-fm : (P : Poly cat) →
                   prop-setoid.WIdx-of poly (idx-of P) → obj
      WFam-of-fm Poly.one        _                    = T .witness
      WFam-of-fm (Poly.const A)  a                    = A .fam .fm a
      WFam-of-fm Poly.var        (prop-setoid.sup i)  = WFam-of-fm Q i
      WFam-of-fm (P₁ Poly.+ P₂)  (inj₁ x)             = WFam-of-fm P₁ x
      WFam-of-fm (P₁ Poly.+ P₂)  (inj₂ y)             = WFam-of-fm P₂ y
      WFam-of-fm (P₁ Poly.× P₂)  (x , y)              = prod (WFam-of-fm P₁ x) (WFam-of-fm P₂ y)

      WFam-of-subst : (P : Poly cat) → ∀ {x y} →
                      prop-setoid.WIdx-≈-of poly (idx-of P) x y →
                      WFam-of-fm P x ⇒ WFam-of-fm P y
      WFam-of-subst Poly.one         _ = id _
      WFam-of-subst (Poly.const A) {x} {y} eq = A .fam .subst eq
      WFam-of-subst Poly.var {prop-setoid.sup i₁} {prop-setoid.sup i₂} eq = WFam-of-subst Q eq
      WFam-of-subst (P₁ Poly.+ P₂) {inj₁ _} {inj₁ _} eq = WFam-of-subst P₁ eq
      WFam-of-subst (P₁ Poly.+ P₂) {inj₂ _} {inj₂ _} eq = WFam-of-subst P₂ eq
      WFam-of-subst (P₁ Poly.+ P₂) {inj₁ _} {inj₂ _} ()
      WFam-of-subst (P₁ Poly.+ P₂) {inj₂ _} {inj₁ _} ()
      WFam-of-subst (P₁ Poly.× P₂) {_ , _} {_ , _} (e₁ , e₂) =
        prod-m (WFam-of-subst P₁ e₁) (WFam-of-subst P₂ e₂)

      WFam-of-refl* : (P : Poly cat) → ∀ {x} →
                      WFam-of-subst P (prop-setoid.WIdx-≈-of-refl poly (idx-of P) {x}) ≈ id _
      WFam-of-refl* Poly.one         = isEquiv .refl
      WFam-of-refl* (Poly.const A) {x} = A .fam .refl*
      WFam-of-refl* Poly.var {prop-setoid.sup i} = WFam-of-refl* Q {i}
      WFam-of-refl* (P₁ Poly.+ P₂) {inj₁ x} = WFam-of-refl* P₁ {x}
      WFam-of-refl* (P₁ Poly.+ P₂) {inj₂ y} = WFam-of-refl* P₂ {y}
      WFam-of-refl* (P₁ Poly.× P₂) {x , y}  =
        begin
          prod-m (WFam-of-subst P₁ _) (WFam-of-subst P₂ _)
        ≈⟨ prod-m-cong (WFam-of-refl* P₁ {x}) (WFam-of-refl* P₂ {y}) ⟩
          prod-m (id _) (id _)
        ≈⟨ prod-m-id ⟩
          id _
        ∎ where open ≈-Reasoning isEquiv

      WFam-of-trans* : (P : Poly cat) → ∀ {x y z}
                       (e₁ : prop-setoid.WIdx-≈-of poly (idx-of P) y z)
                       (e₂ : prop-setoid.WIdx-≈-of poly (idx-of P) x y) →
                       WFam-of-subst P (prop-setoid.WIdx-≈-of-trans poly (idx-of P) e₂ e₁) ≈
                       (WFam-of-subst P e₁ ∘ WFam-of-subst P e₂)
      WFam-of-trans* Poly.one _ _ = isEquiv .sym id-left
      WFam-of-trans* (Poly.const A) e₁ e₂ = A .fam .trans* e₁ e₂
      WFam-of-trans* Poly.var {prop-setoid.sup _} {prop-setoid.sup _} {prop-setoid.sup _} e₁ e₂ =
        WFam-of-trans* Q e₁ e₂
      WFam-of-trans* (P₁ Poly.+ P₂) {inj₁ _} {inj₁ _} {inj₁ _} e₁ e₂ = WFam-of-trans* P₁ e₁ e₂
      WFam-of-trans* (P₁ Poly.+ P₂) {inj₂ _} {inj₂ _} {inj₂ _} e₁ e₂ = WFam-of-trans* P₂ e₁ e₂
      WFam-of-trans* (P₁ Poly.× P₂) {_ , _} {_ , _} {_ , _} (e₁ , f₁) (e₂ , f₂) =
        begin
          prod-m (WFam-of-subst P₁ _) (WFam-of-subst P₂ _)
        ≈⟨ prod-m-cong (WFam-of-trans* P₁ e₁ e₂) (WFam-of-trans* P₂ f₁ f₂) ⟩
          prod-m (WFam-of-subst P₁ e₁ ∘ WFam-of-subst P₁ e₂) (WFam-of-subst P₂ f₁ ∘ WFam-of-subst P₂ f₂)
        ≈⟨ pair-functorial _ _ _ _ ⟩
          prod-m (WFam-of-subst P₁ e₁) (WFam-of-subst P₂ f₁) ∘ prod-m (WFam-of-subst P₁ e₂) (WFam-of-subst P₂ f₂)
        ∎ where open ≈-Reasoning isEquiv

      WFam : Fam (prop-setoid.WSetoid poly) 𝒞
      WFam .fm (prop-setoid.sup i)                              = WFam-of-fm Q i
      WFam .subst {prop-setoid.sup _} {prop-setoid.sup _} eq    = WFam-of-subst Q eq
      WFam .refl* {prop-setoid.sup _}                           = WFam-of-refl* Q
      WFam .trans* {prop-setoid.sup _} {prop-setoid.sup _} {prop-setoid.sup _} e₁ e₂ =
        WFam-of-trans* Q e₁ e₂

      WObj : Obj
      WObj .idx = prop-setoid.WSetoid poly
      WObj .fam = WFam

      -- The sup morphism: poly-obj (terminal T) products coproducts Q WObj ⇒ WObj.
      -- At the idx side, embed the structurally-built Fam-idx into WIdx-of and
      -- wrap with prop-setoid.sup. At the fam side, the fibres are
      -- definitionally equal at each Poly case, so the transf is the identity.
      open import Data.Unit using (tt) renaming (⊤ to 𝟙S)

      embed-idx : (P : Poly cat) →
                  poly-obj (terminal T) products coproducts P WObj .idx .Setoid.Carrier →
                  prop-setoid.WIdx-of poly (idx-of P)
      embed-idx Poly.one         (lift tt)  = lift tt
      embed-idx (Poly.const A)   a          = a
      embed-idx Poly.var         w          = w
      embed-idx (P₁ Poly.+ P₂)   (inj₁ x)   = inj₁ (embed-idx P₁ x)
      embed-idx (P₁ Poly.+ P₂)   (inj₂ y)   = inj₂ (embed-idx P₂ y)
      embed-idx (P₁ Poly.× P₂)   (x , y)    = (embed-idx P₁ x , embed-idx P₂ y)

      embed-≈ : (P : Poly cat) → ∀ {x y} →
                poly-obj (terminal T) products coproducts P WObj .idx .Setoid._≈_ x y →
                prop-setoid.WIdx-≈-of poly (idx-of P) (embed-idx P x) (embed-idx P y)
      embed-≈ Poly.one         _   = tt
      embed-≈ (Poly.const A)   eq  = eq
      embed-≈ Poly.var         eq  = eq
      embed-≈ (P₁ Poly.+ P₂) {inj₁ _} {inj₁ _} eq        = embed-≈ P₁ eq
      embed-≈ (P₁ Poly.+ P₂) {inj₂ _} {inj₂ _} eq        = embed-≈ P₂ eq
      embed-≈ (P₁ Poly.× P₂) {_ , _} {_ , _} (e₁ , e₂)   = (embed-≈ P₁ e₁ , embed-≈ P₂ e₂)

      -- Fibre-level structural identity. Definitionally,
      -- (apply _ _ _ P WObj).fam.fm i = WFam-of-fm P (embed-idx P i)
      -- at each Poly case (after destructing W's sup at the var case).
      embed-fam : (P : Poly cat) (i : poly-obj (terminal T) products coproducts P WObj .idx .Setoid.Carrier) →
                  poly-obj (terminal T) products coproducts P WObj .fam .fm i ⇒
                  WFam-of-fm P (embed-idx P i)
      embed-fam Poly.one       (lift tt)             = id _
      embed-fam (Poly.const A) a                     = id _
      embed-fam Poly.var       (prop-setoid.sup _)   = id _
      embed-fam (P₁ Poly.+ P₂) (inj₁ x)              = embed-fam P₁ x
      embed-fam (P₁ Poly.+ P₂) (inj₂ y)              = embed-fam P₂ y
      embed-fam (P₁ Poly.× P₂) (x , y)               = prod-m (embed-fam P₁ x) (embed-fam P₂ y)

      embed-fam-natural : (P : Poly cat) → ∀ {x₁ x₂}
                          (e : poly-obj (terminal T) products coproducts P WObj .idx .Setoid._≈_ x₁ x₂) →
                          (embed-fam P x₂ ∘ poly-obj (terminal T) products coproducts P WObj .fam .subst e)
                          ≈ (WFam-of-subst P (embed-≈ P e) ∘ embed-fam P x₁)
      embed-fam-natural Poly.one _ =
        isEquiv .trans id-left (≈-sym id-right)
      embed-fam-natural (Poly.const A) _ =
        isEquiv .trans id-left (≈-sym id-right)
      embed-fam-natural Poly.var {prop-setoid.sup _} {prop-setoid.sup _} _ =
        isEquiv .trans id-left (≈-sym id-right)
      embed-fam-natural (P₁ Poly.+ P₂) {inj₁ _} {inj₁ _} e = embed-fam-natural P₁ e
      embed-fam-natural (P₁ Poly.+ P₂) {inj₂ _} {inj₂ _} e = embed-fam-natural P₂ e
      embed-fam-natural (P₁ Poly.× P₂) {x₁ , y₁} {x₂ , y₂} (e , f) =
        begin
          prod-m (embed-fam P₁ x₂) (embed-fam P₂ y₂) ∘ prod-m _ _
        ≈⟨ ≈-sym (pair-functorial _ _ _ _) ⟩
          prod-m (embed-fam P₁ x₂ ∘ _) (embed-fam P₂ y₂ ∘ _)
        ≈⟨ prod-m-cong (embed-fam-natural P₁ e) (embed-fam-natural P₂ f) ⟩
          prod-m (WFam-of-subst P₁ (embed-≈ P₁ e) ∘ embed-fam P₁ x₁) (WFam-of-subst P₂ (embed-≈ P₂ f) ∘ embed-fam P₂ y₁)
        ≈⟨ pair-functorial _ _ _ _ ⟩
          prod-m (WFam-of-subst P₁ (embed-≈ P₁ e)) (WFam-of-subst P₂ (embed-≈ P₂ f)) ∘ prod-m (embed-fam P₁ x₁) (embed-fam P₂ y₁)
        ∎ where open ≈-Reasoning isEquiv

      sup : Mor (poly-obj (terminal T) products coproducts Q WObj) WObj
      sup .idxf .func i                     = prop-setoid.sup (embed-idx Q i)
      sup .idxf .func-resp-≈ eq             = embed-≈ Q eq
      sup .famf .transf i                   = embed-fam Q i
      sup .famf .natural e                  = embed-fam-natural Q e

      -- Fold. Given an algebra alg : apply Q y ⇒ y, the recursion descends
      -- the W structure at each var slot, applying alg's idx/fam components.
      module _ {y : Obj} (alg : Mor (poly-obj (terminal T) products coproducts Q y) y) where

        project-idx : (P : Poly cat) → prop-setoid.WIdx-of poly (idx-of P) →
                      poly-obj (terminal T) products coproducts P y .idx .Setoid.Carrier
        project-idx Poly.one _                       = lift tt
        project-idx (Poly.const A) a                 = a
        project-idx Poly.var (prop-setoid.sup i)     = alg .idxf .func (project-idx Q i)
        project-idx (P₁ Poly.+ P₂) (inj₁ x)          = inj₁ (project-idx P₁ x)
        project-idx (P₁ Poly.+ P₂) (inj₂ z)          = inj₂ (project-idx P₂ z)
        project-idx (P₁ Poly.× P₂) (x , z)           = (project-idx P₁ x , project-idx P₂ z)

        project-≈ : (P : Poly cat) → ∀ {x z} →
                    prop-setoid.WIdx-≈-of poly (idx-of P) x z →
                    poly-obj (terminal T) products coproducts P y .idx .Setoid._≈_
                      (project-idx P x) (project-idx P z)
        project-≈ Poly.one _ = tt
        project-≈ (Poly.const A) eq = eq
        project-≈ Poly.var {prop-setoid.sup _} {prop-setoid.sup _} eq =
          alg .idxf .func-resp-≈ (project-≈ Q eq)
        project-≈ (P₁ Poly.+ P₂) {inj₁ _} {inj₁ _} eq = project-≈ P₁ eq
        project-≈ (P₁ Poly.+ P₂) {inj₂ _} {inj₂ _} eq = project-≈ P₂ eq
        project-≈ (P₁ Poly.× P₂) {_ , _} {_ , _} (e , f) = (project-≈ P₁ e , project-≈ P₂ f)

        project-fam : (P : Poly cat) (i : prop-setoid.WIdx-of poly (idx-of P)) →
                      WFam-of-fm P i ⇒
                      poly-obj (terminal T) products coproducts P y .fam .fm (project-idx P i)
        project-fam Poly.one _                       = id _
        project-fam (Poly.const A) a                 = id _
        project-fam Poly.var (prop-setoid.sup i)     =
          alg .famf .transf (project-idx Q i) ∘ project-fam Q i
        project-fam (P₁ Poly.+ P₂) (inj₁ x)          = project-fam P₁ x
        project-fam (P₁ Poly.+ P₂) (inj₂ z)          = project-fam P₂ z
        project-fam (P₁ Poly.× P₂) (x , z)           =
          prod-m (project-fam P₁ x) (project-fam P₂ z)

        project-fam-natural : (P : Poly cat) → ∀ {x z}
                              (e : prop-setoid.WIdx-≈-of poly (idx-of P) x z) →
                              (project-fam P z ∘ WFam-of-subst P e) ≈
                              (poly-obj (terminal T) products coproducts P y .fam .subst (project-≈ P e) ∘ project-fam P x)
        project-fam-natural Poly.one _ =
          isEquiv .trans id-left (≈-sym id-right)
        project-fam-natural (Poly.const A) _ =
          isEquiv .trans id-left (≈-sym id-right)
        project-fam-natural Poly.var {prop-setoid.sup i₁} {prop-setoid.sup i₂} eq =
          begin
            (alg .famf .transf (project-idx Q i₂) ∘ project-fam Q i₂) ∘ WFam-of-subst Q eq
          ≈⟨ assoc _ _ _ ⟩
            alg .famf .transf (project-idx Q i₂) ∘ (project-fam Q i₂ ∘ WFam-of-subst Q eq)
          ≈⟨ ∘-cong (isEquiv .refl) (project-fam-natural Q eq) ⟩
            alg .famf .transf (project-idx Q i₂) ∘
              (poly-obj (terminal T) products coproducts Q y .fam .subst (project-≈ Q eq) ∘ project-fam Q i₁)
          ≈⟨ ≈-sym (assoc _ _ _) ⟩
            (alg .famf .transf (project-idx Q i₂) ∘
              poly-obj (terminal T) products coproducts Q y .fam .subst (project-≈ Q eq)) ∘ project-fam Q i₁
          ≈⟨ ∘-cong (alg .famf .natural (project-≈ Q eq)) (isEquiv .refl) ⟩
            (y .fam .subst (alg .idxf .func-resp-≈ (project-≈ Q eq)) ∘ alg .famf .transf (project-idx Q i₁)) ∘ project-fam Q i₁
          ≈⟨ assoc _ _ _ ⟩
            y .fam .subst (alg .idxf .func-resp-≈ (project-≈ Q eq)) ∘
              (alg .famf .transf (project-idx Q i₁) ∘ project-fam Q i₁)
          ∎ where open ≈-Reasoning isEquiv
        project-fam-natural (P₁ Poly.+ P₂) {inj₁ _} {inj₁ _} e = project-fam-natural P₁ e
        project-fam-natural (P₁ Poly.+ P₂) {inj₂ _} {inj₂ _} e = project-fam-natural P₂ e
        project-fam-natural (P₁ Poly.× P₂) {x₁ , z₁} {x₂ , z₂} (e , f) =
          begin
            prod-m (project-fam P₁ x₂) (project-fam P₂ z₂) ∘ prod-m _ _
          ≈⟨ ≈-sym (pair-functorial _ _ _ _) ⟩
            prod-m (project-fam P₁ x₂ ∘ _) (project-fam P₂ z₂ ∘ _)
          ≈⟨ prod-m-cong (project-fam-natural P₁ e) (project-fam-natural P₂ f) ⟩
            prod-m (_ ∘ project-fam P₁ x₁) (_ ∘ project-fam P₂ z₁)
          ≈⟨ pair-functorial _ _ _ _ ⟩
            prod-m _ _ ∘ prod-m (project-fam P₁ x₁) (project-fam P₂ z₁)
          ∎ where open ≈-Reasoning isEquiv

        fold-mor : Mor WObj y
        fold-mor .idxf .func (prop-setoid.sup i)                                = alg .idxf .func (project-idx Q i)
        fold-mor .idxf .func-resp-≈ {prop-setoid.sup _} {prop-setoid.sup _} eq  = alg .idxf .func-resp-≈ (project-≈ Q eq)
        fold-mor .famf .transf (prop-setoid.sup i)                              = alg .famf .transf (project-idx Q i) ∘ project-fam Q i
        fold-mor .famf .natural {prop-setoid.sup _} {prop-setoid.sup _} eq      = project-fam-natural Poly.var eq

      fold : ∀ {y : Obj} → Mor (poly-obj (terminal T) products coproducts Q y) y → Mor WObj y
      fold alg = fold-mor alg

    hasMu : (Q : Poly cat) → HasMu (terminal T) products coproducts Q
    hasMu Q .HasMu.μ     = W-types.WObj Q
    hasMu Q .HasMu.inF   = W-types.sup Q
    hasMu Q .HasMu.⦅_⦆   = W-types.fold Q
