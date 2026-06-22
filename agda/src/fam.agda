{-# OPTIONS --prop --postfix-projections --safe #-}

module fam where

open import Level using (_⊔_; suc; lift)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; Σ-syntax)
open import prop using (_,_; tt; ∃ₚ; ⟪_⟫)
open import prop-setoid
  using (IsEquivalence; Setoid; 𝟙; +-setoid; ⊗-setoid; idS; _∘S_; module ≈-Reasoning)
  renaming (_⇒_ to _⇒s_; _≃m_ to _≈s_; ≃m-isEquivalence to ≈s-isEquivalence)
open import categories
  using (Category; HasTerminal; IsTerminal; HasCoproducts; HasProducts; HasStrongCoproducts; HasLists; setoid→category)
open import setoid-cat using (Setoid-products)
open import indexed-family
  using (Fam; _⇒f_; idf; _∘f_; ∘f-cong; _≃f_; ≃f-isEquivalence; ≃f-id-left; ≃f-assoc;
         _[_]; reindex-≈; reindex-≈-refl; reindex-≈-trans; reindex-id; reindex-comp; reindex-f;
         reindex-comp-≈; reindex-f-comp; reindex-f-cong; reindex-sq;
         reindex-id-left; reindex-id-right; reindex-id-natural; reindex-assoc; reindex-comp-natural;
         constantFam)
import stable-coproducts

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

  -- Fam(𝒞) has stable (universal) coproducts: it is extensive.
  module _ where

    module SC = stable-coproducts {𝒞 = cat} coproducts
    open SC using (Stable; StableBits)

    fam-stable : Stable
    fam-stable {x₁} {x₂} {x} {y} f-iso g = go
      where
        open Obj
        open Mor
        open _⇒s_
        open Setoid

        Cprod : Obj
        Cprod = coproducts .HasCoproducts.coprod x₁ x₂

        g' : Mor y Cprod
        g' = Mor-∘ (f-iso .Category.Iso.bwd) g

        p : y .idx ⇒s Cprod .idx
        p = g' .idxf

        P₁ P₂ : x₁ .idx .Carrier ⊎ x₂ .idx .Carrier → Set
        P₁ (inj₁ _) = ⊤
        P₁ (inj₂ _) = ⊥
        P₂ (inj₁ _) = ⊥
        P₂ (inj₂ _) = ⊤

        Y₁idx Y₂idx : Setoid os es
        Y₁idx .Carrier = Σ[ i ∈ y .idx .Carrier ] P₁ (p .func i)
        Y₁idx ._≈_ (i , _) (j , _) = y .idx ._≈_ i j
        Y₁idx .isEquivalence .refl = y .idx .isEquivalence .refl
        Y₁idx .isEquivalence .sym e = y .idx .isEquivalence .sym e
        Y₁idx .isEquivalence .trans e₁ e₂ = y .idx .isEquivalence .trans e₁ e₂
        Y₂idx .Carrier = Σ[ i ∈ y .idx .Carrier ] P₂ (p .func i)
        Y₂idx ._≈_ (i , _) (j , _) = y .idx ._≈_ i j
        Y₂idx .isEquivalence .refl = y .idx .isEquivalence .refl
        Y₂idx .isEquivalence .sym e = y .idx .isEquivalence .sym e
        Y₂idx .isEquivalence .trans e₁ e₂ = y .idx .isEquivalence .trans e₁ e₂

        projY₁ : Y₁idx ⇒s y .idx
        projY₁ .func (i , _) = i
        projY₁ .func-resp-≈ e = e
        projY₂ : Y₂idx ⇒s y .idx
        projY₂ .func (i , _) = i
        projY₂ .func-resp-≈ e = e

        Y₁ Y₂ : Obj
        Y₁ .idx = Y₁idx
        Y₁ .fam = y .fam [ projY₁ ]
        Y₂ .idx = Y₂idx
        Y₂ .fam = y .fam [ projY₂ ]

        go : StableBits f-iso g
        go .StableBits.y₁  = Y₁
        go .StableBits.y₂  = Y₂
        go .StableBits.h₁  = {!!}
        go .StableBits.h₂  = {!!}
        go .StableBits.h   = {!!}
        go .StableBits.eq₁ = {!!}
        go .StableBits.eq₂ = {!!}

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
    bigCoproducts S D .apex .idx .Carrier = Σ[ s ∈ S .Carrier ] D .fobj s .idx .Carrier
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
{-
  module _ (T : HasTerminal 𝒞) (P : HasProducts 𝒞) where

    open import Data.List using ([]; _∷_)
    open Category 𝒞
    open IsEquivalence
    open HasTerminal
    open HasProducts P

    ListFam : (X : Obj) → Fam (prop-setoid.ListS (X .idx)) 𝒞
    ListFam X .fm [] = T .witness
    ListFam X .fm (x ∷ xs) = prod (X .fam .fm x) (ListFam X .fm xs)
    ListFam X .subst {[]} {[]} tt = id _
    ListFam X .subst {x ∷ xs} {y ∷ ys} (x≈y , xs≈ys) = prod-m (X .fam .subst x≈y) (ListFam X .subst xs≈ys)
    ListFam X .refl* {[]} = isEquiv .refl
    ListFam X .refl* {x ∷ xs} =
      begin
        prod-m (X .fam .subst (X .idx .Setoid.refl {x})) (ListFam X .subst (prop-setoid.List-≈-refl (X .idx) {xs}))
      ≈⟨ prod-m-cong (X .fam .refl*) (ListFam X .refl* {xs}) ⟩
        prod-m (id _) (id _)
      ≈⟨ prod-m-id ⟩
        id _
      ∎ where open ≈-Reasoning isEquiv
    ListFam X .trans* {[]} {[]} {[]} e₁ e₂ = ≈-sym id-left
    ListFam X .trans* {x ∷ xs} {y ∷ ys} {z ∷ zs} (x≈y , xs≈ys) (y≈z , ys≈zs) =
      begin
        prod-m (X .fam .subst (X .idx .Setoid.trans y≈z x≈y)) (ListFam X .subst (prop-setoid.List-≈-trans (X .idx) ys≈zs xs≈ys))
      ≈⟨ prod-m-cong (X .fam .trans* x≈y y≈z) (ListFam X .trans* xs≈ys ys≈zs) ⟩
        prod-m (X .fam .subst x≈y ∘ X .fam .subst y≈z) (ListFam X .subst xs≈ys ∘ ListFam X .subst ys≈zs)
      ≈⟨ pair-functorial _ _ _ _ ⟩
       prod-m (X .fam .subst x≈y) (ListFam X .subst xs≈ys) ∘ prod-m (X .fam .subst y≈z) (ListFam X .subst ys≈zs)
      ∎
      where open ≈-Reasoning isEquiv

    ListF : Obj → Obj
    ListF X .idx = prop-setoid.ListS (X .idx)
    ListF X .fam = ListFam X

    module FT = HasTerminal (terminal T)
    open products P
    open _⇒f_
    open _≃f_

    nil : ∀ {X} → Mor FT.witness (ListF X)
    nil .idxf = prop-setoid.nil
    nil .famf .transf (lift tt) = id _
    nil .famf .natural x₁≈x₂ = isEquiv .refl

    cons : ∀ {X} → Mor (X ⊗ (ListF X)) (ListF X)
    cons .idxf = prop-setoid.cons
    cons .famf .transf x = id _
    cons .famf .natural x₁≈x₂ =
      isEquiv .trans id-left (≈-sym id-right)

    private
      _⊛_ = prod
      _⊛f_ = prod-m

      shuffle : ∀ {X Y Z} → (X ⊛ (Y ⊛ Z)) ⇒ ((X ⊛ Y) ⊛ (X ⊛ Z))
      shuffle = pair (id _ ⊛f p₁) (id _ ⊛f p₂)

      shuffle-natural : ∀ {X₁ Y₁ Z₁ X₂ Y₂ Z₂} (f : X₁ ⇒ X₂) (g : Y₁ ⇒ Y₂) (h : Z₁ ⇒ Z₂) →
          (shuffle ∘ (f ⊛f (g ⊛f h))) ≈ (((f ⊛f g) ⊛f (f ⊛f h)) ∘ shuffle)
      shuffle-natural f g h =
        begin
          shuffle ∘ (f ⊛f (g ⊛f h))
        ≈⟨ pair-natural _ _ _ ⟩
          pair ((id _ ⊛f p₁) ∘ (f ⊛f (g ⊛f h))) ((id _ ⊛f p₂) ∘ (f ⊛f (g ⊛f h)))
        ≈⟨ pair-cong (≈-sym (pair-functorial _ _ _ _)) (≈-sym (pair-functorial _ _ _ _)) ⟩
          pair ((id _ ∘ f) ⊛f (p₁ ∘ (g ⊛f h))) ((id _ ∘ f) ⊛f (p₂ ∘ (g ⊛f h)))
        ≈⟨ pair-cong (prod-m-cong id-swap (pair-p₁ _ _)) (prod-m-cong id-swap (pair-p₂ _ _)) ⟩
          pair ((f ∘ id _) ⊛f (g ∘ p₁)) ((f ∘ id _) ⊛f (h ∘ p₂))
        ≈⟨ pair-cong (pair-functorial _ _ _ _) (pair-functorial _ _ _ _) ⟩
          pair ((f ⊛f g) ∘ (id _ ⊛f p₁)) ((f ⊛f h) ∘ (id _ ⊛f p₂))
        ≈⟨ ≈-sym (pair-compose _ _ _ _) ⟩
          ((f ⊛f g) ⊛f (f ⊛f h)) ∘ shuffle
        ∎
        where open ≈-Reasoning isEquiv

    foldr : ∀ {X Y Z} → Mor X Z → Mor ((X ⊗ Y) ⊗ Z) Z → Mor (X ⊗ ListF Y) Z
    foldr nilCase consCase .idxf = prop-setoid.foldrP (nilCase .idxf) (consCase .idxf)
    foldr nilCase consCase .famf .transf (x , []) = nilCase .famf .transf x ∘ p₁
    foldr nilCase consCase .famf .transf (x , y ∷ ys) =
      (consCase .famf .transf ((x , _) , _) ∘ prod-m (id _) (foldr nilCase consCase .famf .transf (x , ys))) ∘ shuffle
    foldr {X} {Y} {Z} nilCase consCase .famf .natural {x₁ , []} {x₂ , []} (x₁≈x₂ , tt) =
      begin
        (nilCase .famf .transf x₂ ∘ p₁) ∘ prod-m (X .fam .subst _) (id _)
      ≈⟨ assoc _ _ _ ⟩
        nilCase .famf .transf x₂ ∘ (p₁ ∘ prod-m (X .fam .subst _) (id _))
      ≈⟨ ∘-cong ≈-refl (pair-p₁ _ _) ⟩
        nilCase .famf .transf x₂ ∘ (X .fam .subst _ ∘ p₁)
      ≈⟨ ≈-sym (assoc _ _ _) ⟩
        (nilCase .famf .transf x₂ ∘ X .fam .subst _) ∘ p₁
      ≈⟨ ∘-cong (nilCase .famf .natural _) ≈-refl ⟩
        (Z .fam .subst _ ∘ nilCase .famf .transf x₁) ∘ p₁
      ≈⟨ assoc _ _ _ ⟩
        Z .fam .subst _ ∘ (nilCase .famf .transf x₁ ∘ p₁)
      ∎ where open ≈-Reasoning isEquiv
    foldr {X} {Y} {Z} nilCase consCase .famf .natural {x₁ , y₁ ∷ ys₁} {x₂ , y₂ ∷ ys₂} (x₁≈x₂ , y₁≈y₂ , ys₁≈ys₂) =
      begin
        ((consCase .famf .transf ((x₂ , _) , _) ∘ prod-m (id _) (foldr nilCase consCase .famf .transf (x₂ , ys₂))) ∘ shuffle) ∘ (sX ⊛f (sY ⊛f sYS))
      ≈⟨ assoc _ _ _ ⟩
        (consCase .famf .transf ((x₂ , _) , _) ∘ prod-m (id _) (foldr nilCase consCase .famf .transf (x₂ , ys₂))) ∘ (shuffle ∘ (sX ⊛f (sY ⊛f sYS)))
      ≈⟨ ∘-cong ≈-refl (shuffle-natural _ _ _) ⟩
        (consCase .famf .transf ((x₂ , _) , _) ∘ prod-m (id _) (foldr nilCase consCase .famf .transf (x₂ , ys₂))) ∘ (((sX ⊛f sY) ⊛f (sX ⊛f sYS)) ∘ shuffle)
      ≈⟨ ≈-sym (assoc _ _ _) ⟩
        ((consCase .famf .transf ((x₂ , _) , _) ∘ prod-m (id _) (foldr nilCase consCase .famf .transf (x₂ , ys₂))) ∘ ((sX ⊛f sY) ⊛f (sX ⊛f sYS))) ∘ shuffle
      ≈⟨ ∘-cong (assoc _ _ _) ≈-refl ⟩
        (consCase .famf .transf ((x₂ , _) , _) ∘ (prod-m (id _) (foldr nilCase consCase .famf .transf (x₂ , ys₂)) ∘ ((sX ⊛f sY) ⊛f (sX ⊛f sYS)))) ∘ shuffle
      ≈⟨ ∘-cong (∘-cong ≈-refl (≈-sym (pair-functorial _ _ _ _))) ≈-refl ⟩
        (consCase .famf .transf ((x₂ , _) , _) ∘ (prod-m (id _ ∘ (sX ⊛f sY)) (foldr nilCase consCase .famf .transf (x₂ , ys₂) ∘ (sX ⊛f sYS)))) ∘ shuffle
      ≈⟨ ∘-cong (∘-cong ≈-refl (prod-m-cong id-swap (foldr nilCase consCase .famf .natural (x₁≈x₂ , ys₁≈ys₂)))) ≈-refl ⟩
        (consCase .famf .transf ((x₂ , _) , _) ∘ (prod-m ((sX ⊛f sY) ∘ id _) ((Z .fam .subst _ ∘ foldr nilCase consCase .famf .transf (x₁ , ys₁))))) ∘ shuffle
      ≈⟨ ∘-cong (∘-cong ≈-refl (pair-functorial _ _ _ _)) ≈-refl ⟩
        (consCase .famf .transf ((x₂ , _) , _) ∘ (prod-m (sX ⊛f sY) (Z .fam .subst _) ∘ prod-m (id _) (foldr nilCase consCase .famf .transf (x₁ , ys₁)))) ∘ shuffle
      ≈⟨ ∘-cong (≈-sym (assoc _ _ _)) ≈-refl ⟩
        ((consCase .famf .transf ((x₂ , _) , _) ∘ prod-m (sX ⊛f sY) (Z .fam .subst _)) ∘ prod-m (id _) (foldr nilCase consCase .famf .transf (x₁ , ys₁))) ∘ shuffle
      ≈⟨ ∘-cong (∘-cong (consCase .famf .natural ((x₁≈x₂ , y₁≈y₂) , eq)) ≈-refl) ≈-refl ⟩
        ((Z .fam .subst _ ∘ consCase .famf .transf ((x₁ , _) , _)) ∘ prod-m (id _) (foldr nilCase consCase .famf .transf (x₁ , ys₁))) ∘ shuffle
      ≈⟨ ∘-cong (assoc _ _ _) ≈-refl ⟩
        (Z .fam .subst _ ∘ (consCase .famf .transf ((x₁ , _) , _) ∘ prod-m (id _) (foldr nilCase consCase .famf .transf (x₁ , ys₁)))) ∘ shuffle
      ≈⟨ assoc _ _ _ ⟩
        Z .fam .subst _ ∘ ((consCase .famf .transf ((x₁ , _) , _) ∘ prod-m (id _) (foldr nilCase consCase .famf .transf (x₁ , ys₁))) ∘ shuffle)
      ∎
      where open ≈-Reasoning isEquiv
            sX = X .fam .subst x₁≈x₂
            sY = Y .fam .subst y₁≈y₂
            sYS = ListF Y .fam .subst ys₁≈ys₂
            eq = prop-setoid.foldrP (nilCase .idxf) (consCase .idxf) ._⇒s_.func-resp-≈ (x₁≈x₂ , ys₁≈ys₂)


    lists : HasLists cat (terminal T) products
    lists .HasLists.list = ListF
    lists .HasLists.nil = nil
    lists .HasLists.cons = cons
    lists .HasLists.fold = foldr
-}
