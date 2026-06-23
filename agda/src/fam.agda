{-# OPTIONS --prop --postfix-projections --safe #-}

module fam where

open import Level using (_⊔_; suc; lift)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
import Relation.Binary.PropositionalEquality as ≡
open ≡ using (_≡_)
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

  -- Fam(𝒞) has stable coproducts: it is extensive.
  module _ where

    open Obj
    open Mor
    open _⇒s_
    open _⇒f_
    open Setoid
    open Category 𝒞 using (_⇒_; obj; _∘_; id; id-left; id-right; ≈-refl; ≈-sym; ≈-trans; assoc; ∘-cong; isEquiv) renaming (_≈_ to _≈C_)
    open HasCoproducts coproducts using (coprod)

    module SC = stable-coproducts {𝒞 = cat} coproducts
    open SC using (Stable; StableBits)

    fam-stable : Stable
    fam-stable {x₁} {x₂} {x} {y} f g = stb
      where
        g' : Mor y (coprod x₁ x₂)
        g' = Mor-∘ (f .Category.Iso.bwd) g

        p : y .idx ⇒s (coprod x₁ x₂) .idx
        p = g' .idxf

        -- ≡ between sum elements lifts to the coproduct's setoid equality.
        ≡→≈ : ∀ {s s' : x₁ .idx .Carrier ⊎ x₂ .idx .Carrier} → s ≡ s' → (coprod x₁ x₂) .idx ._≈_ s s'
        ≡→≈ {s} ≡.refl = (coprod x₁ x₂) .idx .isEquivalence .refl {s}

        -- Transport the coproduct's (Prop-valued) equality along ≡ on both endpoints.
        substₚ₂ : {x x' y y' : x₁ .idx .Carrier ⊎ x₂ .idx .Carrier} → x ≡ x' → y ≡ y' → (coprod x₁ x₂) .idx ._≈_ x y → (coprod x₁ x₂) .idx ._≈_ x' y'
        substₚ₂ ≡.refl ≡.refl r = r

        Y₁ : Obj
        Y₁ .idx .Carrier = Σ[ i ∈ y .idx .Carrier ] Σ[ a ∈ x₁ .idx .Carrier ] (p .func i ≡ inj₁ a)
        Y₁ .idx ._≈_ (i , _) (j , _) = y .idx ._≈_ i j
        Y₁ .idx .isEquivalence .refl = y .idx .isEquivalence .refl
        Y₁ .idx .isEquivalence .sym e = y .idx .isEquivalence .sym e
        Y₁ .idx .isEquivalence .trans e₁ e₂ = y .idx .isEquivalence .trans e₁ e₂
        Y₁ .fam .fm (i , _) = y .fam .fm i
        Y₁ .fam .subst {i , _} {j , _} e = y .fam .subst e
        Y₁ .fam .refl* {i , _} = y .fam .refl*
        Y₁ .fam .trans* {i , _} {j , _} {k , _} e₁ e₂ = y .fam .trans* e₁ e₂

        Y₂ : Obj
        Y₂ .idx .Carrier = Σ[ i ∈ y .idx .Carrier ] Σ[ b ∈ x₂ .idx .Carrier ] (p .func i ≡ inj₂ b)
        Y₂ .idx ._≈_ (i , _) (j , _) = y .idx ._≈_ i j
        Y₂ .idx .isEquivalence .refl = y .idx .isEquivalence .refl
        Y₂ .idx .isEquivalence .sym e = y .idx .isEquivalence .sym e
        Y₂ .idx .isEquivalence .trans e₁ e₂ = y .idx .isEquivalence .trans e₁ e₂
        Y₂ .fam .fm (i , _) = y .fam .fm i
        Y₂ .fam .subst {i , _} {j , _} e = y .fam .subst e
        Y₂ .fam .refl* {i , _} = y .fam .refl*
        Y₂ .fam .trans* {i , _} {j , _} {k , _} e₁ e₂ = y .fam .trans* e₁ e₂

        h₁ : Mor Y₁ x₁
        h₁ .idxf .func (i , a , _) = a
        h₁ .idxf .func-resp-≈ {i , a , eq} {j , a' , eq'} i≈j = substₚ₂ eq eq' (p .func-resp-≈ i≈j)
        h₁ .famf .transf (i , a , eq) =
          (coprod x₁ x₂) .fam .subst {p .func i} {inj₁ a} (≡→≈ eq) ∘ g' .famf .transf i
        h₁ .famf .natural {i , a , eq} {j , a' , eq'} e =
          begin
            (Cf .subst {p .func j} {inj₁ a'} (≡→≈ eq') ∘ g' .famf .transf j) ∘ y .fam .subst e
          ≈⟨ assoc _ _ _ ⟩
            Cf .subst {p .func j} {inj₁ a'} (≡→≈ eq') ∘ (g' .famf .transf j ∘ y .fam .subst e)
          ≈⟨ ∘-cong ≈-refl (g' .famf .natural e) ⟩
            Cf .subst {p .func j} {inj₁ a'} (≡→≈ eq') ∘ (Cf .subst {p .func i} {p .func j} (p .func-resp-≈ e) ∘ g' .famf .transf i)
          ≈⟨ ≈-sym (assoc _ _ _) ⟩
            (Cf .subst {p .func j} {inj₁ a'} (≡→≈ eq') ∘ Cf .subst {p .func i} {p .func j} (p .func-resp-≈ e)) ∘ g' .famf .transf i
          ≈⟨ ∘-cong (≈-sym (Cf .trans* {p .func i} {p .func j} {inj₁ a'} (≡→≈ eq') (p .func-resp-≈ e))) ≈-refl ⟩
            Cf .subst {p .func i} {inj₁ a'} (Ci .isEquivalence .trans {p .func i} {p .func j} {inj₁ a'} (p .func-resp-≈ e) (≡→≈ eq')) ∘ g' .famf .transf i
          ≈⟨ ∘-cong (Cf .trans* {p .func i} {inj₁ a} {inj₁ a'} (substₚ₂ eq eq' (p .func-resp-≈ e)) (≡→≈ eq)) ≈-refl ⟩
            (Cf .subst {inj₁ a} {inj₁ a'} (substₚ₂ eq eq' (p .func-resp-≈ e)) ∘ Cf .subst {p .func i} {inj₁ a} (≡→≈ eq)) ∘ g' .famf .transf i
          ≈⟨ assoc _ _ _ ⟩
            Cf .subst {inj₁ a} {inj₁ a'} (substₚ₂ eq eq' (p .func-resp-≈ e)) ∘ (Cf .subst {p .func i} {inj₁ a} (≡→≈ eq) ∘ g' .famf .transf i)
          ∎
          where
            Cf = (coprod x₁ x₂) .fam
            Ci = (coprod x₁ x₂) .idx
            open ≈-Reasoning isEquiv

        h₂ : Mor Y₂ x₂
        h₂ .idxf .func (i , b , _) = b
        h₂ .idxf .func-resp-≈ {i , b , eq} {j , b' , eq'} i≈j = substₚ₂ eq eq' (p .func-resp-≈ i≈j)
        h₂ .famf .transf (i , b , eq) =
          (coprod x₁ x₂) .fam .subst {p .func i} {inj₂ b} (≡→≈ eq) ∘ g' .famf .transf i
        h₂ .famf .natural {i , b , eq} {j , b' , eq'} e =
          begin
            (Cf .subst {p .func j} {inj₂ b'} (≡→≈ eq') ∘ g' .famf .transf j) ∘ y .fam .subst e
          ≈⟨ assoc _ _ _ ⟩
            Cf .subst {p .func j} {inj₂ b'} (≡→≈ eq') ∘ (g' .famf .transf j ∘ y .fam .subst e)
          ≈⟨ ∘-cong ≈-refl (g' .famf .natural e) ⟩
            Cf .subst {p .func j} {inj₂ b'} (≡→≈ eq') ∘ (Cf .subst {p .func i} {p .func j} (p .func-resp-≈ e) ∘ g' .famf .transf i)
          ≈⟨ ≈-sym (assoc _ _ _) ⟩
            (Cf .subst {p .func j} {inj₂ b'} (≡→≈ eq') ∘ Cf .subst {p .func i} {p .func j} (p .func-resp-≈ e)) ∘ g' .famf .transf i
          ≈⟨ ∘-cong (≈-sym (Cf .trans* {p .func i} {p .func j} {inj₂ b'} (≡→≈ eq') (p .func-resp-≈ e))) ≈-refl ⟩
            Cf .subst {p .func i} {inj₂ b'} (Ci .isEquivalence .trans {p .func i} {p .func j} {inj₂ b'} (p .func-resp-≈ e) (≡→≈ eq')) ∘ g' .famf .transf i
          ≈⟨ ∘-cong (Cf .trans* {p .func i} {inj₂ b} {inj₂ b'} (substₚ₂ eq eq' (p .func-resp-≈ e)) (≡→≈ eq)) ≈-refl ⟩
            (Cf .subst {inj₂ b} {inj₂ b'} (substₚ₂ eq eq' (p .func-resp-≈ e)) ∘ Cf .subst {p .func i} {inj₂ b} (≡→≈ eq)) ∘ g' .famf .transf i
          ≈⟨ assoc _ _ _ ⟩
            Cf .subst {inj₂ b} {inj₂ b'} (substₚ₂ eq eq' (p .func-resp-≈ e)) ∘ (Cf .subst {p .func i} {inj₂ b} (≡→≈ eq) ∘ g' .famf .transf i)
          ∎
          where
            Cf = (coprod x₁ x₂) .fam
            Ci = (coprod x₁ x₂) .idx
            open ≈-Reasoning isEquiv

        fwd : Mor (coprod Y₁ Y₂) y
        fwd .idxf .func (inj₁ (i , _)) = i
        fwd .idxf .func (inj₂ (i , _)) = i
        fwd .idxf .func-resp-≈ {inj₁ (i , _)} {inj₁ (j , _)} e = e
        fwd .idxf .func-resp-≈ {inj₂ (i , _)} {inj₂ (j , _)} e = e
        fwd .idxf .func-resp-≈ {inj₁ _} {inj₂ _} ()
        fwd .idxf .func-resp-≈ {inj₂ _} {inj₁ _} ()
        fwd .famf .transf (inj₁ (i , _)) = id (y .fam .fm i)
        fwd .famf .transf (inj₂ (i , _)) = id (y .fam .fm i)
        fwd .famf .natural {inj₁ (i , _)} {inj₁ (j , _)} e = ≈-trans id-left (≈-sym id-right)
        fwd .famf .natural {inj₂ (i , _)} {inj₂ (j , _)} e = ≈-trans id-left (≈-sym id-right)
        fwd .famf .natural {inj₁ _} {inj₂ _} ()
        fwd .famf .natural {inj₂ _} {inj₁ _} ()

        ⊥-elimₚ : ∀ {ℓ ℓ'} {A : Prop ℓ'} → prop.⊥ {ℓ} → A
        ⊥-elimₚ ()

        decide : (s : x₁ .idx .Carrier ⊎ x₂ .idx .Carrier) →
                 (Σ[ a ∈ x₁ .idx .Carrier ] (s ≡ inj₁ a)) ⊎ (Σ[ b ∈ x₂ .idx .Carrier ] (s ≡ inj₂ b))
        decide (inj₁ a) = inj₁ (a , ≡.refl)
        decide (inj₂ b) = inj₂ (b , ≡.refl)

        build : (i : y .idx .Carrier) →
                (Σ[ a ∈ x₁ .idx .Carrier ] (p .func i ≡ inj₁ a)) ⊎ (Σ[ b ∈ x₂ .idx .Carrier ] (p .func i ≡ inj₂ b)) →
                (coprod Y₁ Y₂) .idx .Carrier
        build i (inj₁ (a , eq)) = inj₁ (i , a , eq)
        build i (inj₂ (b , eq)) = inj₂ (i , b , eq)

        build-resp : {i j : y .idx .Carrier}
                     (di : (Σ[ a ∈ x₁ .idx .Carrier ] (p .func i ≡ inj₁ a)) ⊎ (Σ[ b ∈ x₂ .idx .Carrier ] (p .func i ≡ inj₂ b)))
                     (dj : (Σ[ a ∈ x₁ .idx .Carrier ] (p .func j ≡ inj₁ a)) ⊎ (Σ[ b ∈ x₂ .idx .Carrier ] (p .func j ≡ inj₂ b))) →
                     (coprod x₁ x₂) .idx ._≈_ (p .func i) (p .func j) → y .idx ._≈_ i j →
                     (coprod Y₁ Y₂) .idx ._≈_ (build _ di) (build _ dj)
        build-resp (inj₁ (a , eq)) (inj₁ (a' , eq')) es i≈j = i≈j
        build-resp (inj₂ (b , eq)) (inj₂ (b' , eq')) es i≈j = i≈j
        build-resp (inj₁ (a , eq)) (inj₂ (b' , eq')) es i≈j = ⊥-elimₚ (substₚ₂ eq eq' es)
        build-resp (inj₂ (b , eq)) (inj₁ (a' , eq')) es i≈j = ⊥-elimₚ (substₚ₂ eq eq' es)

        build-fib : (i : y .idx .Carrier)
                    (d : (Σ[ a ∈ x₁ .idx .Carrier ] (p .func i ≡ inj₁ a)) ⊎ (Σ[ b ∈ x₂ .idx .Carrier ] (p .func i ≡ inj₂ b))) →
                    y .fam .fm i ⇒ (coprod Y₁ Y₂) .fam .fm (build i d)
        build-fib i (inj₁ (a , eq)) = id (y .fam .fm i)
        build-fib i (inj₂ (b , eq)) = id (y .fam .fm i)

        build-fib-nat : {i j : y .idx .Carrier}
                        (di : (Σ[ a ∈ x₁ .idx .Carrier ] (p .func i ≡ inj₁ a)) ⊎ (Σ[ b ∈ x₂ .idx .Carrier ] (p .func i ≡ inj₂ b)))
                        (dj : (Σ[ a ∈ x₁ .idx .Carrier ] (p .func j ≡ inj₁ a)) ⊎ (Σ[ b ∈ x₂ .idx .Carrier ] (p .func j ≡ inj₂ b)))
                        (es : (coprod x₁ x₂) .idx ._≈_ (p .func i) (p .func j)) (e : y .idx ._≈_ i j) →
                        (build-fib _ dj ∘ y .fam .subst e) ≈C ((coprod Y₁ Y₂) .fam .subst {build _ di} {build _ dj} (build-resp di dj es e) ∘ build-fib _ di)
        build-fib-nat (inj₁ (a , eq)) (inj₁ (a' , eq')) es e = ≈-trans id-left (≈-sym id-right)
        build-fib-nat (inj₂ (b , eq)) (inj₂ (b' , eq')) es e = ≈-trans id-left (≈-sym id-right)
        build-fib-nat (inj₁ (a , eq)) (inj₂ (b' , eq')) es e = ⊥-elimₚ (substₚ₂ eq eq' es)
        build-fib-nat (inj₂ (b , eq)) (inj₁ (a' , eq')) es e = ⊥-elimₚ (substₚ₂ eq eq' es)

        bwd : Mor y (coprod Y₁ Y₂)
        bwd .idxf .func i = build i (decide (p .func i))
        bwd .idxf .func-resp-≈ {i} {j} i≈j = build-resp (decide (p .func i)) (decide (p .func j)) (p .func-resp-≈ i≈j) i≈j
        bwd .famf .transf i = build-fib i (decide (p .func i))
        bwd .famf .natural {i} {j} e = build-fib-nat (decide (p .func i)) (decide (p .func j)) (p .func-resp-≈ e) e

        -- fwd recovers the index after bwd, for any classification.
        fwd-bwd-idx : (i : y .idx .Carrier)
                      (d : (Σ[ a ∈ x₁ .idx .Carrier ] (p .func i ≡ inj₁ a)) ⊎ (Σ[ b ∈ x₂ .idx .Carrier ] (p .func i ≡ inj₂ b))) →
                      y .idx ._≈_ (fwd .idxf .func (build i d)) i
        fwd-bwd-idx i (inj₁ (a , eq)) = y .idx .isEquivalence .refl
        fwd-bwd-idx i (inj₂ (b , eq)) = y .idx .isEquivalence .refl

        -- bwd recovers a tagged index after fwd.  Case the decision itself; the
        -- carried witness rules out the cross-side branch.
        bwd-fwd₁ : (i : y .idx .Carrier) (a : x₁ .idx .Carrier) (eq : p .func i ≡ inj₁ a)
                   (d : (Σ[ a ∈ x₁ .idx .Carrier ] (p .func i ≡ inj₁ a)) ⊎ (Σ[ b ∈ x₂ .idx .Carrier ] (p .func i ≡ inj₂ b))) →
                   (coprod Y₁ Y₂) .idx ._≈_ (build i d) (inj₁ (i , a , eq))
        bwd-fwd₁ i a eq (inj₁ (a' , eq')) = y .idx .isEquivalence .refl
        bwd-fwd₁ i a eq (inj₂ (b' , eq')) = ⊥-elimₚ (substₚ₂ eq eq' ((coprod x₁ x₂) .idx .isEquivalence .refl {p .func i}))

        bwd-fwd₂ : (i : y .idx .Carrier) (b : x₂ .idx .Carrier) (eq : p .func i ≡ inj₂ b)
                   (d : (Σ[ a ∈ x₁ .idx .Carrier ] (p .func i ≡ inj₁ a)) ⊎ (Σ[ b ∈ x₂ .idx .Carrier ] (p .func i ≡ inj₂ b))) →
                   (coprod Y₁ Y₂) .idx ._≈_ (build i d) (inj₂ (i , b , eq))
        bwd-fwd₂ i b eq (inj₁ (a' , eq')) = ⊥-elimₚ (substₚ₂ eq' eq ((coprod x₁ x₂) .idx .isEquivalence .refl {p .func i}))
        bwd-fwd₂ i b eq (inj₂ (b' , eq')) = y .idx .isEquivalence .refl

        bwd-fwd-idx : (c : (coprod Y₁ Y₂) .idx .Carrier) →
                      (coprod Y₁ Y₂) .idx ._≈_ (bwd .idxf .func (fwd .idxf .func c)) c
        bwd-fwd-idx (inj₁ (i , a , eq)) = bwd-fwd₁ i a eq (decide (p .func i))
        bwd-fwd-idx (inj₂ (i , b , eq)) = bwd-fwd₂ i b eq (decide (p .func i))

        -- After casing the decision the fibre maps are identities and the index
        -- coercion is reflexive (--prop), so the round-trip fibre is the identity.
        fwd∘bwd-fib : (i : y .idx .Carrier)
                      (d : (Σ[ a ∈ x₁ .idx .Carrier ] (p .func i ≡ inj₁ a)) ⊎ (Σ[ b ∈ x₂ .idx .Carrier ] (p .func i ≡ inj₂ b))) →
                      (y .fam .subst (fwd-bwd-idx i d) ∘ (id _ ∘ (fwd .famf .transf (build i d) ∘ build-fib i d))) ≈C id (y .fam .fm i)
        fwd∘bwd-fib i (inj₁ (a , eq)) = ≈-trans (∘-cong (y .fam .refl*) (≈-trans (∘-cong ≈-refl id-left) id-left)) id-left
        fwd∘bwd-fib i (inj₂ (b , eq)) = ≈-trans (∘-cong (y .fam .refl*) (≈-trans (∘-cong ≈-refl id-left) id-left)) id-left

        bwd∘fwd-fib₁ : (i : y .idx .Carrier) (a : x₁ .idx .Carrier) (eq : p .func i ≡ inj₁ a)
                       (d : (Σ[ a ∈ x₁ .idx .Carrier ] (p .func i ≡ inj₁ a)) ⊎ (Σ[ b ∈ x₂ .idx .Carrier ] (p .func i ≡ inj₂ b))) →
                       ((coprod Y₁ Y₂) .fam .subst {build i d} {inj₁ (i , a , eq)} (bwd-fwd₁ i a eq d) ∘ (id _ ∘ (build-fib i d ∘ id _))) ≈C id ((coprod Y₁ Y₂) .fam .fm (inj₁ (i , a , eq)))
        bwd∘fwd-fib₁ i a eq (inj₁ (a' , eq')) =
          ≈-trans (∘-cong (y .fam .refl*) (≈-trans (∘-cong ≈-refl id-left) id-left)) id-left
        bwd∘fwd-fib₁ i a eq (inj₂ (b' , eq')) =
          ⊥-elimₚ (substₚ₂ eq eq' ((coprod x₁ x₂) .idx .isEquivalence .refl {p .func i}))

        bwd∘fwd-fib₂ : (i : y .idx .Carrier) (b : x₂ .idx .Carrier) (eq : p .func i ≡ inj₂ b)
                       (d : (Σ[ a ∈ x₁ .idx .Carrier ] (p .func i ≡ inj₁ a)) ⊎ (Σ[ b ∈ x₂ .idx .Carrier ] (p .func i ≡ inj₂ b))) →
                       ((coprod Y₁ Y₂) .fam .subst {build i d} {inj₂ (i , b , eq)} (bwd-fwd₂ i b eq d) ∘ (id _ ∘ (build-fib i d ∘ id _))) ≈C id ((coprod Y₁ Y₂) .fam .fm (inj₂ (i , b , eq)))
        bwd∘fwd-fib₂ i b eq (inj₂ (b' , eq')) =
          ≈-trans (∘-cong (y .fam .refl*) (≈-trans (∘-cong ≈-refl id-left) id-left)) id-left
        bwd∘fwd-fib₂ i b eq (inj₁ (a' , eq')) =
          ⊥-elimₚ (substₚ₂ eq' eq ((coprod x₁ x₂) .idx .isEquivalence .refl {p .func i}))

        h : Category.Iso cat (coprod Y₁ Y₂) y
        h .Category.Iso.fwd = fwd
        h .Category.Iso.bwd = bwd
        h .Category.Iso.fwd∘bwd≈id .idxf-eq ._≈s_.func-eq {i} i≈i' =
          y .idx .isEquivalence .trans (fwd-bwd-idx i (decide (p .func i))) i≈i'
        h .Category.Iso.fwd∘bwd≈id .famf-eq ._≃f_.transf-eq {i} =
          fwd∘bwd-fib i (decide (p .func i))
        h .Category.Iso.bwd∘fwd≈id .idxf-eq ._≈s_.func-eq {c} {c'} c≈c' =
          (coprod Y₁ Y₂) .idx .isEquivalence .trans {bwd .idxf .func (fwd .idxf .func c)} {c} {c'} (bwd-fwd-idx c) c≈c'
        h .Category.Iso.bwd∘fwd≈id .famf-eq ._≃f_.transf-eq {inj₁ (i , a , eq)} =
          bwd∘fwd-fib₁ i a eq (decide (p .func i))
        h .Category.Iso.bwd∘fwd≈id .famf-eq ._≃f_.transf-eq {inj₂ (i , b , eq)} =
          bwd∘fwd-fib₂ i b eq (decide (p .func i))

        fwd∘bwd-x : (s : x .idx .Carrier) → x .idx ._≈_ (f .Category.Iso.fwd .idxf .func (f .Category.Iso.bwd .idxf .func s)) s
        fwd∘bwd-x s = f .Category.Iso.fwd∘bwd≈id .idxf-eq ._≈s_.func-eq {s} {s} (x .idx .isEquivalence .refl)

        eq₁σ : (i : y .idx .Carrier) (a : x₁ .idx .Carrier) (eq : p .func i ≡ inj₁ a) →
               x .idx ._≈_ (f .Category.Iso.fwd .idxf .func (inj₁ a)) (g .idxf .func i)
        eq₁σ i a eq = x .idx .isEquivalence .trans (f .Category.Iso.fwd .idxf .func-resp-≈ (≡→≈ (≡.sym eq))) (fwd∘bwd-x (g .idxf .func i))

        f-roundtrip₁ : (i : y .idx .Carrier) (a : x₁ .idx .Carrier) (eq : p .func i ≡ inj₁ a) →
                       (x .fam .subst (eq₁σ i a eq) ∘ (f .Category.Iso.fwd .famf .transf (inj₁ a) ∘ ((coprod x₁ x₂) .fam .subst {p .func i} {inj₁ a} (≡→≈ eq) ∘ f .Category.Iso.bwd .famf .transf (g .idxf .func i)))) ≈C
                       id (x .fam .fm (g .idxf .func i))
        f-roundtrip₁ i a eq = begin
            x .fam .subst (eq₁σ i a eq) ∘ (f .Category.Iso.fwd .famf .transf (inj₁ a) ∘ ((coprod x₁ x₂) .fam .subst {p .func i} {inj₁ a} (≡→≈ eq) ∘ f .Category.Iso.bwd .famf .transf (g .idxf .func i)))
          ≈⟨ ∘-cong ≈-refl (≈-sym (assoc _ _ _)) ⟩
            x .fam .subst (eq₁σ i a eq) ∘ ((f .Category.Iso.fwd .famf .transf (inj₁ a) ∘ (coprod x₁ x₂) .fam .subst {p .func i} {inj₁ a} (≡→≈ eq)) ∘ f .Category.Iso.bwd .famf .transf (g .idxf .func i))
          ≈⟨ ∘-cong ≈-refl (∘-cong (f .Category.Iso.fwd .famf .natural {p .func i} {inj₁ a} (≡→≈ eq)) ≈-refl) ⟩
            x .fam .subst (eq₁σ i a eq) ∘ ((x .fam .subst (f .Category.Iso.fwd .idxf .func-resp-≈ (≡→≈ eq)) ∘ f .Category.Iso.fwd .famf .transf (p .func i)) ∘ f .Category.Iso.bwd .famf .transf (g .idxf .func i))
          ≈⟨ ∘-cong ≈-refl (assoc _ _ _) ⟩
            x .fam .subst (eq₁σ i a eq) ∘ (x .fam .subst (f .Category.Iso.fwd .idxf .func-resp-≈ (≡→≈ eq)) ∘ (f .Category.Iso.fwd .famf .transf (p .func i) ∘ f .Category.Iso.bwd .famf .transf (g .idxf .func i)))
          ≈⟨ ≈-sym (assoc _ _ _) ⟩
            (x .fam .subst (eq₁σ i a eq) ∘ x .fam .subst (f .Category.Iso.fwd .idxf .func-resp-≈ (≡→≈ eq))) ∘ (f .Category.Iso.fwd .famf .transf (p .func i) ∘ f .Category.Iso.bwd .famf .transf (g .idxf .func i))
          ≈⟨ ∘-cong (≈-sym (x .fam .trans* (eq₁σ i a eq) (f .Category.Iso.fwd .idxf .func-resp-≈ (≡→≈ eq)))) ≈-refl ⟩
            x .fam .subst (x .idx .isEquivalence .trans (f .Category.Iso.fwd .idxf .func-resp-≈ (≡→≈ eq)) (eq₁σ i a eq)) ∘ (f .Category.Iso.fwd .famf .transf (p .func i) ∘ f .Category.Iso.bwd .famf .transf (g .idxf .func i))
          ≈⟨ ∘-cong ≈-refl (≈-sym id-left) ⟩
            x .fam .subst (x .idx .isEquivalence .trans (f .Category.Iso.fwd .idxf .func-resp-≈ (≡→≈ eq)) (eq₁σ i a eq)) ∘ (id _ ∘ (f .Category.Iso.fwd .famf .transf (p .func i) ∘ f .Category.Iso.bwd .famf .transf (g .idxf .func i)))
          ≈⟨ f .Category.Iso.fwd∘bwd≈id .famf-eq ._≃f_.transf-eq {g .idxf .func i} ⟩
            id (x .fam .fm (g .idxf .func i))
          ∎ where open ≈-Reasoning isEquiv

        eq₂σ : (i : y .idx .Carrier) (b : x₂ .idx .Carrier) (eq : p .func i ≡ inj₂ b) →
               x .idx ._≈_ (f .Category.Iso.fwd .idxf .func (inj₂ b)) (g .idxf .func i)
        eq₂σ i b eq = x .idx .isEquivalence .trans (f .Category.Iso.fwd .idxf .func-resp-≈ (≡→≈ (≡.sym eq))) (fwd∘bwd-x (g .idxf .func i))

        f-roundtrip₂ : (i : y .idx .Carrier) (b : x₂ .idx .Carrier) (eq : p .func i ≡ inj₂ b) →
                       (x .fam .subst (eq₂σ i b eq) ∘ (f .Category.Iso.fwd .famf .transf (inj₂ b) ∘ ((coprod x₁ x₂) .fam .subst {p .func i} {inj₂ b} (≡→≈ eq) ∘ f .Category.Iso.bwd .famf .transf (g .idxf .func i)))) ≈C id (x .fam .fm (g .idxf .func i))
        f-roundtrip₂ i b eq = begin
            x .fam .subst (eq₂σ i b eq) ∘ (f .Category.Iso.fwd .famf .transf (inj₂ b) ∘ ((coprod x₁ x₂) .fam .subst {p .func i} {inj₂ b} (≡→≈ eq) ∘ f .Category.Iso.bwd .famf .transf (g .idxf .func i)))
          ≈⟨ ∘-cong ≈-refl (≈-sym (assoc _ _ _)) ⟩
            x .fam .subst (eq₂σ i b eq) ∘ ((f .Category.Iso.fwd .famf .transf (inj₂ b) ∘ (coprod x₁ x₂) .fam .subst {p .func i} {inj₂ b} (≡→≈ eq)) ∘ f .Category.Iso.bwd .famf .transf (g .idxf .func i))
          ≈⟨ ∘-cong ≈-refl (∘-cong (f .Category.Iso.fwd .famf .natural {p .func i} {inj₂ b} (≡→≈ eq)) ≈-refl) ⟩
            x .fam .subst (eq₂σ i b eq) ∘ ((x .fam .subst (f .Category.Iso.fwd .idxf .func-resp-≈ (≡→≈ eq)) ∘ f .Category.Iso.fwd .famf .transf (p .func i)) ∘ f .Category.Iso.bwd .famf .transf (g .idxf .func i))
          ≈⟨ ∘-cong ≈-refl (assoc _ _ _) ⟩
            x .fam .subst (eq₂σ i b eq) ∘ (x .fam .subst (f .Category.Iso.fwd .idxf .func-resp-≈ (≡→≈ eq)) ∘ (f .Category.Iso.fwd .famf .transf (p .func i) ∘ f .Category.Iso.bwd .famf .transf (g .idxf .func i)))
          ≈⟨ ≈-sym (assoc _ _ _) ⟩
            (x .fam .subst (eq₂σ i b eq) ∘ x .fam .subst (f .Category.Iso.fwd .idxf .func-resp-≈ (≡→≈ eq))) ∘ (f .Category.Iso.fwd .famf .transf (p .func i) ∘ f .Category.Iso.bwd .famf .transf (g .idxf .func i))
          ≈⟨ ∘-cong (≈-sym (x .fam .trans* (eq₂σ i b eq) (f .Category.Iso.fwd .idxf .func-resp-≈ (≡→≈ eq)))) ≈-refl ⟩
            x .fam .subst (x .idx .isEquivalence .trans (f .Category.Iso.fwd .idxf .func-resp-≈ (≡→≈ eq)) (eq₂σ i b eq)) ∘ (f .Category.Iso.fwd .famf .transf (p .func i) ∘ f .Category.Iso.bwd .famf .transf (g .idxf .func i))
          ≈⟨ ∘-cong ≈-refl (≈-sym id-left) ⟩
            x .fam .subst (x .idx .isEquivalence .trans (f .Category.Iso.fwd .idxf .func-resp-≈ (≡→≈ eq)) (eq₂σ i b eq)) ∘ (id _ ∘ (f .Category.Iso.fwd .famf .transf (p .func i) ∘ f .Category.Iso.bwd .famf .transf (g .idxf .func i)))
          ≈⟨ f .Category.Iso.fwd∘bwd≈id .famf-eq ._≃f_.transf-eq {g .idxf .func i} ⟩
            id (x .fam .fm (g .idxf .func i))
          ∎ where open ≈-Reasoning isEquiv

        stb : StableBits f g
        stb .StableBits.y₁ = Y₁
        stb .StableBits.y₂ = Y₂
        stb .StableBits.h₁ = h₁
        stb .StableBits.h₂ = h₂
        stb .StableBits.h = h
        stb .StableBits.eq₁ .idxf-eq ._≈s_.func-eq {i , a , eq} {i' , a' , eq'} c≈c' =
          x .idx .isEquivalence .trans (eq₁σ i a eq) (g .idxf .func-resp-≈ c≈c')
        stb .StableBits.eq₁ .famf-eq ._≃f_.transf-eq {i , a , eq} = begin
            x .fam .subst (eq₁σ i a eq) ∘ (id _ ∘ (f .Category.Iso.fwd .famf .transf (inj₁ a) ∘ (id _ ∘ (id _ ∘ ((coprod x₁ x₂) .fam .subst {p .func i} {inj₁ a} (≡→≈ eq) ∘ (id _ ∘ (f .Category.Iso.bwd .famf .transf (g .idxf .func i) ∘ g .famf .transf i)))))))
          ≈⟨ ∘-cong ≈-refl (≈-trans id-left (∘-cong ≈-refl (≈-trans (≈-trans id-left id-left) (∘-cong ≈-refl id-left)))) ⟩
            x .fam .subst (eq₁σ i a eq) ∘ (f .Category.Iso.fwd .famf .transf (inj₁ a) ∘ ((coprod x₁ x₂) .fam .subst {p .func i} {inj₁ a} (≡→≈ eq) ∘ (f .Category.Iso.bwd .famf .transf (g .idxf .func i) ∘ g .famf .transf i)))
          ≈⟨ ∘-cong ≈-refl (∘-cong ≈-refl (≈-sym (assoc _ _ _))) ⟩
            x .fam .subst (eq₁σ i a eq) ∘ (f .Category.Iso.fwd .famf .transf (inj₁ a) ∘ (((coprod x₁ x₂) .fam .subst {p .func i} {inj₁ a} (≡→≈ eq) ∘ f .Category.Iso.bwd .famf .transf (g .idxf .func i)) ∘ g .famf .transf i))
          ≈⟨ ∘-cong ≈-refl (≈-sym (assoc _ _ _)) ⟩
            x .fam .subst (eq₁σ i a eq) ∘ ((f .Category.Iso.fwd .famf .transf (inj₁ a) ∘ ((coprod x₁ x₂) .fam .subst {p .func i} {inj₁ a} (≡→≈ eq) ∘ f .Category.Iso.bwd .famf .transf (g .idxf .func i))) ∘ g .famf .transf i)
          ≈⟨ ≈-sym (assoc _ _ _) ⟩
            (x .fam .subst (eq₁σ i a eq) ∘ (f .Category.Iso.fwd .famf .transf (inj₁ a) ∘ ((coprod x₁ x₂) .fam .subst {p .func i} {inj₁ a} (≡→≈ eq) ∘ f .Category.Iso.bwd .famf .transf (g .idxf .func i)))) ∘ g .famf .transf i
          ≈⟨ ∘-cong (f-roundtrip₁ i a eq) ≈-refl ⟩
            id _ ∘ g .famf .transf i
          ≈⟨ id-left ⟩
            g .famf .transf i
          ≈˘⟨ ≈-trans id-left (≈-trans (∘-cong ≈-refl (≈-trans id-left id-left)) id-right) ⟩
            id _ ∘ (g .famf .transf i ∘ (id _ ∘ (id _ ∘ id _)))
          ∎ where open ≈-Reasoning isEquiv
        stb .StableBits.eq₂ .idxf-eq ._≈s_.func-eq {i , b , eq} {i' , b' , eq'} c≈c' =
          x .idx .isEquivalence .trans (eq₂σ i b eq) (g .idxf .func-resp-≈ c≈c')
        stb .StableBits.eq₂ .famf-eq ._≃f_.transf-eq {i , b , eq} = begin
            x .fam .subst (eq₂σ i b eq) ∘ (id _ ∘ (f .Category.Iso.fwd .famf .transf (inj₂ b) ∘ (id _ ∘ (id _ ∘ ((coprod x₁ x₂) .fam .subst {p .func i} {inj₂ b} (≡→≈ eq) ∘ (id _ ∘ (f .Category.Iso.bwd .famf .transf (g .idxf .func i) ∘ g .famf .transf i)))))))
          ≈⟨ ∘-cong ≈-refl (≈-trans id-left (∘-cong ≈-refl (≈-trans (≈-trans id-left id-left) (∘-cong ≈-refl id-left)))) ⟩
            x .fam .subst (eq₂σ i b eq) ∘ (f .Category.Iso.fwd .famf .transf (inj₂ b) ∘ ((coprod x₁ x₂) .fam .subst {p .func i} {inj₂ b} (≡→≈ eq) ∘ (f .Category.Iso.bwd .famf .transf (g .idxf .func i) ∘ g .famf .transf i)))
          ≈⟨ ∘-cong ≈-refl (∘-cong ≈-refl (≈-sym (assoc _ _ _))) ⟩
            x .fam .subst (eq₂σ i b eq) ∘ (f .Category.Iso.fwd .famf .transf (inj₂ b) ∘ (((coprod x₁ x₂) .fam .subst {p .func i} {inj₂ b} (≡→≈ eq) ∘ f .Category.Iso.bwd .famf .transf (g .idxf .func i)) ∘ g .famf .transf i))
          ≈⟨ ∘-cong ≈-refl (≈-sym (assoc _ _ _)) ⟩
            x .fam .subst (eq₂σ i b eq) ∘ ((f .Category.Iso.fwd .famf .transf (inj₂ b) ∘ ((coprod x₁ x₂) .fam .subst {p .func i} {inj₂ b} (≡→≈ eq) ∘ f .Category.Iso.bwd .famf .transf (g .idxf .func i))) ∘ g .famf .transf i)
          ≈⟨ ≈-sym (assoc _ _ _) ⟩
            (x .fam .subst (eq₂σ i b eq) ∘ (f .Category.Iso.fwd .famf .transf (inj₂ b) ∘ ((coprod x₁ x₂) .fam .subst {p .func i} {inj₂ b} (≡→≈ eq) ∘ f .Category.Iso.bwd .famf .transf (g .idxf .func i)))) ∘ g .famf .transf i
          ≈⟨ ∘-cong (f-roundtrip₂ i b eq) ≈-refl ⟩
            id _ ∘ g .famf .transf i
          ≈⟨ id-left ⟩
            g .famf .transf i
          ≈˘⟨ ≈-trans id-left (≈-trans (∘-cong ≈-refl (≈-trans id-left id-left)) id-right) ⟩
            id _ ∘ (g .famf .transf i ∘ (id _ ∘ (id _ ∘ id _)))
          ∎ where open ≈-Reasoning isEquiv

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
