{-# OPTIONS --postfix-projections --prop #-}

module intrinsic-derivative where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties using (*-zeroʳ)
open import Data.Fin using (Fin; zero; suc; _≟_; splitAt; _↑ˡ_; _↑ʳ_)
open import Data.Fin.Properties using (splitAt-↑ˡ; splitAt-↑ʳ)
open import Data.Product using (_×_; proj₁; proj₂; _,_; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym; cong₂; subst)

data 𝔹 : Set where
  I O : 𝔹

_⊑_ : 𝔹 → 𝔹 → Set
I ⊑ I = ⊤
I ⊑ O = ⊥
O ⊑ y = ⊤

⊑-refl : ∀ {x} → x ⊑ x
⊑-refl {I} = tt
⊑-refl {O} = tt

⊑-reflexive : ∀ {x y} → x ≡ y → x ⊑ y
⊑-reflexive refl = ⊑-refl

⊑-trans : ∀ {x y z} → x ⊑ y → y ⊑ z → x ⊑ z
⊑-trans {I} {I} {I} ϕ ψ = tt
⊑-trans {O} {I} {I} ϕ ψ = tt
⊑-trans {O} {O} {I} ϕ ψ = tt
⊑-trans {O} {O} {O} ϕ ψ = tt

I-top : ∀ {x} → x ⊑ I
I-top {I} = tt
I-top {O} = tt

_∨_ : 𝔹 → 𝔹 → 𝔹
I ∨ y = I
O ∨ y = y

upper₁ : ∀ {x y} → x ⊑ (x ∨ y)
upper₁ {I} {y} = tt
upper₁ {O} {y} = tt

upper₂ : ∀ {x y} → y ⊑ (x ∨ y)
upper₂ {I} {I} = tt
upper₂ {I} {O} = tt
upper₂ {O} {y} = ⊑-refl

least-∨ : ∀ {x y z} → x ⊑ z → y ⊑ z → (x ∨ y) ⊑ z
least-∨ {I} {y} {z} ϕ ψ = ϕ
least-∨ {O} {y} {z} ϕ ψ = ψ

_∧_ : 𝔹 → 𝔹 → 𝔹
I ∧ x = x
O ∧ y = O

lower₁ : ∀ {x y} → (x ∧ y) ⊑ x
lower₁ {I} {y} = I-top
lower₁ {O} {y} = tt

lower₂ : ∀ {x y} → (x ∧ y) ⊑ y
lower₂ {I} {y} = ⊑-refl
lower₂ {O} {y} = tt

greatest : ∀ {x y z} → x ⊑ y → x ⊑ z → x ⊑ (y ∧ z)
greatest {I} {I} {I} ϕ ψ = tt
greatest {O} {y} {z} ϕ ψ = tt

⋁ : ∀ {n} → (Fin n → 𝔹) → 𝔹
⋁ {zero} f = O
⋁ {suc n} f = f zero ∨ ⋁ (λ i → f (suc i))

upper : ∀ {n} {f : Fin n → 𝔹} (i : Fin n) → f i ⊑ ⋁ f
upper {n} zero = upper₁
upper {n} (suc i) = ⊑-trans (upper i) upper₂

least : ∀ {n} {x} {f : Fin n → 𝔹} → (∀ i → f i ⊑ x) → ⋁ f ⊑ x
least {zero}  f⊑x = tt
least {suc n} f⊑x = least-∨ (f⊑x zero) (least (λ i → f⊑x (suc i)))

∨-interchange : ∀ {w x y z} → ((w ∨ x) ∨ (y ∨ z)) ≡ ((w ∨ y) ∨ (x ∨ z))
∨-interchange {I} {x} {y} {z} = refl
∨-interchange {O} {I} {I} {z} = refl
∨-interchange {O} {I} {O} {z} = refl
∨-interchange {O} {O} {y} {z} = refl

⋁-∨ : ∀ {n} {f g : Fin n → 𝔹} → (⋁ f) ∨ (⋁ g) ≡ ⋁ (λ i → f i ∨ g i)
⋁-∨ {zero} {f} {g} = refl
⋁-∨ {suc n} {f} {g} = trans (∨-interchange {f zero} {_} {g zero}) (cong (_∨_ (f zero ∨ g zero)) (⋁-∨ {n} {λ i → f (suc i)} {λ i → g (suc i)}))

⋁-cong : ∀ {n} {f g : Fin n → 𝔹} → (∀ i → f i ≡ g i) → ⋁ f ≡ ⋁ g
⋁-cong {zero} {f} {g} eq = refl
⋁-cong {suc n} {f} {g} eq = cong₂ _∨_ (eq zero) (⋁-cong {n} {λ i → f (suc i)} {λ i → g (suc i)} λ i → eq (suc i))

antisym : ∀ {x y} → x ⊑ y → y ⊑ x → x ≡ y
antisym {I} {I} ϕ ψ = refl
antisym {O} {O} ϕ ψ = refl

∧-∨-distribˡ : ∀ {x y z} → ((x ∧ y) ∨ (x ∧ z)) ≡ (x ∧ (y ∨ z))
∧-∨-distribˡ {I} {y} {z} = refl
∧-∨-distribˡ {O} {y} {z} = refl

------------------------------------------------------------------------------
-- Vectors and Matricies of booleans
Matrix : ℕ → ℕ → Set
Matrix m n = Fin m → Fin n → 𝔹

Vec : ℕ → Set
Vec n = Fin n → 𝔹


_⊔_ : ∀ {n} → Vec n → Vec n → Vec n
(x ⊔ y) i = x i ∨ y i

∅ : ∀ {n} → Vec n
∅ i = O

_∙_ : ∀ {m n} → Matrix m n → Vec m → Vec n
(M ∙ x) i = ⋁ λ j → M j i ∧ x j

_≈V_ : ∀ {n} → Vec n → Vec n → Set
x ≈V y = ∀ i → x i ≡ y i

_≈M_ : ∀ {m n} → Matrix m n → Matrix m n → Set
M ≈M N = ∀ i j → M i j ≡ N i j

_∘M_ : ∀ {m n o} → Matrix n o → Matrix m n → Matrix m o
(M ∘M N) i j = ⋁ λ k → M k j ∧ N i k

infix 4 _≈V_ _≈M_

∙-preserve-∅ : ∀ {m n} (M : Matrix m n) → M ∙ ∅ ≈V ∅
∙-preserve-∅ M i = antisym (least {f = λ j → M j i ∧ O} (λ j → lower₂)) tt

∙-preserve-⊔ : ∀ {m n} (M : Matrix m n) (x y : Vec m) → (M ∙ x) ⊔ (M ∙ y) ≈V M ∙ (x ⊔ y)
∙-preserve-⊔ M x y j = trans (⋁-∨ {f = λ k → M k j ∧ x k} {g = λ k → M k j ∧ y k}) (⋁-cong {f = λ i → (M i j ∧ x i) ∨ (M i j ∧ y i)} {g = λ i → M i j ∧ (x i ∨ y i)} λ i → ∧-∨-distribˡ {M i j} {x i} {y i})

postulate
  f-ext : ∀ {A : Set} {B : A → Set} {f g : ∀ a → B a} → (∀ a → f a ≡ g a) → f ≡ g


------------------------------------------------------------------------------
module version1 where
  record Obj : Set₁ where
    field
      arity : ℕ
      dom   : Fin arity → Set
  open Obj

  El : Obj → Set
  El X = (i : Fin (X .arity)) → X .dom i

  -- Functions that carry correct but not necessarily complete
  -- dependency information
  record _⇒_ (X Y : Obj) : Set₁ where
    field
      func : El X → El Y
      deps : El X → Matrix (X .arity) (Y .arity)
      deps-ok : ∀ x x' j → (∀ i → deps x i j ≡ I → x i ≡ x' i) → func x j ≡ func x' j
      -- More generally: (⋀ λ i → deps x i j ⊸ X i .eq (x i) (x' i)) ⊸ Y j .eq (func x j) (func x' j)
  open _⇒_

  constant : ∀ {X Y} → El Y → X ⇒ Y
  constant y .func _ = y
  constant y .deps _ i j = O
  constant y .deps-ok = λ x x' j z → refl

  id : ∀ X → X ⇒ X
  id X .func x = x
  id X .deps x i j with i ≟ j
  ... | yes _ = I
  ... | no _ = O
  id X .deps-ok x x' j z with z j
  ... | z' with j ≟ j
  ... | yes _ = z' refl
  ... | no ¬j≡j with ¬j≡j refl
  ... | ()

  _∘_ : ∀ {X Y Z} → Y ⇒ Z → X ⇒ Y → X ⇒ Z
  (f ∘ g) .func x = f .func (g .func x)
  (f ∘ g) .deps x = f .deps (g .func x) ∘M g .deps x
  (f ∘ g) .deps-ok x x' j x₁ = f .deps-ok (g .func x) (g .func x') j
      (λ i f-dep-ij → g .deps-ok x x' i (λ i₁ x₂ → x₁ i₁ (antisym I-top (⊑-trans (greatest (⊑-reflexive (sym f-dep-ij)) (⊑-reflexive (sym x₂))) (upper {f = λ k → f .deps (g .func x) k j ∧ g .deps x i₁ k} i)))))

  -- Products
  prod : Obj → Obj → Obj
  prod X Y .arity = X .arity + Y .arity
  prod X Y .dom i = [ X .dom , Y .dom ] (splitAt (X .arity) i)

  is-eq : ∀ {n} → Fin n → Fin n → 𝔹
  is-eq i j with i ≟ j
  ... | yes _ = I
  ... | no _ = O

  is-eq-refl : ∀ {n} {i : Fin n} → is-eq i i ≡ I
  is-eq-refl {n} {i} with i ≟ i
  ... | yes refl = refl
  ... | no ¬i≡i with ¬i≡i refl
  ... | ()

  project₁ : ∀ {X Y} → prod X Y ⇒ X
  project₁ {X} {Y} .func x i = subst [ X .dom , Y .dom ] (splitAt-↑ˡ (X .arity) i (Y .arity)) (x (i ↑ˡ Y .arity))
  project₁ {X} {Y} .deps x i j = [ is-eq j , (λ _ → O) ] (splitAt (X .arity) i)
  project₁ {X} {Y} .deps-ok x x' j x₁ =
    cong
     (λ □ →
        subst [ X .dom , Y .dom ] (splitAt-↑ˡ (X .arity) j (Y .arity)) □)
     (x₁ (j ↑ˡ Y .arity)
         (trans (cong [ is-eq j , (λ _ → O) ] (splitAt-↑ˡ (X .arity) j (Y .arity))) is-eq-refl))

  project₂ : ∀ {X Y} → prod X Y ⇒ Y
  project₂ {X} {Y} .func x i = subst [ X .dom , Y .dom ] (splitAt-↑ʳ (X .arity) (Y .arity) i) (x (X .arity ↑ʳ i))
  project₂ {X} {Y} .deps x i j = [ (λ _ → O) , is-eq j ] (splitAt (X .arity) i)
  project₂ {X} {Y} .deps-ok x x' j x₁ =
    cong
      (λ □ → subst [ X .dom , Y .dom ] (splitAt-↑ʳ (X .arity) (Y .arity) j) □)
      (x₁ (X .arity ↑ʳ j)
          (trans (cong [ (λ _ → O) , is-eq j ] (splitAt-↑ʳ (X .arity) (Y .arity) j)) is-eq-refl))

  pair-func : ∀ {A B : Set} {X : A → Set} {Y : B → Set} →
              (f : ∀ a → X a) →
              (g : ∀ b → Y b) →
              (d : A ⊎ B) → [_,_] {C = λ _ → Set} X Y d
  pair-func f g (inj₁ x) = f x
  pair-func f g (inj₂ y) = g y


  pair : ∀ {W X Y} → W ⇒ X → W ⇒ Y → W ⇒ prod X Y
  pair {W} {X} {Y} f g .func w i = pair-func (f .func w) (g .func w) (splitAt (X .arity) i)
  pair {W} {X} {Y} f g .deps w i j = [ (f .deps w i) , (g .deps w i) ] (splitAt (X .arity) j)
  pair {W} {X} {Y} f g .deps-ok x x' j x₁ with splitAt (X .arity) j
  ... | inj₁ j₁ = f .deps-ok x x' j₁ x₁
  ... | inj₂ j₂ = g .deps-ok x x' j₂ x₁

  ------------------------------------------------------------------------------
  -- A function with interesting dependency structure

  set : Set → Obj
  set A .arity = 1
  set A .dom _ = A

  set-f : ∀ {A B} → (A → B) → set A ⇒ set B
  set-f f .func x _ = f (x zero)
  set-f f .deps _ _ _ = I
  set-f f .deps-ok x x' j ϕ = cong f (ϕ zero refl)

  is-zero : ℕ → 𝔹
  is-zero zero = I
  is-zero (suc n) = O

  is-not-zero : ℕ → 𝔹
  is-not-zero zero = O
  is-not-zero (suc n) = I

  add : prod (set ℕ) (set ℕ) ⇒ set ℕ
  add .func xy _ = xy zero + xy (suc zero)
  add .deps xy _ _ = I -- matrix of all 'I's; this suffices for all functions, but we needn't do that
  add .deps-ok x x' j ϕ = cong₂ _+_ (ϕ zero refl) (ϕ (suc zero) refl)

  mul : prod (set ℕ) (set ℕ) ⇒ set ℕ
  mul .func xy _ = xy zero * xy (suc zero)
  mul .deps xy zero       _ = is-zero (xy zero) ∨ is-not-zero (xy (suc zero))
  mul .deps xy (suc zero) _ = is-not-zero (xy zero) -- ∨ is-zero (xy (suc zero))
  mul .deps-ok x x' _ ϕ with ϕ zero
  mul .deps-ok x x' _ ϕ | ϕ₁ with ϕ (suc zero)
  mul .deps-ok x x' _ ϕ | ϕ₁ | ϕ₂ with x zero
  mul .deps-ok x x' _ ϕ | ϕ₁ | ϕ₂ | zero rewrite sym (ϕ₁ refl) = refl
  mul .deps-ok x x' _ ϕ | ϕ₁ | ϕ₂ | suc n with x (suc zero)
  mul .deps-ok x x' _ ϕ | ϕ₁ | ϕ₂ | suc n | zero rewrite sym (ϕ₂ refl) = trans (*-zeroʳ n) (sym (*-zeroʳ (x' zero)))
  mul .deps-ok x x' _ ϕ | ϕ₁ | ϕ₂ | suc n | suc m rewrite sym (ϕ₁ refl) rewrite sym (ϕ₂ refl) = refl

  -- This gives an interesting matrix of dependencies, including the
  -- forbidden "parallel" one!
  _ = {!mul .deps (λ { zero → 0 ; (suc zero) → 0 }) zero zero!}

  -- mul (0, 0) = (I O) -- or (O I) or (I I)
  -- mul (0, n) = (I O)
  -- mul (m, 0) = (O I)
  -- mul (m, n) = (I I)

  ite : ∀ {X : Set} → 𝔹 → X → X → X
  ite I x y = x
  ite O x y = y

  ifthenelse : ∀ {X} → prod (set 𝔹) (prod X X) ⇒ X
  ifthenelse .func x = ite (x zero) (project₁ .func (λ i → x (suc i))) (project₂ .func (λ i → x (suc i)))
  ifthenelse .deps x zero    j = I
  ifthenelse .deps x (suc i) j =
    ite (x zero) (project₁ .deps (λ i → x (suc i)) i j) (project₂ .deps (λ i → x (suc i)) i j)
  ifthenelse .deps-ok x x' j ϕ with (λ i → ϕ (suc i))
  ifthenelse .deps-ok x x' j ϕ | ϕ' with ϕ zero refl
  ifthenelse .deps-ok x x' j ϕ | ϕ' | ψ with x zero
  ifthenelse .deps-ok x x' j ϕ | ϕ' | ψ | I with x' zero
  ifthenelse .deps-ok x x' j ϕ | ϕ' | ψ | I | I = project₁ .deps-ok (λ i → x (suc i)) (λ i → x' (suc i)) j ϕ'
  ifthenelse .deps-ok x x' j ϕ | ϕ' | ψ | O with x' zero
  ifthenelse .deps-ok x x' j ϕ | ϕ' | ψ | O | O = project₂ .deps-ok (λ i → x (suc i)) (λ i → x' (suc i)) j ϕ'

------------------------------------------------------------------------------
module version2 where
  record Obj : Set₁ where
    field
      arity : ℕ
      dom   : Fin arity → Set
  open Obj

  El : Obj → Set
  El X = (i : Fin (X .arity)) → X .dom i

  -- Functions that carry correct but not necessarily complete
  -- dependency information
  record _⇒_ (X Y : Obj) : Set₁ where
    field
      func : El X → El Y
      deps : El X → Matrix (X .arity) (Y .arity)
      deps-ok : ∀ x x' i → (∀ i' → i ≡ i' ⊎ x i' ≡ x' i') → ∀ j → deps x i j ≡ O → func x j ≡ func x' j
      -- deps-ok : ∀ x x' i j → deps x i j ≡ O →
  open _⇒_

  constant : ∀ {X Y} → El Y → X ⇒ Y
  constant y .func _ = y
  constant y .deps _ i j = O
  constant y .deps-ok = λ x x' i z j z₁ → refl

  id : ∀ X → X ⇒ X
  id X .func x = x
  id X .deps x i j with i ≟ j
  ... | yes _ = I
  ... | no _ = O
  id X .deps-ok x x' j ϕ j' x₁ with j ≟ j'
  ... | no ¬j≡j' with ϕ j'
  ... | inj₁ j≡j' = ⊥-elim (¬j≡j' j≡j')
  ... | inj₂ eq = eq

  lemma₀ : ∀ {x y} → x ∨ y ≡ O → x ≡ O
  lemma₀ {O} eq = refl

  lemma₁ : ∀ {x y} → x ∨ y ≡ O → y ≡ O
  lemma₁ {O} {y} eq = eq


  lemma : ∀ {n} {f : Fin n → 𝔹} → ⋁ f ≡ O → ∀ k → f k ≡ O
  lemma {zero} {f} eq ()
  lemma {suc n} {f} eq zero = lemma₀ eq
  lemma {suc n} {f} eq (suc x) = lemma (lemma₁ eq) x

  ∧-split : ∀ {x y} → (x ∧ y) ≡ O → (x ≡ O × y ≡ I) ⊎ (y ≡ O)
  ∧-split {I} {y} eq = inj₂ eq
  ∧-split {O} {I} eq = inj₁ (eq , refl)
  ∧-split {O} {O} eq = inj₂ eq

  lemma₂ : ∀ {n} {f g : Fin n → 𝔹} → (∀ k → f k ∧ g k ≡ O) → (Σ[ k ∈ Fin n ] f k ≡ O × g k ≡ I) ⊎ (∀ k → g k ≡ O)
  lemma₂ {zero} {f} {g} ϕ = inj₂ (λ ())
  lemma₂ {suc n} {f} {g} ϕ with ∧-split {x = f zero} {y = g zero} (ϕ zero)
  ... | inj₁ eq = inj₁ (zero , eq)
  ... | inj₂ eq with lemma₂ {f = λ i → f (suc i)} (λ i → ϕ (suc i))
  ... | inj₁ (k , ψ) = inj₁ (suc k , ψ)
  ... | inj₂ ψ = inj₂ (λ { zero → eq ; (suc k) → ψ k })

{-
  -- FIXME: this doesn't work?
  _∘_ : ∀ {X Y Z} → Y ⇒ Z → X ⇒ Y → X ⇒ Z
  (f ∘ g) .func x = f .func (g .func x)
  (f ∘ g) .deps x = f .deps (g .func x) ∘M g .deps x
  _∘_ {X} {Y} {Z} f g  .deps-ok x x' j x₁ j₁ ϕ with lemma₂ {f = λ k → f .deps (g .func x) k j₁} (lemma ϕ)
  ... | inj₁ (k , ψ , χ) =
        f .deps-ok (g .func x) (g .func x') k
                   (λ k' → {!g .deps-ok x x' j ? k'!})
                   j₁ ψ
  ... | inj₂ ψ = cong (λ □ → f .func □ j₁) (f-ext (λ k → g .deps-ok x x' j x₁ k (ψ k)))
-}

------------------------------------------------------------------------------
{-
module with-sets where
  Matrix : ℕ → ℕ → Set₁
  Matrix m n = Fin m → Fin n → Set

  Vec : ℕ → Set₁
  Vec n = Fin n → Set

  _⊔_ : ∀ {n} → Vec n → Vec n → Vec n
  (x ⊔ y) i = x i ⊎ y i

  ∅ : ∀ {n} → Vec n
  ∅ i = ⊥

  _∙_ : ∀ {m n} → Matrix m n → Vec m → Vec n
  (M ∙ v) i = Σ[ j ∈ _ ] M j i × v j

  _≈_ : ∀ {n} → Vec n → Vec n → Set
  x ≈ y = ∀ i → (x i → y i) × (y i → x i)

  _≈M_ : ∀ {m n} → Matrix m n → Matrix m n → Set
  M ≈M N = ∀ i j → (M i j → N i j) × (N i j → M i j)

  _≈S_ : Set → Set → Set
  X ≈S Y = (X → Y) × (Y → X)

  infix 4 _≈_ _≈M_ _≈S_

  _∘M_ : ∀ {m n o} → Matrix n o → Matrix m n → Matrix m o
  (M ∘M N) i j = Σ[ k ∈ _ ] (M k j × N i k)

  -- Matrices are linear maps
  ∙-preserve-∅ : ∀ {m n} (M : Matrix m n) → M ∙ ∅ ≈ ∅
  ∙-preserve-∅ M i .proj₁ ()
  ∙-preserve-∅ M i .proj₂ ()

  ∙-preserve-⊔ : ∀ {m n} (M : Matrix m n) (x y : Vec m) → (M ∙ x) ⊔ (M ∙ y) ≈ M ∙ (x ⊔ y)
  ∙-preserve-⊔ M x y i .proj₁ (inj₁ (j , Mji , xj)) = j , Mji , inj₁ xj
  ∙-preserve-⊔ M x y i .proj₁ (inj₂ (j , Mji , yj)) = j , Mji , inj₂ yj
  ∙-preserve-⊔ M x y i .proj₂ (j , Mji , inj₁ xj) = inj₁ (j , Mji , xj)
  ∙-preserve-⊔ M x y i .proj₂ (j , Mji , inj₂ yj) = inj₂ (j , Mji , yj)



  record Obj : Set₁ where
    field
      arity : ℕ
      dom   : Fin arity → Set
  open Obj

  El : Obj → Set
  El X = (i : Fin (X .arity)) → X .dom i

  -- Functions that carry correct dependency information
  record _⇒_ (X Y : Obj) : Set₁ where
    field
      func : El X → El Y
      deps : El X → Matrix (X .arity) (Y .arity)
      deps-ok : ∀ x x' j → (∀ i → deps x i j → x i ≡ x' i) → func x j ≡ func x' j
  open _⇒_

  constant : ∀ {X Y} → El Y → X ⇒ Y
  constant y .func _ = y
  constant y .deps _ i j = ⊥
  constant y .deps-ok = λ x x' j z → refl

  id : ∀ X → X ⇒ X
  id X .func x = x
  id X .deps x i j = i ≡ j
  id X .deps-ok = λ x x' j z → z j refl

  _∘_ : ∀ {X Y Z} → Y ⇒ Z → X ⇒ Y → X ⇒ Z
  (f ∘ g) .func x = f .func (g .func x)
  (f ∘ g) .deps x = f .deps (g .func x) ∘M g .deps x
  (f ∘ g) .deps-ok x x' j x₁ = f .deps-ok (g .func x) (g .func x') j
                                (λ i z → g .deps-ok x x' i (λ i₁ z₁ → x₁ i₁ (i , z , z₁)))



-}



{-

El : Obj → Set
El X = (i : Fin (X .arity)) → Maybe (X .dom i)

is-just : ∀ {A : Set} → Maybe A → Set
is-just nothing = ⊥
is-just (just _) = ⊤

is-nothing : ∀ {A : Set} → Maybe A → Set
is-nothing nothing = ⊤
is-nothing (just _) = ⊥

record _⇒_ (X Y : Obj) : Set where
  field
    func : El X → El Y
    func-total : ∀ x → (∀ i → is-just (x i)) → ∀ j → is-just (func x j)
open _⇒_



_∘_ : ∀ {X Y Z} → Y ⇒ Z → X ⇒ Y → X ⇒ Z
(f ∘ g) .func x i = f .func (g .func x) i
(f ∘ g) .func-total x i = f .func-total (g .func x) (g .func-total x i)

Matrix : ℕ → ℕ → Set₁
Matrix m n = Fin m → Fin n → Set

Vec : ℕ → Set₁
Vec n = Fin n → Set

_⊔_ : ∀ {n} → Vec n → Vec n → Vec n
(x ⊔ y) i = x i ⊎ y i

∅ : ∀ {n} → Vec n
∅ i = ⊥

_∙_ : ∀ {m n} → Matrix m n → Vec m → Vec n
(M ∙ v) i = Σ[ j ∈ _ ] M j i × v j

_≈_ : ∀ {n} → Vec n → Vec n → Set
x ≈ y = ∀ i → (x i → y i) × (y i → x i)

_≈M_ : ∀ {m n} → Matrix m n → Matrix m n → Set
M ≈M N = ∀ i j → (M i j → N i j) × (N i j → M i j)

_≈S_ : Set → Set → Set
X ≈S Y = (X → Y) × (Y → X)

infix 4 _≈_ _≈M_ _≈S_

∙-preserve-∅ : ∀ {m n} (M : Matrix m n) → M ∙ ∅ ≈ ∅
∙-preserve-∅ M i .proj₁ ()
∙-preserve-∅ M i .proj₂ ()

∙-preserve-⊔ : ∀ {m n} (M : Matrix m n) (x y : Vec m) → (M ∙ x) ⊔ (M ∙ y) ≈ M ∙ (x ⊔ y)
∙-preserve-⊔ M x y i .proj₁ (inj₁ (j , Mji , xj)) = j , Mji , inj₁ xj
∙-preserve-⊔ M x y i .proj₁ (inj₂ (j , Mji , yj)) = j , Mji , inj₂ yj
∙-preserve-⊔ M x y i .proj₂ (j , Mji , inj₁ xj) = inj₁ (j , Mji , xj)
∙-preserve-⊔ M x y i .proj₂ (j , Mji , inj₂ yj) = inj₂ (j , Mji , yj)

_∘M_ : ∀ {m n o} → Matrix n o → Matrix m n → Matrix m o
(M ∘M N) i j = Σ[ k ∈ _ ] (M k j × N i k)

remove : ∀ {X : Obj} (x : El X) (i : Fin (X .arity)) → El X
remove x i i' with i ≟ i'
... | yes refl = nothing
... | no _     = x i'

jacobian : ∀ {X Y} → X ⇒ Y → El X → Matrix (X .arity) (Y .arity)
jacobian f x i j = is-nothing (f .func (remove x i) j)

-- lemma : is-nothing (f .func

chain-rule : ∀ {X Y Z} (f : X ⇒ Y) (g : Y ⇒ Z) (x : El X) →
             jacobian g (f .func x) ∘M jacobian f x ≈M jacobian (g ∘ f) x
chain-rule f g x i j .proj₁ (k , ϕ , ψ) = {!!}
chain-rule f g x i j .proj₂ x₁ = {!!} -- We don't know which element of Y is the crucial one! But maybe if the function was sequential?

-}

{-

_∘'_ : ∀ {m n o} → Matrix n o → Matrix m n → Matrix m o
(M ∘' N) i j = ∀ k → M k j ⊎ N i k

upd : ∀ {X : Obj} (x : El X) (i : Fin (X .arity)) (x'ᵢ : X .dom i) → El X
upd x i x'ᵢ i' with i ≟ i'
... | yes refl = x'ᵢ
... | no _     = x i'

postulate
  co-trans : ∀ {A : Set} {x y : A} z → (x ≡ y → ⊥) → (x ≡ z → ⊥) ⊎ (z ≡ y → ⊥)

foop : ∀ {A B : Set} → (f : A → B) → A → Set
foop f a = ∀ a' → f a ≡ f a' → a ≡ a'

non-const : ∀ {A B : Set} → (f : A → B) → A → Set
non-const f _ = Σ[ a ∈ _ ] Σ[ a' ∈ _ ] (f a ≡ f a' → ⊥)

constant : ∀ {A B : Set} → (f : A → B) → A → Set
constant f _ = ∀ a a' → f a ≡ f a'

jacobian : ∀ {X Y} → X ⇒ Y → El X → Matrix (X .arity) (Y .arity)
jacobian {X} {Y} f x i j = Σ[ x'ᵢ ∈ X .dom i ] (f x j ≡ f (upd x i x'ᵢ) j → ⊥)

-- not constant
f true  = 1
f false = 2

-- not constant
g 1 = true
g 2 = true
g 3 = false

-- but the composite is constant 'true'

-- a function is strict in component ⊥ if replacing that component with ⊥ causes the whole thing to be ⊥.
--
-- so we can talk about functions f : (Lift A)ᵐ → (Lift B)ⁿ and ask if they are strict in each argument
--
-- assuming that f(a) = ⊥ => ∃i. aᵢ = ⊥
--
-- In this way, functions intrinsically carry their dependency information.

chain-rule1 : ∀ {X Y Z} (f : X → Y) (g : Y → Z) (x : X) →
              (non-const g (f x) × non-const f x) ≈S non-const (λ x → g (f x)) x
chain-rule1 f g _ .proj₁ ((y , y' , ϕ) , (x , x' , ψ)) = x , x' , {!!}
chain-rule1 f g _ .proj₂ (x , x' , ϕ) =
  (f x , f x' , ϕ) ,
  x , x' , λ eq → ϕ (cong g eq)

chain-rule2 : ∀ {X Y Z} (f : X → Y) (g : Y → Z) (x : X) →
              (constant g (f x) × constant f x) ≈S constant (λ x → g (f x)) x
chain-rule2 f g x .proj₁ = λ z a a' → z .proj₁ (f a) (f a')
chain-rule2 f g x .proj₂ x₁ = {!!} , {!!} -- if 'f' is constant, then second one
  -- if 'f' is not constant, then there is an x' where f x ≠ f x'
  -- if 'g' is constant, then ok
  -- otherwise there is a
  -- but g might not be constant, but be constant on all of f's range


chain-rule : ∀ {X Y Z} (f : X ⇒ Y) (g : Y ⇒ Z) (x : El X) →
             jacobian g (f x) ∘ jacobian f x ≈M jacobian (λ x → g (f x)) x
chain-rule f g x i j .proj₁ (k , (y'ₖ , ϕ) , (x'ᵢ , ψ)) with co-trans (g (f (upd x i x'ᵢ)) j) ϕ
... | inj₁ χ = x'ᵢ , χ
... | inj₂ χ = {!!}
  -- g (f (upd x i x'ᵢ)) j ≠ g (upd (f x) k y'ₖ) j
  -- so f (upd x i x'ᵢ) ≠ upd (f x) k y'ₖ

  --



  -- g (f x) j ≠ g (upd (f x) k y'ₖ) j
  -- so f x ≠ upd (f x) k y'ₖ at some k'

  -- either g (f x) j ≠ g (f (upd x i x'ᵢ)) j  -- done
  --     or g (upd (f x) k y'ₖ) j ≠ g (f (upd x i x'ᵢ))
  --        do : upd (f x)

  -- and f x k ≠ f (upd x i x'ᵢ) k

chain-rule f g x i j .proj₂ (x'ᵢ , ϕ) =
   -- g (f x) j ≠ g (f (upd x i x'ᵢ)) j
   -- so f x ≠ f (upd x i x'ᵢ) at some element k
   --

  {!!} , ({!!} , {!!})


jacobian' : ∀ {X Y} → X ⇒ Y → El X → Matrix (X .arity) (Y .arity)
jacobian' {X} {Y} f x i j = ∀ x'ᵢ → f x j ≡ f (upd x i x'ᵢ) j

chain-rule' : ∀ {X Y Z} (f : X ⇒ Y) (g : Y ⇒ Z) (x : El X) →
              jacobian' g (f x) ∘' jacobian' f x ≈M jacobian' (λ x → g (f x)) x
chain-rule' f g x i j .proj₁ ϕ x'ᵢ = {!!}
chain-rule' f g x i j .proj₂ ϕ k =
  -- either
  {!!}

-}

{-
-- If f : A → B is a function, then its derivative is ⊥ if it is
-- constant, and ⊤ if not.
--
-- Extend this to n-ary functions by partial derivatives. Does this
-- work?
--
-- Interpretation. For a point (a1,...,an), the tangent space is the
-- semimodule 𝔹ⁿ. Interpret ⊤ at a position as "this changes" and ⊥ as
-- "no change".
--
-- The derivative of a function Aⁿ → A at a point (a1, ..., an) is a
-- vector in 𝔹ⁿ (linear map). If a position is ⊤ then changing this
-- input changes the output, and ⊥ otherwise. So it is ⊤ if the
-- function depends on this argument at this point.
--
-- Applying a derivative map to an input tangent tells us whether or
-- not the output will change given this change in the input.
--
-- A cotangent is a (linear) predicate on tangents. The reverse
-- derivative takes a predicate on changes in the output and tells you
-- what changes in the input would lead to that. The musical
-- isomorphisms tell you how to convert between tangents and
-- cotangents.
--
-- What is the relationship between this and Galois connections?
--
-- Or between this and other kinds of dependency analysis?

-- Let (A,eq : A → A → Ω) be a set-with-equality.
--
-- A function is one such that f : A → B satisfies eq(a,a') ≤ eq(f a, f a')
--
-- A monad M : Spc → Spc collapses all the elements by setting
-- eq(a,a') = ⊤. A function 'f' is insensitive to its argument if


-- For OR(Tr,Tr) = Tr:
--
--  ∂OR(Tr,Tr) = (⊥ ⊥)  -- changing one independently will not change the output
--
--  (⊥ ⊥) · (⊤ ⊤) = ⊥   -- both outputs change, should mean that the value changes

-- d(xy)/dx = y
-- d(xy)/dy = x

-- Derivative of xy at (0,0) is 0, because it is a stationary point. Changing one of the arguments will not affect anything.

-- Is this what we want?

-- Change means "one of these changes"

record Domain : Set₁ where
  field
    arity : ℕ
    set   : Fin arity → Set
open Domain

point : Domain → Set
point D = (i : Fin (D .arity)) → D .set i

upd : ∀ {A : Domain} (a : point A) (j : Fin (A .arity)) (aⱼ : A .set j) → point A
upd a j aⱼ i with i ≟ j
... | yes refl = aⱼ
... | no proof = a i

record Function (D : Domain) (B : Set) : Set where
  field
    *→* : ((i : Fin (D .arity)) → D .set i) → B
open Function

-- Tangent at a point is a vector of truth values
Tan : (A : Domain) → point A → Set₁
Tan A a = Fin (A .arity) → Set

-- Tangents induce a relation between points of a domain. A related
-- point differs in one place that it is allowed to.
--
-- FIXME: shouldn't it allow all changes?
related : ∀ {A : Domain} (a : point A) (δa : Tan A a) → point A → Set
related {A} a δa a' = Σ[ i ∈ Fin _ ] (δa i × Σ[ aᵢ ∈ _ ] (a' ≡ upd a i aᵢ)) -- and the point is different?

-- Partial derivatives
derivative : ∀ {A B} (f : Function A B) → point A → Fin (A .arity) → Set
derivative {A} f a i = Σ[ a' ∈ A .set i ] (f .*→* a ≡ f .*→* (upd a i a') → ⊥) -- also, a' ≠ a i?

apply : ∀ {n} → (f : Fin n → Set) (δ : Fin n → Set) → Set
apply f δ = Σ[ i ∈ _ ] (f i × δ i)



-- apply (derivative f a) δa = ⊥ means

-- for every position, either we are insenstive to it, or

-- Correctness: for f : A → B, then
--
-- given `a : A`, `δa : Tan A a`, and `a'` such that `related a δa a'`,
-- then if ∂f(a) δa ≡ ⊥ <-> f a ≡ f a'

postulate
  fext : ∀ {A : Set}{B : A → Set}(f g : (a : A) → B a) → (∀ a → f a ≡ g a) → f ≡ g

correctness : ∀ {A B} (f : Function A B) (a : point A) (δa : Tan A a)
                (a' : point A) → related a δa a' → (f .*→* a ≡ f .*→* a' → ⊥) → apply (derivative f a) δa
correctness f a δa a' (i , δaᵢ , aᵢ , refl) x₁ = i , (aᵢ , x₁) , δaᵢ

--


{-
module _ n (A : Fin n → Set) where

  Tan : ℕ → Set₁
  Tan n = Fin n → Set

  -- derivative as a vector
  derivative2 : (B : Set) (f : (∀ i → A i) → B) (a : ∀ i → A i) → Tan n
  derivative2 B f a i = ∀ aᵢ → f a ≡ f (upd a i aᵢ)
    -- if equality of the codomain is Ω-valued, then we can

  -- This extends to derivatives of m → n functions, which are
  -- matrices of truth values.

  -- application of a tangent vector to an approximation vector
  app : ∀ {n} → Tan n → (Fin n → Set) → Set
  app δ x = ∀ i → δ i ⊎ x i

  -- application always preserves meets (TODO)

  -- What is reverse application?

  derivative : (B : Set) (f : (∀ i → A i) → B) (a : ∀ i → A i) → (Fin n → Set) → Set
  derivative B f a δa = ∀ a' → (∀ i → δa i → a i ≡ a' i) → f a ≡ f a'

  monotone : ∀ B f a δa₁ δa₂ → (∀ i → δa₁ i → δa₂ i) → derivative B f a δa₁ → derivative B f a δa₂
  monotone B f a δa₁ δa₂ δa₁≤δa₂ d = λ a' z → d a' (λ i z₁ → z i (δa₁≤δa₂ i z₁))

  -- Can't preserve joins, because the derivative of the constant
  -- function doesn't map the bottom tangent to bottom
  constant-derivative : ∀ B b a δa → derivative B (λ _ → b) a δa
  constant-derivative B b a δa = λ a' z → refl

  -- projection-derivative : ∀ i a δa → derivative (A i) (λ a → a i) a δa → δa i
  -- projection-derivative i a δa d with excluded-middle (δa i)
  -- ... | inj₁ x = x
  -- ... | inj₂ y = {!d a !} -- if we had another value at (a i), then we could do it. Need to know that A i is non-trivial.

  -- top-derivative : ∀ B f a → derivative B f a (λ _ → ⊤)
  -- top-derivative B f a a' x = {!!} -- this is function extensionality



  -- preserve-meet : ∀ a δa₁ δa₂ →
  --                 derivative a δa₁ × derivative a δa₂ →
  --                 derivative a (λ i → δa₁ i × δa₂ i)
  -- preserve-meet a δa₁ δa₂ (d₁ , d₂) a' v = d₁ a' {!!}


  -- preserve-join : ∀ a δa₁ δa₂ →
  --                 derivative a δa₁ ⊎ derivative a δa₂ →
  --                 derivative a (λ i → δa₁ i ⊎ δa₂ i)
  -- preserve-join a δa₁ δa₂ (inj₁ x) a' x₁ = x a' (λ i z → x₁ i (inj₁ z))
  -- preserve-join a δa₁ δa₂ (inj₂ y) a' x₁ = y a' (λ i z → x₁ i (inj₂ z))

  -- preserve-join⁻¹ : ∀ a δa₁ δa₂ →
  --                   derivative a (λ i → δa₁ i ⊎ δa₂ i) →
  --                   derivative a δa₁ ⊎ derivative a δa₂
  -- preserve-join⁻¹ a δa₁ δa₂ f with excluded-middle (∀ i → δa₁ i → ⊥)
  -- ... | inj₁ x = inj₂ (λ a' v → f a' λ { i (inj₁ x') → ⊥-elim (x _ x') ; i (inj₂ y) → v i y })
  -- -- Case2 : there exists a δa₁ that is true
  -- ... | inj₂ y = {!!}
-}
-}
