{-# OPTIONS --postfix-projections --safe --prop #-}

open import Level using (_⊔_) renaming (suc to lsuc)
open import Data.Nat using (ℕ; zero; suc) renaming (_+_ to _+ℕ_)
open import Data.Fin using (Fin; zero; suc; _≟_; splitAt; _↑ˡ_; _↑ʳ_)
open import Data.Fin.Properties using (splitAt-↑ˡ; splitAt-↑ʳ)
open import Data.Product using (_×_; proj₁; proj₂; _,_; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]; map₁)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; subst; sym)

open import prop using (proj₁; proj₂)
open import prop-setoid using (Setoid)
open import basics using (IsPreorder; IsMeet; IsTop; module ≤-Reasoning; IsMonoid; monoidOfMeet)
open import commutative-monoid using (CommutativeMonoid)
open import commutative-semiring using (CommutativeSemiring)
open import matrix using (module Mat)

-- A model of dependent sensitivity analysis. Normal sensitivity
-- analysis has a fixed sensitivity on the input, but here we can vary
-- the sensitivity based on the value of the input.

module sensitivity
  {o₁ e₁ o₂ e₂}
  -- R is a partial order with a commutative monoid
  {R : Set o₁} {_≤_ : R → R → Prop e₁} (R-preorder : IsPreorder _≤_)
  {_⊗_ : R → R → R} {I : R} (⊗-I-isMonoid : IsMonoid R-preorder _⊗_ I)
  (comm : ∀ {x y} → (x ⊗ y) ≤ (y ⊗ x))
  -- S is a semiring of dependency coefficients
  {S : Setoid o₂ e₂} (S-semiring : CommutativeSemiring S)
  (let module S = Setoid S)
  (let module R  = IsPreorder R-preorder)
  (let module Ss = CommutativeSemiring S-semiring)

  (_▷_ : S .Setoid.Carrier → R → R)
  (▷-mono : ∀ {s₁ s₂ r₁ r₂} → s₁ S.≈ s₂ → r₁ ≤ r₂ → (s₁ ▷ r₁) ≤ (s₂ ▷ r₂))
  (▷-1 : ∀ {r} → (Ss.ι ▷ r) ≤ r)
  (▷-· : ∀ {x y r} → ((x Ss.· y) ▷ r) ≤ (x ▷ (y ▷ r)))
  (ε-▷ : ∀ {r} → (Ss.ε ▷ r) ≤ I)
  (+-▷ : ∀ {x y r} → ((x Ss.+ y) ▷ r) ≤ ((x ▷ r) ⊗ (y ▷ r)))
  (▷-⊤ : ∀ {x} → I ≤ (x ▷ I))
  (▷-∧ : ∀ {x r s} → ((x ▷ r) ⊗ (x ▷ s)) ≤ (x ▷ (r ⊗ s)))
  where

-- Examples:
-- 1. R = S = 𝔹, with x ▷ y = x → y
-- 2. Same but with R replaced by Prop
-- 3. Same but with both replaced by Prop
-- 4. R = (ℚ≥0,≥,+) and S =          -- for sensitivity with distances
-- 5. R = (ℚ≥0,≤,min) and S =        -- for something else
-- 6. R = (P(Col),⊆,∩) and S = (Pfin(Col)) and

private
  module RM = IsMonoid ⊗-I-isMonoid

open Mat S-semiring renaming (_∘_ to _∘M_; I to Id) using (Σ; Matrix)

record Obj : Set (lsuc o₁) where
  field
    arity : ℕ
    dom   : Fin arity → Set
    rel   : ∀ i → dom i → dom i → R -- does this need to act like an equivalence relation?
open Obj

El : Obj → Set
El X = ∀ i → X .dom i

⨂ : ∀ {n} (f : Fin n → R) → R
⨂ {zero} f = I
⨂ {suc n} f = (f zero) ⊗ (⨂ (λ i → f (suc i)))

▷-⨂ : ∀ {n} {f : Fin n → R} {x} → ⨂ (λ i → x ▷ f i) ≤ (x ▷ ⨂ f)
▷-⨂ {zero} {f} = ▷-⊤
▷-⨂ {suc n} {f} = R.trans (RM.mono R.refl (▷-⨂ {n} {f = λ i → f (suc i)})) ▷-∧

⨂-mono : ∀ {n} {f g : Fin n → R} → (∀ i → f i ≤ g i) → ⨂ f ≤ ⨂ g
⨂-mono {zero} {f} {g} fi≤gi = R.refl
⨂-mono {suc n} {f} {g} fi≤gi = RM.mono (fi≤gi zero) (⨂-mono (λ i → fi≤gi (suc i)))

Σ-▷ : ∀ {n} (f : Fin n → S.Carrier) r → (Σ f ▷ r) ≤ ⨂ (λ i → f i ▷ r)
Σ-▷ {zero} f r = ε-▷
Σ-▷ {suc n} f r = R.trans +-▷ (RM.mono R.refl (Σ-▷ (λ i → f (suc i)) r))

⨂-⊗ : ∀ {n} (f g : Fin n → R) → ⨂ (λ i → f i ⊗ g i) ≤ (⨂ f ⊗ ⨂ g)
⨂-⊗ {zero} f g = RM.lunit .proj₂
⨂-⊗ {suc n} f g = begin
    (f zero ⊗ g zero) ⊗ ⨂ (λ i → f (suc i) ⊗ g (suc i))
  ≤⟨ RM.mono R.refl (⨂-⊗ (λ i → f (suc i)) (λ i → g (suc i))) ⟩
    (f zero ⊗ g zero) ⊗ ((⨂ (λ i → f (suc i))) ⊗ (⨂ (λ i → g (suc i))))
  ≤⟨ RM.interchange comm .proj₁ ⟩
    (f zero ⊗ ⨂ (λ i → f (suc i))) ⊗ (g zero ⊗ ⨂ (λ i → g (suc i)))
  ∎
  where open ≤-Reasoning R-preorder

⨂-I : ∀ {n} → ⨂ {n} (λ i → I) ≤ I
⨂-I {zero} = R.refl
⨂-I {suc n} = R.trans (RM.lunit .proj₁) (⨂-I {n})

⨂-swap : ∀ {m n} (f : Fin m → Fin n → R) → ⨂ (λ i → ⨂ (λ j → f i j)) ≤ ⨂ (λ j → ⨂ (λ i → f i j))
⨂-swap {m} {zero} f = ⨂-I {m}
⨂-swap {m} {suc n} f = begin
    ⨂ (λ i → f i zero ⊗ ⨂ (λ j → f i (suc j)))             ≤⟨ ⨂-⊗ (λ i → f i zero) (λ i → ⨂ (λ i₁ → f i (suc i₁))) ⟩
    ⨂ (λ i → f i zero) ⊗ ⨂ (λ i → ⨂ (λ j → f i (suc j)))  ≤⟨ RM.mono R.refl (⨂-swap (λ i j → f i (suc j))) ⟩
    ⨂ (λ i → f i zero) ⊗ ⨂ (λ j → ⨂ (λ i → f i (suc j)))  ∎
  where open ≤-Reasoning R-preorder

record _⇒_ (X Y : Obj) : Set (o₁ ⊔ e₁ ⊔ o₂) where
  field
    func : El X → El Y
    deps : El X → Matrix (X .arity) (Y .arity)
    -- FIXME: deps probably needs to be a congruence with respect to
    -- an underlying equality on X
    deps-ok : ∀ x x' j → ⨂ (λ i → deps x i j ▷ X .rel i (x i) (x' i)) ≤ Y .rel j (func x j) (func x' j)
open _⇒_

-- In the case of unary functions, this is (f .dep x ▷ (x ≈ x')) ≤ f x ≈ f x'
--
-- How sensitive are you at 'x'?
--
-- For boolean sensitivity, this is essentially the same as ⊥ = constant, ⊤ = non-constant
--
-- For metric sensitivity, this is like non-uniform Lipschitz
-- continuity (is that a thing?). Though in the unary case, we don't
-- need to use addition, which means that the elements of S can just
-- be functions with composition.
--
-- And we can vary according to the output component we are
-- extracting. Compared to a graded comonad, this means that we don't
-- need to specify in advance which input is more important.

project-from-Id : ∀ {n} {f : Fin n → R} (j : Fin n) → ⨂ (λ i → Id i j ▷ f i) ≤ f j
project-from-Id {suc n} {f} zero = begin
    (Ss.ι ▷ f zero) ⊗ ⨂ (λ i → Ss.ε ▷ f (suc i)) ≤⟨ RM.mono ▷-1 (⨂-mono (λ i → ε-▷ {f (suc i)})) ⟩
    f zero ⊗ ⨂ {n} (λ i → I)                     ≤⟨ RM.mono R.refl (⨂-I {n}) ⟩
    f zero ⊗ I                                    ≤⟨ RM.runit .proj₁ ⟩
    f zero                                        ∎
  where open ≤-Reasoning R-preorder
project-from-Id {suc n} {f} (suc j) = begin
    (Ss.ε ▷ f zero) ⊗ ⨂ (λ i → Id i j ▷ f (suc i))  ≤⟨ RM.mono ε-▷ (project-from-Id {f = λ i → f (suc i)} j) ⟩
    I ⊗ f (suc j)                                    ≤⟨ RM.lunit .proj₁ ⟩
    f (suc j)                                        ∎
  where open ≤-Reasoning R-preorder

id : ∀ X → X ⇒ X
id X .func x = x
id X .deps x = Id
id X .deps-ok x x' j = begin
     ⨂ (λ i → Id i j ▷ X .rel i (x i) (x' i))    ≤⟨ project-from-Id j ⟩
     X .rel j (x j) (x' j)                        ∎
  where open ≤-Reasoning R-preorder

_∘_ : ∀ {X Y Z} → Y ⇒ Z → X ⇒ Y → X ⇒ Z
(f ∘ g) .func x = f .func (g .func x)
(f ∘ g) .deps x = (g .deps x) ∘M f .deps (g .func x)
_∘_ {X} {Y} {Z} f g .deps-ok x x' k = begin
    ⨂ (λ i → (Σ (λ j → g .deps x i j Ss.· f .deps (g .func x) j k)) ▷ X .rel i (x i) (x' i))
  ≤⟨ ⨂-mono (λ i → Σ-▷ (λ j → g .deps x i j Ss.· f .deps (g .func x) j k) (X .rel i (x i) (x' i))) ⟩
    ⨂ (λ i → ⨂ (λ j → (g .deps x i j Ss.· f .deps (g .func x) j k) ▷ X .rel i (x i) (x' i)))
  ≤⟨ ⨂-mono (λ i → ⨂-mono (λ j → ▷-mono (Ss.·-comm {g .deps x i j} {f .deps (g .func x) j k}) R.refl)) ⟩
    ⨂ (λ i → ⨂ (λ j → (f .deps (g .func x) j k Ss.· g .deps x i j) ▷ X .rel i (x i) (x' i)))
  ≤⟨ ⨂-mono (λ i → ⨂-mono (λ j → ▷-· {f .deps (g .func x) j k} {g .deps x i j} {X .rel i (x i) (x' i)}))  ⟩
    ⨂ (λ i → ⨂ (λ j → f .deps (g .func x) j k ▷ (g .deps x i j ▷ X .rel i (x i) (x' i))))
  ≤⟨ ⨂-swap (λ i j → f .deps (g .func x) j k ▷ (g .deps x i j ▷ X .rel i (x i) (x' i))) ⟩
    ⨂ (λ j → ⨂ (λ i → f .deps (g .func x) j k ▷ (g .deps x i j ▷ X .rel i (x i) (x' i))))
  ≤⟨ ⨂-mono (λ j → ▷-⨂ {f = λ i → g .deps x i j ▷ X .rel i (x i) (x' i)} {x = f .deps (g .func x) j k}) ⟩
    ⨂ (λ j → f .deps (g .func x) j k ▷ ⨂ (λ i → g .deps x i j ▷ X .rel i (x i) (x' i)))
  ≤⟨ ⨂-mono (λ j → ▷-mono (S.refl {f .deps (g .func x) j k}) (g .deps-ok x x' j)) ⟩
    ⨂ (λ j → f .deps (g .func x) j k ▷ Y .rel j (g .func x j) (g .func x' j))
  ≤⟨ f .deps-ok (g .func x) (g .func x') k ⟩
    Z .rel k (f .func (g .func x) k) (f .func (g .func x') k)
  ∎
  where open ≤-Reasoning R-preorder

------------------------------------------------------------------------------
-- Finite products

-- terminal object
terminal : Obj
terminal .arity = 0

to-terminal : ∀ {X} → X ⇒ terminal
to-terminal {X} .func x ()
to-terminal {X} .deps x _ ()
to-terminal {X} .deps-ok x x' ()


-- Specialised version of Data.Sum.[_,_] to cut down on the
-- metavariable problems.
S[_,_] : ∀ {a b c} {A : Set a} {B : Set b} → (A → Set c) → (B → Set c) → A ⊎ B → Set c
S[ X , Y ] (inj₁ a) = X a
S[ X , Y ] (inj₂ b) = Y b

binary-[] : ∀ {a b c d} {A : Set a} {B : Set b} {X₁ X₂ : A → Set c} {Y₁ Y₂ : B → Set c} {Z : Set d}
            (f : ∀ a → X₁ a → X₂ a → Z)
            (g : ∀ b → Y₁ b → Y₂ b → Z) →
            ∀ d → S[ X₁ , Y₁ ] d → S[ X₂ , Y₂ ] d → Z
binary-[] f g (inj₁ a) x y = f a x y
binary-[] f g (inj₂ b) x y = g b x y

prod : Obj → Obj → Obj
prod X Y .arity = X .arity +ℕ Y .arity
prod X Y .dom i = S[ X .dom , Y .dom ] (splitAt (X .arity) i)
prod X Y .rel i = binary-[] (X .rel) (Y .rel) (splitAt (X .arity) i)

[]-project₁ : ∀ {c} {A B : Set} {X : A → Set c} {Y : B → Set c} →
               ∀ {d} {i} → d ≡ inj₁ i → S[ X , Y ] d → X i
[]-project₁ refl x = x

lemma₁ : ∀ {c d} {A : Set} {B : Set} {X₁ X₂ : A → Set c} {Y₁ Y₂ : B → Set c} {Z : Set d}
            (f : ∀ a → X₁ a → X₂ a → Z)
            (g : ∀ b → Y₁ b → Y₂ b → Z)
            (d : A ⊎ B) (x₁ : S[ X₁ , Y₁ ] d) (x₂ : S[ X₂ , Y₂ ] d)
            (a : A) (e : d ≡ inj₁ a) →
        binary-[] f g d x₁ x₂ ≡ f a ([]-project₁ e x₁) ([]-project₁ e x₂)
lemma₁ f g d a x₁ x₂ refl = refl

[]-project₂ : ∀ {c} {A B : Set} {X : A → Set c} {Y : B → Set c} →
               ∀ {d} {i} → d ≡ inj₂ i → S[ X , Y ] d → Y i
[]-project₂ refl y = y

lemma₂ : ∀ {c d} {A : Set} {B : Set} {X₁ X₂ : A → Set c} {Y₁ Y₂ : B → Set c} {Z : Set d}
            (f : ∀ a → X₁ a → X₂ a → Z)
            (g : ∀ b → Y₁ b → Y₂ b → Z)
            (d : A ⊎ B) (x₁ : S[ X₁ , Y₁ ] d) (x₂ : S[ X₂ , Y₂ ] d)
            (b : B) (e : d ≡ inj₂ b) →
        binary-[] f g d x₁ x₂ ≡ g b ([]-project₂ e x₁) ([]-project₂ e x₂)
lemma₂ f g d a x₁ x₂ refl = refl

[]-map₁ : ∀ {c} {A A' : Set} {B : Set} {C : Set c} →
          {l : A → C} {r : B → C} {d : A' ⊎ B} {f : A' → A} →
          [_,_] {C = λ _ → C} l r (map₁ f d) ≡ [ (λ i → l (f i)) , r ] d
[]-map₁ {d = inj₁ x} = refl
[]-map₁ {d = inj₂ y} = refl

[]-pair : ∀ {A B : Set} {X : A → Set} {Y : B → Set} →
            (f : ∀ a → X a) →
            (g : ∀ b → Y b) →
            (d : A ⊎ B) → S[ X , Y ] d
[]-pair f g (inj₁ x) = f x
[]-pair f g (inj₂ y) = g y

Sreflexive : ∀ {x y} → x ≡ y → x S.≈ y
Sreflexive refl = S.refl

Rreflexive : ∀ {x y} → x ≡ y → x ≤ y
Rreflexive refl = R.refl

[]-split : ∀ {m n} (l : Fin m → S.Carrier) (r : Fin n → S.Carrier) (f : Fin (m +ℕ n) → R) →
           ⨂ (λ i → [ l , r ] (splitAt m i) ▷ f i) ≤ (⨂ (λ i → l i ▷ f (i ↑ˡ n)) ⊗ ⨂ (λ i → r i ▷ f (m ↑ʳ i)))
[]-split {zero}  {n} l r f = RM.lunit .proj₂
[]-split {suc m} {n} l r f = begin
    (l zero ▷ f zero) ⊗ ⨂ (λ i → [ l , r ] (map₁ suc (splitAt m i)) ▷ f (suc i))
  ≤⟨ RM.mono R.refl (⨂-mono {f = λ i → [ l , r ] (map₁ suc (splitAt m i)) ▷ f (suc i)} {g = λ i → [ (λ i → l (suc i)) , r ] (splitAt m i) ▷ f (suc i)}
                          λ i → ▷-mono (Sreflexive ([]-map₁ {A = Fin (suc m)} {A' = Fin m} {B = Fin n} {_} {l} {r} {splitAt m i})) R.refl) ⟩
    (l zero ▷ f zero) ⊗ (⨂ (λ i → [ (λ i → l (suc i)) , r ] (splitAt m i) ▷ f (suc i)))
  ≤⟨ RM.mono R.refl ([]-split (λ i → l (suc i)) r (λ i → f (suc i))) ⟩
    (l zero ▷ f zero) ⊗ (⨂ (λ i → l (suc i) ▷ f (suc (i ↑ˡ n))) ⊗ ⨂ (λ i → r i ▷ f (suc (m ↑ʳ i))))
  ≤⟨ RM.assoc .proj₂ ⟩
    ((l zero ▷ f zero) ⊗ ⨂ (λ i → l (suc i) ▷ f (suc (i ↑ˡ n)))) ⊗ ⨂ (λ i → r i ▷ f (suc (m ↑ʳ i)))
  ∎
  where open ≤-Reasoning R-preorder

project₁ : ∀ {X Y} → prod X Y ⇒ X
project₁ {X} {Y} .func x i = []-project₁ (splitAt-↑ˡ (X .arity) i (Y .arity)) (x (i ↑ˡ Y .arity))
project₁ {X} {Y} .deps x i j = [ (λ i → Id i j) , (λ _ → Ss.ε) ] (splitAt (X .arity) i)
project₁ {X} {Y} .deps-ok x x' j  = begin
    ⨂ (λ i → [ (λ i₁ → Id i₁ j) , (λ _ → Ss.ε) ] (splitAt (X .arity) i) ▷ binary-[] (X .rel) (Y .rel) (splitAt (X .arity) i) (x i) (x' i))
  ≤⟨ []-split (λ i → Id i j) (λ i → Ss.ε) (λ i → binary-[] (X .rel) (Y .rel) (splitAt (X .arity) i) (x i) (x' i)) ⟩
      ⨂ (λ i → Id i j ▷ binary-[] (X .rel) (Y .rel) (splitAt (X .arity) (i ↑ˡ Y .arity)) (x (i ↑ˡ Y .arity)) (x' (i ↑ˡ Y .arity)))
    ⊗ ⨂ (λ i → Ss.ε ▷ binary-[] (X .rel) (Y .rel) (splitAt (X .arity) (X .arity ↑ʳ i)) (x (X .arity ↑ʳ i)) (x' (X .arity ↑ʳ i)))
  ≤⟨ RM.mono (⨂-mono {X .arity} (λ i → ▷-mono S.refl (Rreflexive (lemma₁ (X .rel) (Y .rel) (splitAt (X .arity) (i ↑ˡ Y .arity)) (x (i ↑ˡ Y .arity)) (x' (i ↑ˡ Y .arity)) i (splitAt-↑ˡ (X .arity) i (Y .arity))))))
             (⨂-mono {Y .arity} (λ i → ε-▷)) ⟩
      ⨂ (λ i → Id i j ▷ X .rel i ([]-project₁ (splitAt-↑ˡ (X .arity) i (Y .arity)) (x (i ↑ˡ Y .arity)))
                                  ([]-project₁ (splitAt-↑ˡ (X .arity) i (Y .arity)) (x' (i ↑ˡ Y .arity))))
    ⊗ ⨂ {Y .arity} (λ i → I)
  ≤⟨ RM.mono (project-from-Id j) R.refl ⟩
      X .rel j ([]-project₁ (splitAt-↑ˡ (X .arity) j (Y .arity)) (x (j ↑ˡ Y .arity))) ([]-project₁ (splitAt-↑ˡ (X .arity) j (Y .arity)) (x' (j ↑ˡ Y .arity)))
    ⊗ ⨂ {Y .arity} (λ i → I)
  ≤⟨ RM.mono R.refl (⨂-I {Y .arity})⟩
      X .rel j ([]-project₁ (splitAt-↑ˡ (X .arity) j (Y .arity)) (x (j ↑ˡ Y .arity))) ([]-project₁ (splitAt-↑ˡ (X .arity) j (Y .arity)) (x' (j ↑ˡ Y .arity)))
    ⊗ I
  ≤⟨ RM.runit .proj₁ ⟩
    X .rel j ([]-project₁ (splitAt-↑ˡ (X .arity) j (Y .arity)) (x (j ↑ˡ Y .arity))) ([]-project₁ (splitAt-↑ˡ (X .arity) j (Y .arity)) (x' (j ↑ˡ Y .arity)))
  ∎
  where open ≤-Reasoning R-preorder

project₂ : ∀ {X Y} → prod X Y ⇒ Y
project₂ {X} {Y} .func x i = []-project₂ (splitAt-↑ʳ (X .arity) (Y .arity) i) (x (X .arity ↑ʳ i))
project₂ {X} {Y} .deps x i j = [ (λ i → Ss.ε) , (λ i → Id i j) ] (splitAt (X .arity) i)
project₂ {X} {Y} .deps-ok x x' j  = begin
    ⨂ (λ i → [ (λ i₁ → Ss.ε) , (λ i₁ → Id i₁ j) ] (splitAt (X .arity) i) ▷ binary-[] (X .rel) (Y .rel) (splitAt (X .arity) i) (x i) (x' i))
  ≤⟨ []-split (λ i → Ss.ε) (λ i → Id i j) (λ i → binary-[] (X .rel) (Y .rel) (splitAt (X .arity) i) (x i) (x' i)) ⟩
      ⨂ (λ i → Ss.ε ▷ binary-[] (X .rel) (Y .rel) (splitAt (X .arity) (i ↑ˡ Y .arity)) (x (i ↑ˡ Y .arity)) (x' (i ↑ˡ Y .arity)))
    ⊗ ⨂ (λ i → Id i j ▷ binary-[] (X .rel) (Y .rel) (splitAt (X .arity) (X .arity ↑ʳ i)) (x (X .arity ↑ʳ i)) (x' (X .arity ↑ʳ i)))
  ≤⟨ RM.mono (⨂-mono {X .arity} λ i → ε-▷) R.refl ⟩
      ⨂ {X .arity} (λ i → I)
    ⊗ ⨂ (λ i → Id i j ▷ binary-[] (X .rel) (Y .rel) (splitAt (X .arity) (X .arity ↑ʳ i)) (x (X .arity ↑ʳ i)) (x' (X .arity ↑ʳ i)))
  ≤⟨ RM.mono (⨂-I {X .arity}) R.refl ⟩
      I
    ⊗ ⨂ (λ i → Id i j ▷ binary-[] (X .rel) (Y .rel) (splitAt (X .arity) (X .arity ↑ʳ i)) (x (X .arity ↑ʳ i)) (x' (X .arity ↑ʳ i)))
  ≤⟨ RM.lunit .proj₁ ⟩
      ⨂ (λ i → Id i j ▷ binary-[] (X .rel) (Y .rel) (splitAt (X .arity) (X .arity ↑ʳ i)) (x (X .arity ↑ʳ i)) (x' (X .arity ↑ʳ i)))
  ≤⟨ project-from-Id j ⟩
      binary-[] (X .rel) (Y .rel) (splitAt (X .arity) (X .arity ↑ʳ j)) (x (X .arity ↑ʳ j)) (x' (X .arity ↑ʳ j))
  ≤⟨ Rreflexive (lemma₂ (X .rel) (Y .rel) (splitAt (X .arity) (X .arity ↑ʳ j)) (x (X .arity ↑ʳ j)) (x' (X .arity ↑ʳ j)) j (splitAt-↑ʳ (X .arity) (Y .arity) j)) ⟩
    Y .rel j ([]-project₂ (splitAt-↑ʳ (X .arity) (Y .arity) j) (x (X .arity ↑ʳ j))) ([]-project₂ (splitAt-↑ʳ (X .arity) (Y .arity) j) (x' (X .arity ↑ʳ j)))
  ∎
  where open ≤-Reasoning R-preorder

pair : ∀ {W X Y} → W ⇒ X → W ⇒ Y → W ⇒ prod X Y
pair {W} {X} {Y} f g .func w i = []-pair (f .func w) (g .func w) (splitAt (X .arity) i)
pair {W} {X} {Y} f g .deps w i j = [ (f .deps w i) , (g .deps w i) ] (splitAt (X .arity) j)
pair {W} {X} {Y} f g .deps-ok x x' j with splitAt (X .arity) j
... | inj₁ j₁ = f .deps-ok x x' j₁
... | inj₂ j₂ = g .deps-ok x x' j₂

------------------------------------------------------------------------------
-- If-then-else? Which gives a non-trivial dependent sensitivity

------------------------------------------------------------------------------
-- Multiplication from the semiring; would expect the derivatives to
-- follow Leibniz, but maybe they don't?

-- mult :
