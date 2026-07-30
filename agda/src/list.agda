{-# OPTIONS --prop --postfix-projections --safe #-}

-- Permutation, filtering and partition lemmas for lists, including lists of lists compared up to
-- reordering at both levels.
module list where

open import Data.Bool as Bool using (Bool; _∨_)
open import Data.Bool.ListAction using (any)
open import Data.Bool.Properties using (∨-assoc)
open import Data.List using (List; []; _∷_; _++_; map; concat; filterᵇ; partitionᵇ)
open import Data.List.Properties using (++-assoc)
import Data.List.Relation.Binary.Permutation.Homogeneous as H
import Data.List.Relation.Binary.Permutation.Propositional as ↭
open ↭ using (_↭_; ↭-refl; ↭-sym; ↭-trans; ↭-reflexive)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties using (++⁺; ++-comm; shift)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_)
  renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans; cong to ≡-cong; cong₂ to ≡-cong₂)

private
  ∨-swap : ∀ a b c → (a ∨ (b ∨ c)) ≡ (b ∨ (a ∨ c))
  ∨-swap Bool.false b c = ≡-refl
  ∨-swap Bool.true Bool.false c = ≡-refl
  ∨-swap Bool.true Bool.true c = ≡-refl

∨-false : ∀ x y → (x ∨ y) ≡ Bool.false → (x ≡ Bool.false) × (y ≡ Bool.false)
∨-false Bool.false y h = ≡-refl , h

++-swap : ∀ {a} {A : Set a} (xs ys zs : List A) → xs ++ (ys ++ zs) ↭ ys ++ (xs ++ zs)
++-swap xs ys zs =
  ↭-trans (↭-reflexive (≡-sym (++-assoc xs ys zs)))
          (↭-trans (++⁺ (++-comm xs ys) ↭-refl) (↭-reflexive (++-assoc ys xs zs)))

any-perm : ∀ {a} {A : Set a} (f : A → Bool) {rs rs' : List A} →
           rs ↭ rs' → any f rs ≡ any f rs'
any-perm f ↭.refl = ≡-refl
any-perm f (↭.prep r p) = ≡-cong (f r ∨_) (any-perm f p)
any-perm f (↭.swap a b p) =
  ≡-trans (≡-cong (λ z → f a ∨ (f b ∨ z)) (any-perm f p)) (∨-swap (f a) (f b) _)
any-perm f (↭.trans p q) = ≡-trans (any-perm f p) (any-perm f q)

any-cong : ∀ {a} {A : Set a} {f g : A → Bool} → (∀ x → f x ≡ g x) →
           ∀ xs → any f xs ≡ any g xs
any-cong h []       = ≡-refl
any-cong h (x ∷ xs) = ≡-cong₂ _∨_ (h x) (any-cong h xs)

any-++ : ∀ {a} {A : Set a} (f : A → Bool) (xs ys : List A) →
         any f (xs ++ ys) ≡ (any f xs ∨ any f ys)
any-++ f []       ys = ≡-refl
any-++ f (x ∷ xs) ys = ≡-trans (≡-cong (f x ∨_) (any-++ f xs ys)) (≡-sym (∨-assoc (f x) _ _))

any-concat : ∀ {a} {A : Set a} (f : A → Bool) (xss : List (List A)) →
             any f (concat xss) ≡ any (λ xs → any f xs) xss
any-concat f []         = ≡-refl
any-concat f (xs ∷ xss) =
  ≡-trans (any-++ f xs (concat xss)) (≡-cong (any f xs ∨_) (any-concat f xss))

any-filter : ∀ {a} {A : Set a} (f g : A → Bool) (xs : List A) →
             any g (filterᵇ f xs) ≡ any (λ x → f x Bool.∧ g x) xs
any-filter f g []       = ≡-refl
any-filter f g (x ∷ xs) with f x
... | Bool.true  = ≡-cong (g x ∨_) (any-filter f g xs)
... | Bool.false = any-filter f g xs

part₁-filter : ∀ {a} {A : Set a} (f : A → Bool) (xs : List A) →
               proj₁ (partitionᵇ f xs) ≡ filterᵇ f xs
part₁-filter f []       = ≡-refl
part₁-filter f (x ∷ xs) with f x
... | Bool.true  = ≡-cong (x ∷_) (part₁-filter f xs)
... | Bool.false = part₁-filter f xs

part₂-filter : ∀ {a} {A : Set a} (f : A → Bool) (xs : List A) →
               proj₂ (partitionᵇ f xs) ≡ filterᵇ (λ x → Bool.not (f x)) xs
part₂-filter f []       = ≡-refl
part₂-filter f (x ∷ xs) with f x
... | Bool.true  = part₂-filter f xs
... | Bool.false = ≡-cong (x ∷_) (part₂-filter f xs)

filter-cong : ∀ {a} {A : Set a} {f g : A → Bool} → (∀ x → f x ≡ g x) →
              ∀ xs → filterᵇ f xs ≡ filterᵇ g xs
filter-cong h [] = ≡-refl
filter-cong {f = f} {g} h (x ∷ xs) with f x | g x | h x
... | Bool.true  | _ | ≡-refl = ≡-cong (x ∷_) (filter-cong h xs)
... | Bool.false | _ | ≡-refl = filter-cong h xs

filter-filter : ∀ {a} {A : Set a} (f g : A → Bool) (xs : List A) →
                filterᵇ g (filterᵇ f xs) ≡ filterᵇ (λ x → f x Bool.∧ g x) xs
filter-filter f g []       = ≡-refl
filter-filter f g (x ∷ xs) with f x
... | Bool.false = filter-filter f g xs
... | Bool.true  with g x
...   | Bool.true  = ≡-cong (x ∷_) (filter-filter f g xs)
...   | Bool.false = filter-filter f g xs

-- Members failing f can be filtered out before filtering by g, when no member passes both.
filter-absorb : ∀ {a} {A : Set a} (f g : A → Bool) (xs : List A) →
                any (λ x → f x Bool.∧ g x) xs ≡ Bool.false →
                filterᵇ g (filterᵇ (λ x → Bool.not (f x)) xs) ≡ filterᵇ g xs
filter-absorb f g []       h = ≡-refl
filter-absorb f g (x ∷ xs) h with ∨-false (f x Bool.∧ g x) _ h
... | (hx , hrest) with f x
...   | Bool.true  rewrite hx = filter-absorb f g xs hrest
...   | Bool.false with g x
...     | Bool.true  = ≡-cong (x ∷_) (filter-absorb f g xs hrest)
...     | Bool.false = filter-absorb f g xs hrest

-- Selecting by f and then by g among the rest is selecting by their disjunction, up to order.
concat-select : ∀ {a} {A : Set a} (f g : List A → Bool) (xss : List (List A)) →
                concat (filterᵇ f xss) ++ concat (filterᵇ g (filterᵇ (λ C → Bool.not (f C)) xss))
                ↭ concat (filterᵇ (λ C → f C ∨ g C) xss)
concat-select f g []        = ↭-refl
concat-select f g (C ∷ xss) with f C
... | Bool.true  =
  ↭-trans (↭-reflexive (++-assoc C (concat (filterᵇ f xss)) _)) (++⁺ ↭-refl (concat-select f g xss))
... | Bool.false with g C
...   | Bool.true  =
  ↭-trans (++-swap (concat (filterᵇ f xss)) C _) (++⁺ ↭-refl (concat-select f g xss))
...   | Bool.false = concat-select f g xss

-- Lists of lists compared up to reordering at both levels.
_↭↭_ : ∀ {a} {A : Set a} → List (List A) → List (List A) → Set a
_↭↭_ = H.Permutation _↭_

private
  pw-refl : ∀ {a} {A : Set a} (xss : List (List A)) → Pointwise _↭_ xss xss
  pw-refl []         = []
  pw-refl (xs ∷ xss) = ↭-refl ∷ pw-refl xss

↭↭-refl : ∀ {a} {A : Set a} {xss : List (List A)} → xss ↭↭ xss
↭↭-refl = H.refl (pw-refl _)

↭↭-of-≡ : ∀ {a} {A : Set a} {xss yss : List (List A)} → xss ≡ yss → xss ↭↭ yss
↭↭-of-≡ ≡-refl = ↭↭-refl

concat-resp : ∀ {a} {A : Set a} {rss rss' : List (List A)} →
              rss ↭↭ rss' → concat rss ↭ concat rss'
concat-resp (H.refl [])       = ↭-refl
concat-resp (H.refl (r ∷ pw)) = ++⁺ r (concat-resp (H.refl pw))
concat-resp (H.prep r p)      = ++⁺ r (concat-resp p)
concat-resp (H.swap {ys = ys} {x′ = x′} {y′ = y′} r₁ r₂ p) =
  ↭-trans (++⁺ r₁ (++⁺ r₂ (concat-resp p))) (++-swap x′ y′ (concat ys))
concat-resp (H.trans p q)     = ↭-trans (concat-resp p) (concat-resp q)

partition-resp : ∀ {a r} {A : Set a} {S : A → A → Set r} (f : A → Bool) →
                 (∀ {x y} → S x y → f x ≡ f y) →
                 ∀ {rs rs'} → H.Permutation S rs rs' →
                 H.Permutation S (proj₁ (partitionᵇ f rs)) (proj₁ (partitionᵇ f rs'))
                 × H.Permutation S (proj₂ (partitionᵇ f rs)) (proj₂ (partitionᵇ f rs'))
partition-resp f resp (H.refl []) = H.refl [] , H.refl []
partition-resp f resp (H.refl (_∷_ {x} {y} s pw)) with partition-resp f resp (H.refl pw)
... | (p₁ , p₂) with f x | f y | resp s
...   | Bool.true  | _ | ≡-refl = H.prep s p₁ , p₂
...   | Bool.false | _ | ≡-refl = p₁ , H.prep s p₂
partition-resp f resp (H.prep {x = x} {y} s p) with partition-resp f resp p
... | (p₁ , p₂) with f x | f y | resp s
...   | Bool.true  | _ | ≡-refl = H.prep s p₁ , p₂
...   | Bool.false | _ | ≡-refl = p₁ , H.prep s p₂
partition-resp f resp (H.swap {x = x} {y} {x′} {y′} s₁ s₂ p) with partition-resp f resp p
... | (p₁ , p₂) with f x | f x′ | resp s₁ | f y | f y′ | resp s₂
...   | Bool.true  | _ | ≡-refl | Bool.true  | _ | ≡-refl = H.swap s₁ s₂ p₁ , p₂
...   | Bool.true  | _ | ≡-refl | Bool.false | _ | ≡-refl = H.prep s₁ p₁ , H.prep s₂ p₂
...   | Bool.false | _ | ≡-refl | Bool.true  | _ | ≡-refl = H.prep s₂ p₁ , H.prep s₁ p₂
...   | Bool.false | _ | ≡-refl | Bool.false | _ | ≡-refl = p₁ , H.swap s₁ s₂ p₂
partition-resp f resp (H.trans p q) with partition-resp f resp p | partition-resp f resp q
... | (p₁ , p₂) | (q₁ , q₂) = H.trans p₁ q₁ , H.trans p₂ q₂

map-proj₁-pair : ∀ {a b} {A : Set a} {B : Set b} (g : A → B) (xs : List A) →
                 map proj₁ (map (λ x → (x , g x)) xs) ≡ xs
map-proj₁-pair g []       = ≡-refl
map-proj₁-pair g (x ∷ xs) = ≡-cong (x ∷_) (map-proj₁-pair g xs)

-- The two halves of a partition recombine to the original, up to order.
partition-↭ : ∀ {a} {A : Set a} (f : A → Bool) (xs : List A) →
              (proj₁ (partitionᵇ f xs) ++ proj₂ (partitionᵇ f xs)) ↭ xs
partition-↭ f []       = ↭-refl
partition-↭ f (x ∷ xs) with f x
... | Bool.true  = ↭.prep x (partition-↭ f xs)
... | Bool.false =
  ↭-trans (shift x (proj₁ (partitionᵇ f xs)) (proj₂ (partitionᵇ f xs)))
          (↭.prep x (partition-↭ f xs))

↭↭-sym : ∀ {a} {A : Set a} {xss yss : List (List A)} → xss ↭↭ yss → yss ↭↭ xss
↭↭-sym = H.sym ↭-sym

↭↭-of-↭ : ∀ {a} {A : Set a} {xss yss : List (List A)} → xss ↭ yss → xss ↭↭ yss
↭↭-of-↭ ↭.refl         = ↭↭-refl
↭↭-of-↭ (↭.prep x p)   = H.prep ↭-refl (↭↭-of-↭ p)
↭↭-of-↭ (↭.swap x y p) = H.swap ↭-refl ↭-refl (↭↭-of-↭ p)
↭↭-of-↭ (↭.trans p q)  = H.trans (↭↭-of-↭ p) (↭↭-of-↭ q)
