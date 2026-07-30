{-# OPTIONS --prop --postfix-projections --safe #-}

-- Permutation and partition lemmas for lists, including lists of lists compared up to reordering
-- at both levels.
module list where

open import Data.Bool as Bool using (Bool; _∨_)
open import Data.Bool.ListAction using (any)
open import Data.Bool.Properties using (∨-assoc)
open import Data.List using (List; []; _∷_; _++_; map; concat; partitionᵇ)
open import Data.List.Properties using (++-assoc)
import Data.List.Relation.Binary.Permutation.Homogeneous as H
import Data.List.Relation.Binary.Permutation.Propositional as ↭
open ↭ using (_↭_; ↭-refl; ↭-trans; ↭-reflexive)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_; universal) renaming (map to All-map)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties using (++⁺; ++-comm; shift)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_)
  renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans; cong to ≡-cong; cong₂ to ≡-cong₂)

private
  ∨-swap : ∀ a b c → (a ∨ (b ∨ c)) ≡ (b ∨ (a ∨ c))
  ∨-swap Bool.false b c = ≡-refl
  ∨-swap Bool.true Bool.false c = ≡-refl
  ∨-swap Bool.true Bool.true c = ≡-refl

  ∨-interchange : ∀ a b c d → ((a ∨ b) ∨ (c ∨ d)) ≡ ((a ∨ c) ∨ (b ∨ d))
  ∨-interchange Bool.true  b c d = ≡-refl
  ∨-interchange Bool.false b c d = ∨-swap b c d

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

any-false : ∀ {a} {A : Set a} {f : A → Bool} {xs : List A} →
            All (λ x → f x ≡ Bool.false) xs → any f xs ≡ Bool.false
any-false []       = ≡-refl
any-false (h ∷ hs) = ≡-cong₂ _∨_ h (any-false hs)

any-or : ∀ {a} {A : Set a} (f g : A → Bool) (xs : List A) →
         any (λ x → f x ∨ g x) xs ≡ (any f xs ∨ any g xs)
any-or f g []       = ≡-refl
any-or f g (x ∷ xs) =
  ≡-trans (≡-cong ((f x ∨ g x) ∨_) (any-or f g xs)) (∨-interchange (f x) (g x) (any f xs) (any g xs))

-- Swapping the order of a doubly-nested search.
any-comm : ∀ {a b} {A : Set a} {B : Set b} (h : A → B → Bool) (xs : List A) (ys : List B) →
           any (λ x → any (h x) ys) xs ≡ any (λ y → any (λ x → h x y) xs) ys
any-comm h []       ys = ≡-sym (any-false (universal (λ y → ≡-refl) ys))
any-comm h (x ∷ xs) ys =
  ≡-trans (≡-cong (any (h x) ys ∨_) (any-comm h xs ys))
          (≡-sym (any-or (h x) (λ y → any (λ x' → h x' y) xs) ys))

any-++ : ∀ {a} {A : Set a} (f : A → Bool) (xs ys : List A) →
         any f (xs ++ ys) ≡ (any f xs ∨ any f ys)
any-++ f []       ys = ≡-refl
any-++ f (x ∷ xs) ys = ≡-trans (≡-cong (f x ∨_) (any-++ f xs ys)) (≡-sym (∨-assoc (f x) _ _))

any-concat : ∀ {a} {A : Set a} (f : A → Bool) (xss : List (List A)) →
             any f (concat xss) ≡ any (λ xs → any f xs) xss
any-concat f []         = ≡-refl
any-concat f (xs ∷ xss) =
  ≡-trans (any-++ f xs (concat xss)) (≡-cong (any f xs ∨_) (any-concat f xss))

-- Lists of lists compared up to reordering at both levels.
_↭↭_ : ∀ {a} {A : Set a} → List (List A) → List (List A) → Set a
_↭↭_ = H.Permutation _↭_

private
  pw-refl : ∀ {a} {A : Set a} (xss : List (List A)) → Pointwise _↭_ xss xss
  pw-refl []         = []
  pw-refl (xs ∷ xss) = ↭-refl ∷ pw-refl xss

↭↭-refl : ∀ {a} {A : Set a} {xss : List (List A)} → xss ↭↭ xss
↭↭-refl = H.refl (pw-refl _)

↭↭-of-↭ : ∀ {a} {A : Set a} {xss yss : List (List A)} → xss ↭ yss → xss ↭↭ yss
↭↭-of-↭ ↭.refl         = ↭↭-refl
↭↭-of-↭ (↭.prep x p)   = H.prep ↭-refl (↭↭-of-↭ p)
↭↭-of-↭ (↭.swap x y p) = H.swap ↭-refl ↭-refl (↭↭-of-↭ p)
↭↭-of-↭ (↭.trans p q)  = H.trans (↭↭-of-↭ p) (↭↭-of-↭ q)

concat-resp : ∀ {a} {A : Set a} {rss rss' : List (List A)} →
              rss ↭↭ rss' → concat rss ↭ concat rss'
concat-resp (H.refl [])       = ↭-refl
concat-resp (H.refl (r ∷ pw)) = ++⁺ r (concat-resp (H.refl pw))
concat-resp (H.prep r p)      = ++⁺ r (concat-resp p)
concat-resp (H.swap {ys = ys} {x′ = x′} {y′ = y′} r₁ r₂ p) =
  ↭-trans (++⁺ r₁ (++⁺ r₂ (concat-resp p))) (++-swap x′ y′ (concat ys))
concat-resp (H.trans p q)     = ↭-trans (concat-resp p) (concat-resp q)

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

partition-All : ∀ {a p} {A : Set a} {P : A → Set p} (f : A → Bool) {xs : List A} → All P xs →
                All P (proj₁ (partitionᵇ f xs)) × All P (proj₂ (partitionᵇ f xs))
partition-All f [] = [] , []
partition-All f (_∷_ {x} px pxs) with partition-All f pxs
... | (a₁ , a₂) with f x
...   | Bool.true  = px ∷ a₁ , a₂
...   | Bool.false = a₁ , px ∷ a₂

part₂-false : ∀ {a} {A : Set a} (f : A → Bool) (xs : List A) →
              All (λ x → f x ≡ Bool.false) (proj₂ (partitionᵇ f xs))
part₂-false f []       = []
part₂-false f (x ∷ xs) with f x in eq
... | Bool.true  = part₂-false f xs
... | Bool.false = eq ∷ part₂-false f xs

All-zip : ∀ {a p q r} {A : Set a} {P : A → Set p} {Q : A → Set q} {R : A → Set r} →
          (∀ {x} → P x → Q x → R x) → ∀ {xs : List A} → All P xs → All Q xs → All R xs
All-zip h []       []       = []
All-zip h (p ∷ ps) (q ∷ qs) = h p q ∷ All-zip h ps qs

-- Partitioning preserves pairwise relatedness, and every kept member relates to every dropped one.
partition-AllPairs : ∀ {a r} {A : Set a} {S : A → A → Set r} (f : A → Bool) →
                     (∀ {x y} → S x y → S y x) →
                     ∀ {xs : List A} → AllPairs S xs →
                     AllPairs S (proj₁ (partitionᵇ f xs))
                     × AllPairs S (proj₂ (partitionᵇ f xs))
                     × All (λ y → All (λ x → S x y) (proj₁ (partitionᵇ f xs)))
                           (proj₂ (partitionᵇ f xs))
partition-AllPairs f sym [] = [] , [] , []
partition-AllPairs f sym (_∷_ {x} px ps) with partition-AllPairs f sym ps | partition-All f px
... | (a₁ , a₂ , cross) | (px₁ , px₂) with f x
...   | Bool.true  = px₁ ∷ a₁ , a₂ , All-zip (λ s c → s ∷ c) px₂ cross
...   | Bool.false = a₁ , px₂ ∷ a₂ , All-map (λ s → sym s) px₁ ∷ cross

map-partition₁ : ∀ {a b} {A : Set a} {B : Set b} (h : A → B) (f : B → Bool) (xs : List A) →
                 proj₁ (partitionᵇ f (map h xs)) ≡ map h (proj₁ (partitionᵇ (λ x → f (h x)) xs))
map-partition₁ h f []       = ≡-refl
map-partition₁ h f (x ∷ xs) with f (h x)
... | Bool.true  = ≡-cong (h x ∷_) (map-partition₁ h f xs)
... | Bool.false = map-partition₁ h f xs

map-partition₂ : ∀ {a b} {A : Set a} {B : Set b} (h : A → B) (f : B → Bool) (xs : List A) →
                 proj₂ (partitionᵇ f (map h xs)) ≡ map h (proj₂ (partitionᵇ (λ x → f (h x)) xs))
map-partition₂ h f []       = ≡-refl
map-partition₂ h f (x ∷ xs) with f (h x)
... | Bool.true  = map-partition₂ h f xs
... | Bool.false = ≡-cong (h x ∷_) (map-partition₂ h f xs)
