{-# OPTIONS --prop --postfix-projections --safe #-}

-- Permutation and partition lemmas for lists, including lists of lists compared up to reordering
-- at both levels.
module list where

open import Data.Bool using (Bool; true; false; not)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_; length; map; concat; filter; filterᵇ; partition)
open import Data.Nat.ListAction using (sum)
open import Data.List.Properties using (++-assoc; length-++; filter-all; filter-accept; filter-reject;
                                        partition-defn)
import Data.List.Properties as ListP
import Data.List.Relation.Binary.Permutation.Homogeneous as H
import Data.List.Relation.Binary.Permutation.Propositional as ↭
open ↭ using (_↭_; ↭-refl; ↭-sym; ↭-trans; ↭-reflexive)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_; Pointwise-length)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_; universal)
  renaming (map to All-map)
import Data.List.Relation.Unary.All.Properties as AllP
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
open import Data.List.Relation.Unary.Any using (Any; any?; here; there; tail)
import Data.List.Relation.Unary.Any.Properties as AnyP
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties
  using (++⁺; ++-comm; shift; All-resp-↭)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (suc-injective; n≤0⇒n≡0; +-cancelʳ-≤; +-mono-≤; ≤-reflexive; ≤-trans)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (Dec; does; ¬?; yes; no; dec-false)
open import Relation.Unary.Properties using (∁?)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; subst; subst₂)
  renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans; cong to ≡-cong; cong₂ to ≡-cong₂)

++-swap : ∀ {a} {A : Set a} (xs ys zs : List A) → xs ++ (ys ++ zs) ↭ ys ++ (xs ++ zs)
++-swap xs ys zs =
  ↭-trans (↭-reflexive (≡-sym (++-assoc xs ys zs)))
          (↭-trans (++⁺ (++-comm xs ys) ↭-refl) (↭-reflexive (++-assoc ys xs zs)))

Any-All : ∀ {a p q} {A : Set a} {P : A → Set p} {Q : A → Set q} {xs : List A} →
          Any P xs → All Q xs → Any (λ x → P x × Q x) xs
Any-All (here px) (qx ∷ _) = here (px , qx)
Any-All (there a) (_ ∷ qs) = there (Any-All a qs)

Any-filter⁺ : ∀ {a p q} {A : Set a} {P : A → Set p} {Q : A → Set q}
              (P? : (x : A) → Dec (P x)) {xs : List A} →
              Any (λ x → P x × Q x) xs → Any Q (filter P? xs)
Any-filter⁺ P? {x ∷ xs} (here (px , qx)) with P? x
... | yes _   = here qx
... | no  ¬px = ⊥-elim (¬px px)
Any-filter⁺ P? {x ∷ xs} (there m) with P? x
... | yes _ = there (Any-filter⁺ P? m)
... | no  _ = Any-filter⁺ P? m

Any-filter⁻ : ∀ {a p q} {A : Set a} {P : A → Set p} {Q : A → Set q}
              (P? : (x : A) → Dec (P x)) (xs : List A) →
              Any Q (filter P? xs) → Any (λ x → Q x × P x) xs
Any-filter⁻ P? xs m = AnyP.filter⁻ P? (Any-All m (AllP.all-filter P? xs))

-- Splitting a list by a Boolean predicate: the rejected elements followed by the accepted ones
-- permute to the original list.
filterᵇ-split : ∀ {a} {A : Set a} (p : A → Bool) (xs : List A) →
                (filterᵇ (λ x → not (p x)) xs ++ filterᵇ p xs) ↭ xs
filterᵇ-split p []       = ↭-refl
filterᵇ-split p (x ∷ xs) with p x
... | true  = ↭-trans (shift x (filterᵇ (λ y → not (p y)) xs) (filterᵇ p xs))
                      (↭.prep x (filterᵇ-split p xs))
... | false = ↭.prep x (filterᵇ-split p xs)

Any-contra : ∀ {a p b} {A : Set a} {P : A → Set p} {B : Set b} {xs : List A} →
             (∀ {x} → P x → ⊥) → Any P xs → B
Any-contra contra (here px) = ⊥-elim (contra px)
Any-contra contra (there a) = Any-contra contra a

perm-length : ∀ {a r} {A : Set a} {R : A → A → Set r} {xs ys : List A} →
              H.Permutation R xs ys → length xs ≡ length ys
perm-length (H.refl pw)      = Pointwise-length pw
perm-length (H.prep _ p)     = ≡-cong suc (perm-length p)
perm-length (H.swap _ _ p)   = ≡-cong (λ n → suc (suc n)) (perm-length p)
perm-length (H.trans p q)    = ≡-trans (perm-length p) (perm-length q)

perm-All : ∀ {a r q} {A : Set a} {R : A → A → Set r} {P : A → Set q} →
           (∀ {x y} → R x y → P x → P y) →
           {xs ys : List A} → H.Permutation R xs ys → All P xs → All P ys
perm-All resp (H.refl [])          []         = []
perm-All resp (H.refl (r ∷ pw))    (px ∷ pxs) = resp r px ∷ perm-All resp (H.refl pw) pxs
perm-All resp (H.prep r p)         (px ∷ pxs) = resp r px ∷ perm-All resp p pxs
perm-All resp (H.swap r₁ r₂ p) (px ∷ py ∷ pxs) = resp r₂ py ∷ resp r₁ px ∷ perm-All resp p pxs
perm-All resp (H.trans p q)        pxs        = perm-All resp q (perm-All resp p pxs)

length-concat : ∀ {a} {A : Set a} (xss : List (List A)) → length (concat xss) ≡ sum (map length xss)
length-concat []         = ≡-refl
length-concat (xs ∷ xss) = ≡-trans (length-++ xs) (≡-cong (length xs +_) (length-concat xss))

sum-≥-length : ∀ {ns : List ℕ} → All (λ n → 1 ≤ n) ns → length ns ≤ sum ns
sum-≥-length []       = z≤n
sum-≥-length (h ∷ hs) = +-mono-≤ h (sum-≥-length hs)

sum-ones : ∀ {ns : List ℕ} → All (λ n → 1 ≤ n) ns → sum ns ≡ length ns → All (_≡ 1) ns
sum-ones []                                  _  = []
sum-ones {ns = suc m ∷ ns} (s≤s z≤n ∷ hs) eq = ≡-cong suc m≡0 ∷ sum-ones hs rest
  where
  eq₂ : m + sum ns ≡ length ns
  eq₂ = suc-injective eq

  m≡0 : m ≡ 0
  m≡0 = n≤0⇒n≡0 (+-cancelʳ-≤ (sum ns) m 0 (≤-trans (≤-reflexive eq₂) (sum-≥-length hs)))

  rest : sum ns ≡ length ns
  rest = ≡-trans (≡-cong (_+ sum ns) (≡-sym m≡0)) eq₂

singleton : ∀ {a} {A : Set a} (l : List A) → length l ≡ 1 → Σ A (λ x → l ≡ x ∷ [])
singleton (x ∷ []) e = x , ≡-refl

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

↭↭-of-↭ : ∀ {a} {A : Set a} {xss yss : List (List A)} → xss ↭ yss → xss ↭↭ yss
↭↭-of-↭ ↭.refl         = ↭↭-refl
↭↭-of-↭ (↭.prep x p)   = H.prep ↭-refl (↭↭-of-↭ p)
↭↭-of-↭ (↭.swap x y p) = H.swap ↭-refl ↭-refl (↭↭-of-↭ p)
↭↭-of-↭ (↭.trans p q)  = H.trans (↭↭-of-↭ p) (↭↭-of-↭ q)

↭↭-++⁺ : ∀ {a} {A : Set a} {xss yss uss vss : List (List A)} →
         xss ↭↭ yss → uss ↭↭ vss → (xss ++ uss) ↭↭ (yss ++ vss)
↭↭-++⁺ (H.refl [])        q = q
↭↭-++⁺ (H.refl (r ∷ pw))  q = H.prep r (↭↭-++⁺ (H.refl pw) q)
↭↭-++⁺ (H.prep r p)       q = H.prep r (↭↭-++⁺ p q)
↭↭-++⁺ (H.swap r₁ r₂ p)   q = H.swap r₁ r₂ (↭↭-++⁺ p q)
↭↭-++⁺ (H.trans p p')     q = H.trans (↭↭-++⁺ p q) (↭↭-++⁺ p' ↭↭-refl)

concat-↭↭ : ∀ {a b} {A : Set a} {B : Set b} {f g : A → List (List B)} {xs : List A} →
            All (λ x → f x ↭↭ g x) xs → concat (map f xs) ↭↭ concat (map g xs)
concat-↭↭ []         = ↭↭-refl
concat-↭↭ (px ∷ pxs) = ↭↭-++⁺ px (concat-↭↭ pxs)

concat-resp : ∀ {a} {A : Set a} {rss rss' : List (List A)} → rss ↭↭ rss' → concat rss ↭ concat rss'
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

partition-↭ : ∀ {a p} {A : Set a} {P : A → Set p} (P? : (x : A) → Dec (P x)) (xs : List A) →
              (proj₁ (partition P? xs) ++ proj₂ (partition P? xs)) ↭ xs
partition-↭ P? []       = ↭-refl
partition-↭ P? (x ∷ xs) with P? x
... | yes _ = ↭.prep x (partition-↭ P? xs)
... | no  _ =
  ↭-trans (shift x (proj₁ (partition P? xs)) (proj₂ (partition P? xs)))
          (↭.prep x (partition-↭ P? xs))

partition-All : ∀ {a p q} {A : Set a} {P : A → Set p} {Q : A → Set q}
                (P? : (x : A) → Dec (P x)) {xs : List A} → All Q xs →
                All Q (proj₁ (partition P? xs)) × All Q (proj₂ (partition P? xs))
partition-All P? [] = [] , []
partition-All P? (_∷_ {x} px pxs) with partition-All P? pxs
... | (a₁ , a₂) with P? x
...   | yes _ = px ∷ a₁ , a₂
...   | no  _ = a₁ , px ∷ a₂

part₂-¬ : ∀ {a p} {A : Set a} {P : A → Set p} (P? : (x : A) → Dec (P x)) (xs : List A) →
          All (λ x → ¬ P x) (proj₂ (partition P? xs))
part₂-¬ P? []       = []
part₂-¬ P? (x ∷ xs) with P? x
... | yes _  = part₂-¬ P? xs
... | no ¬px = ¬px ∷ part₂-¬ P? xs

partition-AllPairs : ∀ {a r p} {A : Set a} {S : A → A → Set r} {P : A → Set p}
                     (P? : (x : A) → Dec (P x)) → (∀ {x y} → S x y → S y x) →
                     ∀ {xs : List A} → AllPairs S xs →
                     AllPairs S (proj₁ (partition P? xs))
                     × AllPairs S (proj₂ (partition P? xs))
                     × All (λ y → All (λ x → S x y) (proj₁ (partition P? xs)))
                           (proj₂ (partition P? xs))
partition-AllPairs P? sym [] = [] , [] , []
partition-AllPairs P? sym (_∷_ {x} px ps) with partition-AllPairs P? sym ps | partition-All P? px
... | (a₁ , a₂ , cross) | (px₁ , px₂) with P? x
...   | yes _ = px₁ ∷ a₁ , a₂ , All.zipWith (λ (s , c) → s ∷ c) (px₂ , cross)
...   | no  _ = a₁ , px₂ ∷ a₂ , All-map (λ s → sym s) px₁ ∷ cross

AllPairs-++⁻ : ∀ {a r} {A : Set a} {S : A → A → Set r} (xs ys : List A) →
               AllPairs S (xs ++ ys) →
               AllPairs S xs × AllPairs S ys × All (λ x → All (S x) ys) xs
AllPairs-++⁻ []       ys ps        = [] , ps , []
AllPairs-++⁻ (x ∷ xs) ys (px ∷ ps) with AllPairs-++⁻ xs ys ps
... | (a₁ , a₂ , cross) = (AllP.++⁻ˡ xs px ∷ a₁) , a₂ , (AllP.++⁻ʳ xs px ∷ cross)

AllPairs-perm : ∀ {a r} {A : Set a} {S : A → A → Set r} →
                (∀ {x y} → S x y → S y x) →
                {xs ys : List A} → xs ↭ ys → AllPairs S xs → AllPairs S ys
AllPairs-perm sym ↭.refl         ps                            = ps
AllPairs-perm sym (↭.prep x p)   (px ∷ ps)                     = All-resp-↭ p px ∷ AllPairs-perm sym p ps
AllPairs-perm sym (↭.swap x y p) ((pxy ∷ pxs) ∷ (pys ∷ ps)) =
  (sym pxy ∷ All-resp-↭ p pys) ∷ (All-resp-↭ p pxs ∷ AllPairs-perm sym p ps)
AllPairs-perm sym (↭.trans p q)  ps                            = AllPairs-perm sym q (AllPairs-perm sym p ps)

perm-AllPairs : ∀ {a r s} {A : Set a} {R : A → A → Set r} {S : A → A → Set s} →
                (∀ {x y} → S x y → S y x) →
                (∀ {x x' y} → R x x' → S x y → S x' y) →
                {xs ys : List A} → H.Permutation R xs ys → AllPairs S xs → AllPairs S ys
perm-AllPairs sym resp (H.refl [])                []                      = []
perm-AllPairs sym resp (H.refl (r ∷ pw))          (px ∷ ps)               =
  perm-All (λ r' s' → sym (resp r' (sym s'))) (H.refl pw) (All-map (resp r) px) ∷
  perm-AllPairs sym resp (H.refl pw) ps
perm-AllPairs sym resp (H.prep r p)               (px ∷ ps)               =
  perm-All (λ r' s' → sym (resp r' (sym s'))) p (All-map (resp r) px) ∷
  perm-AllPairs sym resp p ps
perm-AllPairs sym resp (H.swap r₁ r₂ p) ((pxy ∷ pxs) ∷ (pys ∷ ps)) =
  (resp r₂ (sym (resp r₁ pxy)) ∷
   perm-All (λ r' s' → sym (resp r' (sym s'))) p (All-map (resp r₂) pys)) ∷
  (perm-All (λ r' s' → sym (resp r' (sym s'))) p (All-map (resp r₁) pxs) ∷
   perm-AllPairs sym resp p ps)
perm-AllPairs sym resp (H.trans p q)              ps                      =
  perm-AllPairs sym resp q (perm-AllPairs sym resp p ps)

filter-out-↭ : ∀ {a} {A : Set a} (_≟_ : DecidableEquality A) {x : A} {xs : List A} →
               AllPairs _≢_ xs → x ∈ xs →
               (x ∷ filter (λ y → ¬? (x ≟ y)) xs) ↭ xs
filter-out-↭ _≟_ {x} {y ∷ xs} (py ∷ ps) h with x ≟ y
... | no ¬e      = ↭-trans (↭.swap x y ↭.refl) (↭.prep y (filter-out-↭ _≟_ ps (tail ¬e h)))
... | yes ≡-refl = ↭.prep x (↭-reflexive (filter-all (λ z → ¬? (x ≟ z)) py))

dec-case : ∀ {a p} {A : Set a} {P : Set p} → Dec P → (P → A) → (¬ P → A) → A
dec-case (yes k)  t f = t k
dec-case (no  ¬k) t f = f ¬k

filter-permᴿ : ∀ {a p r} {A : Set a} {P : A → Set p} {R : A → A → Set r} →
               (P? : (x : A) → Dec (P x)) →
               (∀ {x y} → R x y → P x → P y) → (∀ {x y} → R x y → P y → P x) →
               {xs ys : List A} → H.Permutation R xs ys →
               H.Permutation R (filter P? xs) (filter P? ys)
filter-permᴿ P? to from (H.refl []) = H.refl []
filter-permᴿ {R = R} P? to from (H.refl (_∷_ {x} {y} {xs} {ys} rxy pw)) =
  dec-case (P? x)
    (λ px → subst₂ (H.Permutation R)
              (≡-sym (filter-accept P? {x} {xs} px))
              (≡-sym (filter-accept P? {y} {ys} (to rxy px)))
              (H.prep rxy (filter-permᴿ P? to from (H.refl pw))))
    (λ ¬px → subst₂ (H.Permutation R)
               (≡-sym (filter-reject P? {x} {xs} ¬px))
               (≡-sym (filter-reject P? {y} {ys} (λ py → ¬px (from rxy py))))
               (filter-permᴿ P? to from (H.refl pw)))
filter-permᴿ {R = R} P? to from (H.prep {xs} {ys} {x} {y} rxy p) =
  dec-case (P? x)
    (λ px → subst₂ (H.Permutation R)
              (≡-sym (filter-accept P? {x} {xs} px))
              (≡-sym (filter-accept P? {y} {ys} (to rxy px)))
              (H.prep rxy (filter-permᴿ P? to from p)))
    (λ ¬px → subst₂ (H.Permutation R)
               (≡-sym (filter-reject P? {x} {xs} ¬px))
               (≡-sym (filter-reject P? {y} {ys} (λ py → ¬px (from rxy py))))
               (filter-permᴿ P? to from p))
filter-permᴿ {R = R} P? to from (H.swap {xs} {ys} {x} {y} {x′} {y′} r₁ r₂ p) =
  dec-case (P? x)
    (λ px → dec-case (P? y)
      (λ py → subst₂ (H.Permutation R)
                (≡-sym (≡-trans (filter-accept P? {x} {y ∷ xs} px)
                                (≡-cong (x ∷_) (filter-accept P? {y} {xs} py))))
                (≡-sym (≡-trans (filter-accept P? {y′} {x′ ∷ ys} (to r₂ py))
                                (≡-cong (y′ ∷_) (filter-accept P? {x′} {ys} (to r₁ px)))))
                (H.swap r₁ r₂ (filter-permᴿ P? to from p)))
      (λ ¬py → subst₂ (H.Permutation R)
                 (≡-sym (≡-trans (filter-accept P? {x} {y ∷ xs} px)
                                 (≡-cong (x ∷_) (filter-reject P? {y} {xs} ¬py))))
                 (≡-sym (≡-trans (filter-reject P? {y′} {x′ ∷ ys} (λ q → ¬py (from r₂ q)))
                                 (filter-accept P? {x′} {ys} (to r₁ px))))
                 (H.prep r₁ (filter-permᴿ P? to from p))))
    (λ ¬px → dec-case (P? y)
      (λ py → subst₂ (H.Permutation R)
                (≡-sym (≡-trans (filter-reject P? {x} {y ∷ xs} ¬px)
                                (filter-accept P? {y} {xs} py)))
                (≡-sym (≡-trans (filter-accept P? {y′} {x′ ∷ ys} (to r₂ py))
                                (≡-cong (y′ ∷_)
                                        (filter-reject P? {x′} {ys} (λ q → ¬px (from r₁ q))))))
                (H.prep r₂ (filter-permᴿ P? to from p)))
      (λ ¬py → subst₂ (H.Permutation R)
                 (≡-sym (≡-trans (filter-reject P? {x} {y ∷ xs} ¬px)
                                 (filter-reject P? {y} {xs} ¬py)))
                 (≡-sym (≡-trans (filter-reject P? {y′} {x′ ∷ ys} (λ q → ¬py (from r₂ q)))
                                 (filter-reject P? {x′} {ys} (λ q → ¬px (from r₁ q)))))
                 (filter-permᴿ P? to from p)))
filter-permᴿ P? to from (H.trans p q) = H.trans (filter-permᴿ P? to from p) (filter-permᴿ P? to from q)

partition-permᴿ : ∀ {a p r} {A : Set a} {P : A → Set p} {R : A → A → Set r} →
                  (P? : (x : A) → Dec (P x)) →
                  (∀ {x y} → R x y → P x → P y) → (∀ {x y} → R x y → P y → P x) →
                  {xs ys : List A} → H.Permutation R xs ys →
                  H.Permutation R (proj₁ (partition P? xs)) (proj₁ (partition P? ys)) ×
                  H.Permutation R (proj₂ (partition P? xs)) (proj₂ (partition P? ys))
partition-permᴿ {R = R} P? to from {xs} {ys} p =
  subst₂ (λ u v → H.Permutation R (proj₁ u) (proj₁ v))
         (≡-sym (partition-defn P? xs)) (≡-sym (partition-defn P? ys))
         (filter-permᴿ P? to from p) ,
  subst₂ (λ u v → H.Permutation R (proj₂ u) (proj₂ v))
         (≡-sym (partition-defn P? xs)) (≡-sym (partition-defn P? ys))
         (filter-permᴿ (λ x → ¬? (P? x))
                       (λ rxy ¬px py → ¬px (from rxy py)) (λ rxy ¬py px → ¬py (to rxy px)) p)

filter-concat : ∀ {a p} {A : Set a} {P : A → Set p} (P? : (x : A) → Dec (P x)) (xss : List (List A)) →
                filter P? (concat xss) ≡ concat (map (filter P?) xss)
filter-concat P? []         = ≡-refl
filter-concat P? (xs ∷ xss) =
  ≡-trans (ListP.filter-++ P? xs (concat xss))
          (≡-cong (filter P? xs ++_) (filter-concat P? xss))

filter-comm : ∀ {a p q} {A : Set a} {P : A → Set p} {Q : A → Set q}
              (P? : (x : A) → Dec (P x)) (Q? : (x : A) → Dec (Q x)) (xs : List A) →
              filter P? (filter Q? xs) ≡ filter Q? (filter P? xs)
filter-comm P? Q? []       = ≡-refl
filter-comm P? Q? (x ∷ xs) =
  dec-case (Q? x)
    (λ qx → dec-case (P? x)
      (λ px →
        ≡-trans (≡-cong (filter P?) (filter-accept Q? {x} {xs} qx))
        (≡-trans (filter-accept P? {x} {filter Q? xs} px)
        (≡-trans (≡-cong (x ∷_) (filter-comm P? Q? xs))
        (≡-sym (≡-trans (≡-cong (filter Q?) (filter-accept P? {x} {xs} px))
                        (filter-accept Q? {x} {filter P? xs} qx))))))
      (λ ¬px →
        ≡-trans (≡-cong (filter P?) (filter-accept Q? {x} {xs} qx))
        (≡-trans (filter-reject P? {x} {filter Q? xs} ¬px)
        (≡-trans (filter-comm P? Q? xs)
                 (≡-sym (≡-cong (filter Q?) (filter-reject P? {x} {xs} ¬px)))))))
    (λ ¬qx → dec-case (P? x)
      (λ px →
        ≡-trans (≡-cong (filter P?) (filter-reject Q? {x} {xs} ¬qx))
        (≡-trans (filter-comm P? Q? xs)
        (≡-sym (≡-trans (≡-cong (filter Q?) (filter-accept P? {x} {xs} px))
                        (filter-reject Q? {x} {filter P? xs} ¬qx)))))
      (λ ¬px →
        ≡-trans (≡-cong (filter P?) (filter-reject Q? {x} {xs} ¬qx))
        (≡-trans (filter-comm P? Q? xs)
                 (≡-sym (≡-cong (filter Q?) (filter-reject P? {x} {xs} ¬px))))))

filter-avoid : ∀ {a p q} {A : Set a} {P : A → Set p} {Q : A → Set q}
               (P? : (x : A) → Dec (P x)) (Q? : (x : A) → Dec (Q x)) (xs : List A) →
               ¬ Any (λ x → Q x × P x) xs →
               filter P? (filter (∁? Q?) xs) ≡ filter P? xs
filter-avoid P? Q? []       h = ≡-refl
filter-avoid P? Q? (x ∷ xs) h =
  dec-case (Q? x)
    (λ qx →
      ≡-trans (≡-cong (filter P?) (filter-reject (∁? Q?) {x} {xs} (λ k → k qx)))
      (≡-trans (filter-avoid P? Q? xs (λ m → h (there m)))
               (≡-sym (filter-reject P? {x} {xs} (λ px → h (here (qx , px)))))))
    (λ ¬qx →
      ≡-trans (≡-cong (filter P?) (filter-accept (∁? Q?) {x} {xs} ¬qx))
              (dec-case (P? x)
                (λ px →
                  ≡-trans (filter-accept P? {x} {filter (∁? Q?) xs} px)
                  (≡-trans (≡-cong (x ∷_) (filter-avoid P? Q? xs (λ m → h (there m))))
                           (≡-sym (filter-accept P? {x} {xs} px))))
                (λ ¬px →
                  ≡-trans (filter-reject P? {x} {filter (∁? Q?) xs} ¬px)
                  (≡-trans (filter-avoid P? Q? xs (λ m → h (there m)))
                           (≡-sym (filter-reject P? {x} {xs} ¬px))))))

filter-exchange : ∀ {a p q} {A : Set a} {P : A → Set p} {Q : A → Set q}
                  (P? : (x : A) → Dec (P x)) (Q? : (x : A) → Dec (Q x)) (xs : List A) →
                  (filter Q? xs ++ filter P? (filter (∁? Q?) xs)) ↭
                  (filter P? xs ++ filter Q? (filter (∁? P?) xs))
filter-exchange P? Q? []       = ↭-refl
filter-exchange P? Q? (x ∷ xs) =
  dec-case (Q? x)
    (λ qx → dec-case (P? x)
      (λ px →
        ↭-trans (↭-reflexive (≡-cong₂ _++_ (filter-accept Q? {x} {xs} qx)
                   (≡-cong (filter P?) (filter-reject (∁? Q?) {x} {xs} (λ k → k qx)))))
        (↭-trans (↭.prep x (filter-exchange P? Q? xs))
                 (↭-reflexive (≡-sym (≡-cong₂ _++_ (filter-accept P? {x} {xs} px)
                    (≡-cong (filter Q?) (filter-reject (∁? P?) {x} {xs} (λ k → k px))))))))
      (λ ¬px →
        ↭-trans (↭-reflexive (≡-cong₂ _++_ (filter-accept Q? {x} {xs} qx)
                   (≡-cong (filter P?) (filter-reject (∁? Q?) {x} {xs} (λ k → k qx)))))
        (↭-trans (↭.prep x (filter-exchange P? Q? xs))
        (↭-trans (↭-sym (shift x (filter P? xs) (filter Q? (filter (∁? P?) xs))))
                 (↭-reflexive (≡-sym (≡-cong₂ _++_ (filter-reject P? {x} {xs} ¬px)
                    (≡-trans (≡-cong (filter Q?) (filter-accept (∁? P?) {x} {xs} ¬px))
                             (filter-accept Q? {x} {filter (∁? P?) xs} qx)))))))))
    (λ ¬qx → dec-case (P? x)
      (λ px →
        ↭-trans (↭-reflexive (≡-cong₂ _++_ (filter-reject Q? {x} {xs} ¬qx)
                   (≡-trans (≡-cong (filter P?) (filter-accept (∁? Q?) {x} {xs} ¬qx))
                            (filter-accept P? {x} {filter (∁? Q?) xs} px))))
        (↭-trans (shift x (filter Q? xs) (filter P? (filter (∁? Q?) xs)))
        (↭-trans (↭.prep x (filter-exchange P? Q? xs))
                 (↭-reflexive (≡-sym (≡-cong₂ _++_ (filter-accept P? {x} {xs} px)
                    (≡-cong (filter Q?) (filter-reject (∁? P?) {x} {xs} (λ k → k px)))))))))
      (λ ¬px →
        ↭-trans (↭-reflexive (≡-cong₂ _++_ (filter-reject Q? {x} {xs} ¬qx)
                   (≡-trans (≡-cong (filter P?) (filter-accept (∁? Q?) {x} {xs} ¬qx))
                            (filter-reject P? {x} {filter (∁? Q?) xs} ¬px))))
        (↭-trans (filter-exchange P? Q? xs)
                 (↭-reflexive (≡-sym (≡-cong₂ _++_ (filter-reject P? {x} {xs} ¬px)
                    (≡-trans (≡-cong (filter Q?) (filter-accept (∁? P?) {x} {xs} ¬px))
                             (filter-reject Q? {x} {filter (∁? P?) xs} ¬qx))))))))

map-partition₁ : ∀ {a b p} {A : Set a} {B : Set b} {P : B → Set p} (h : A → B)
                 (P? : (x : B) → Dec (P x)) (xs : List A) →
                 proj₁ (partition P? (map h xs)) ≡ map h (proj₁ (partition (λ x → P? (h x)) xs))
map-partition₁ h P? []       = ≡-refl
map-partition₁ h P? (x ∷ xs) with P? (h x)
... | yes _ = ≡-cong (h x ∷_) (map-partition₁ h P? xs)
... | no  _ = map-partition₁ h P? xs

map-partition₂ : ∀ {a b p} {A : Set a} {B : Set b} {P : B → Set p} (h : A → B)
                 (P? : (x : B) → Dec (P x)) (xs : List A) →
                 proj₂ (partition P? (map h xs)) ≡ map h (proj₂ (partition (λ x → P? (h x)) xs))
map-partition₂ h P? []       = ≡-refl
map-partition₂ h P? (x ∷ xs) with P? (h x)
... | yes _ = map-partition₂ h P? xs
... | no  _ = ≡-cong (h x ∷_) (map-partition₂ h P? xs)
