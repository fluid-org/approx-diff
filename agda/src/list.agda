{-# OPTIONS --prop --postfix-projections --safe #-}

-- Permutation and partition lemmas for lists, including lists of lists compared up to reordering
-- at both levels.
module list where

open import Data.Bool as Bool using (Bool; not; _∨_)
open import Data.Bool.ListAction using (any)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool.Properties using (∨-assoc)
open import Data.Fin as Fin using (Fin)
open import Data.List using (List; []; _∷_; _++_; length; map; concat; filterᵇ; partitionᵇ; tabulate)
open import Data.Nat.ListAction using (sum)
open import Data.List.Properties using (++-assoc; length-++)
import Data.List.Relation.Binary.Permutation.Homogeneous as H
import Data.List.Relation.Binary.Permutation.Propositional as ↭
open ↭ using (_↭_; ↭-refl; ↭-sym; ↭-trans; ↭-reflexive)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_; Pointwise-length)
open import Data.List.Relation.Unary.All using (All; []; _∷_; universal) renaming (map to All-map)
import Data.List.Relation.Unary.All.Properties as AllP
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
open import Data.List.Relation.Unary.Any using (Any; here; there; tail)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties
  using (++⁺; ++-comm; shift; All-resp-↭)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (suc-injective; n≤0⇒n≡0; +-cancelʳ-≤; +-mono-≤; ≤-reflexive; ≤-trans)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Nullary.Decidable using (does; yes; no; dec-false)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; subst; subst₂)
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

∨-false : ∀ x y → (x ∨ y) ≡ Bool.false → (x ≡ Bool.false) × (y ≡ Bool.false)
∨-false Bool.false y h = ≡-refl , h

∨-true : ∀ x → (x ∨ Bool.true) ≡ Bool.true
∨-true Bool.false = ≡-refl
∨-true Bool.true  = ≡-refl

∨-true-inv : ∀ x y → (x ∨ y) ≡ Bool.true → (x ≡ Bool.true) ⊎ (y ≡ Bool.true)
∨-true-inv Bool.true  y h = inj₁ ≡-refl
∨-true-inv Bool.false y h = inj₂ h

any-false : ∀ {a} {A : Set a} {f : A → Bool} {xs : List A} →
            All (λ x → f x ≡ Bool.false) xs → any f xs ≡ Bool.false
any-false []       = ≡-refl
any-false (h ∷ hs) = ≡-cong₂ _∨_ h (any-false hs)

any-false-All : ∀ {a} {A : Set a} (f : A → Bool) (xs : List A) →
                any f xs ≡ Bool.false → All (λ x → f x ≡ Bool.false) xs
any-false-All f []       h = []
any-false-All f (x ∷ xs) h with ∨-false (f x) (any f xs) h
... | (hx , hxs) = hx ∷ any-false-All f xs hxs

any-tabulate-false : ∀ {a} {A : Set a} {n} (g : Fin n → A) (f : A → Bool) →
                     any f (tabulate g) ≡ Bool.false → ∀ i → f (g i) ≡ Bool.false
any-tabulate-false g f h Fin.zero    = proj₁ (∨-false (f (g Fin.zero)) _ h)
any-tabulate-false g f h (Fin.suc i) =
  any-tabulate-false (λ k → g (Fin.suc k)) f (proj₂ (∨-false (f (g Fin.zero)) _ h)) i

Any-All : ∀ {a p q} {A : Set a} {P : A → Set p} {Q : A → Set q} {xs : List A} →
          Any P xs → All Q xs → Any (λ x → P x × Q x) xs
Any-All (here px) (qx ∷ _) = here (px , qx)
Any-All (there a) (_ ∷ qs) = there (Any-All a qs)

Any-contra : ∀ {a p b} {A : Set a} {P : A → Set p} {B : Set b} {xs : List A} →
             (∀ {x} → P x → ⊥) → Any P xs → B
Any-contra contra (here px) = ⊥-elim (contra px)
Any-contra contra (there a) = Any-contra contra a

map-All-cong : ∀ {a b} {A : Set a} {B : Set b} {f g : A → B} {xs : List A} →
               All (λ x → f x ≡ g x) xs → map f xs ≡ map g xs
map-All-cong []       = ≡-refl
map-All-cong (h ∷ hs) = ≡-cong₂ _∷_ h (map-All-cong hs)

any-or : ∀ {a} {A : Set a} (f g : A → Bool) (xs : List A) →
         any (λ x → f x ∨ g x) xs ≡ (any f xs ∨ any g xs)
any-or f g []       = ≡-refl
any-or f g (x ∷ xs) =
  ≡-trans (≡-cong ((f x ∨ g x) ∨_) (any-or f g xs)) (∨-interchange (f x) (g x) (any f xs) (any g xs))

any-++ : ∀ {a} {A : Set a} (f : A → Bool) (xs ys : List A) →
         any f (xs ++ ys) ≡ (any f xs ∨ any f ys)
any-++ f []       ys = ≡-refl
any-++ f (x ∷ xs) ys = ≡-trans (≡-cong (f x ∨_) (any-++ f xs ys)) (≡-sym (∨-assoc (f x) _ _))

any-concat : ∀ {a} {A : Set a} (f : A → Bool) (xss : List (List A)) →
             any f (concat xss) ≡ any (λ xs → any f xs) xss
any-concat f []         = ≡-refl
any-concat f (xs ∷ xss) =
  ≡-trans (any-++ f xs (concat xss)) (≡-cong (any f xs ∨_) (any-concat f xss))

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

length-concat : ∀ {a} {A : Set a} (xss : List (List A)) →
                length (concat xss) ≡ sum (map length xss)
length-concat []         = ≡-refl
length-concat (xs ∷ xss) =
  ≡-trans (length-++ xs) (≡-cong (length xs +_) (length-concat xss))

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

AllPairs-zip : ∀ {a r s} {A : Set a} {S : A → A → Set r} {S' : A → A → Set s} →
               ∀ {xs : List A} → AllPairs S xs → AllPairs S' xs →
               AllPairs (λ x y → S x y × S' x y) xs
AllPairs-zip []         []           = []
AllPairs-zip (px ∷ ps) (px' ∷ ps') = All-zip _,_ px px' ∷ AllPairs-zip ps ps'

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

∈-filterᵇ⁻ : ∀ {a} {A : Set a} (g : A → Bool) {x : A} (xs : List A) → x ∈ filterᵇ g xs → x ∈ xs
∈-filterᵇ⁻ g (y ∷ xs) h with g y
... | Bool.false = there (∈-filterᵇ⁻ g xs h)
... | Bool.true with h
...   | here e   = here e
...   | there h' = there (∈-filterᵇ⁻ g xs h')

any-filterᵇ : ∀ {a} {A : Set a} (f g : A → Bool) (xs : List A) →
              any f (filterᵇ g xs) ≡ Bool.true → any f xs ≡ Bool.true
any-filterᵇ f g (x ∷ xs) h with g x
... | Bool.false = ≡-trans (≡-cong (f x ∨_) (any-filterᵇ f g xs h)) (∨-true (f x))
... | Bool.true with ∨-true-inv (f x) (any f (filterᵇ g xs)) h
...   | inj₁ e = ≡-cong (_∨ any f xs) e
...   | inj₂ e = ≡-trans (≡-cong (f x ∨_) (any-filterᵇ f g xs e)) (∨-true (f x))

filter-All : ∀ {a p} {A : Set a} {P : A → Set p} (f : A → Bool) {xs : List A} →
             All P xs → All P (filterᵇ f xs)
filter-All f []               = []
filter-All f (_∷_ {x} px pxs) with f x
... | Bool.true  = px ∷ filter-All f pxs
... | Bool.false = filter-All f pxs

filter-AllPairs : ∀ {a r} {A : Set a} {S : A → A → Set r} (f : A → Bool) {xs : List A} →
                  AllPairs S xs → AllPairs S (filterᵇ f xs)
filter-AllPairs f []               = []
filter-AllPairs f (_∷_ {x} px ps) with f x
... | Bool.true  = filter-All f px ∷ filter-AllPairs f ps
... | Bool.false = filter-AllPairs f ps

filter-all-true : ∀ {a} {A : Set a} {f : A → Bool} {xs : List A} →
                  All (λ x → f x ≡ Bool.true) xs → filterᵇ f xs ≡ xs
filter-all-true []              = ≡-refl
filter-all-true (_∷_ {x} h hs) rewrite h = ≡-cong (x ∷_) (filter-all-true hs)

filter-head-false : ∀ {a} {A : Set a} {f : A → Bool} {x : A} (xs : List A) →
                    f x ≡ Bool.false → filterᵇ f (x ∷ xs) ≡ filterᵇ f xs
filter-head-false xs h rewrite h = ≡-refl

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
AllPairs-perm sym (↭.prep x p)   (px ∷ ps)                     =
  All-resp-↭ p px ∷ AllPairs-perm sym p ps
AllPairs-perm sym (↭.swap x y p) ((pxy ∷ pxs) ∷ (pys ∷ ps)) =
  (sym pxy ∷ All-resp-↭ p pys) ∷ (All-resp-↭ p pxs ∷ AllPairs-perm sym p ps)
AllPairs-perm sym (↭.trans p q)  ps                            =
  AllPairs-perm sym q (AllPairs-perm sym p ps)

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
               (x ∷ filterᵇ (λ y → not (does (x ≟ y))) xs) ↭ xs
filter-out-↭ _≟_ {x} {y ∷ xs} (py ∷ ps) h with x ≟ y
... | no ¬e   = ↭-trans (↭.swap x y ↭.refl) (↭.prep y (filter-out-↭ _≟_ ps (tail ¬e h)))
... | yes ≡-refl =
  ↭.prep x (↭-reflexive (filter-all-true (All-map (λ {z} hz → ≡-cong not (dec-false (x ≟ z) hz)) py)))

filter-head-true : ∀ {a} {A : Set a} {f : A → Bool} {x : A} (xs : List A) →
                   f x ≡ Bool.true → filterᵇ f (x ∷ xs) ≡ x ∷ filterᵇ f xs
filter-head-true xs h rewrite h = ≡-refl

partition-filter : ∀ {a} {A : Set a} (f : A → Bool) (xs : List A) →
                   partitionᵇ f xs ≡ (filterᵇ f xs , filterᵇ (λ x → not (f x)) xs)
partition-filter f []       = ≡-refl
partition-filter f (x ∷ xs) rewrite partition-filter f xs with f x
... | Bool.true  = ≡-refl
... | Bool.false = ≡-refl

bool-case : ∀ {a} {A : Set a} (b : Bool) → (b ≡ Bool.true → A) → (b ≡ Bool.false → A) → A
bool-case Bool.true  t f = t ≡-refl
bool-case Bool.false t f = f ≡-refl

filter-permᴿ : ∀ {a r} {A : Set a} {R : A → A → Set r} (f : A → Bool) →
               (∀ {x y} → R x y → f x ≡ f y) →
               {xs ys : List A} → H.Permutation R xs ys →
               H.Permutation R (filterᵇ f xs) (filterᵇ f ys)
filter-permᴿ f resp (H.refl []) = H.refl []
filter-permᴿ {R = R} f resp (H.refl (_∷_ {x} {y} {xs} {ys} rxy pw)) =
  bool-case (f x)
    (λ ex → subst₂ (H.Permutation R)
              (≡-sym (filter-head-true {f = f} {x = x} xs ex))
              (≡-sym (filter-head-true {f = f} {x = y} ys (≡-trans (≡-sym (resp rxy)) ex)))
              (H.prep rxy (filter-permᴿ f resp (H.refl pw))))
    (λ ex → subst₂ (H.Permutation R)
              (≡-sym (filter-head-false {f = f} {x = x} xs ex))
              (≡-sym (filter-head-false {f = f} {x = y} ys (≡-trans (≡-sym (resp rxy)) ex)))
              (filter-permᴿ f resp (H.refl pw)))
filter-permᴿ {R = R} f resp (H.prep {xs} {ys} {x} {y} rxy p) =
  bool-case (f x)
    (λ ex → subst₂ (H.Permutation R)
              (≡-sym (filter-head-true {f = f} {x = x} xs ex))
              (≡-sym (filter-head-true {f = f} {x = y} ys (≡-trans (≡-sym (resp rxy)) ex)))
              (H.prep rxy (filter-permᴿ f resp p)))
    (λ ex → subst₂ (H.Permutation R)
              (≡-sym (filter-head-false {f = f} {x = x} xs ex))
              (≡-sym (filter-head-false {f = f} {x = y} ys (≡-trans (≡-sym (resp rxy)) ex)))
              (filter-permᴿ f resp p))
filter-permᴿ {R = R} f resp (H.swap {xs} {ys} {x} {y} {x′} {y′} eq₁ eq₂ p) =
  bool-case (f x)
    (λ ex → bool-case (f y)
      (λ ey → subst₂ (H.Permutation R)
                (≡-sym (≡-trans (filter-head-true {f = f} {x = x} (y ∷ xs) ex)
                                (≡-cong (x ∷_) (filter-head-true {f = f} {x = y} xs ey))))
                (≡-sym (≡-trans (filter-head-true {f = f} {x = y′} (x′ ∷ ys) (≡-trans (≡-sym (resp eq₂)) ey))
                                (≡-cong (y′ ∷_)
                                        (filter-head-true {f = f} {x = x′} ys (≡-trans (≡-sym (resp eq₁)) ex)))))
                (H.swap eq₁ eq₂ (filter-permᴿ f resp p)))
      (λ ey → subst₂ (H.Permutation R)
                (≡-sym (≡-trans (filter-head-true {f = f} {x = x} (y ∷ xs) ex)
                                (≡-cong (x ∷_) (filter-head-false {f = f} {x = y} xs ey))))
                (≡-sym (≡-trans (filter-head-false {f = f} {x = y′} (x′ ∷ ys) (≡-trans (≡-sym (resp eq₂)) ey))
                                (filter-head-true {f = f} {x = x′} ys (≡-trans (≡-sym (resp eq₁)) ex))))
                (H.prep eq₁ (filter-permᴿ f resp p))))
    (λ ex → bool-case (f y)
      (λ ey → subst₂ (H.Permutation R)
                (≡-sym (≡-trans (filter-head-false {f = f} {x = x} (y ∷ xs) ex)
                                (filter-head-true {f = f} {x = y} xs ey)))
                (≡-sym (≡-trans (filter-head-true {f = f} {x = y′} (x′ ∷ ys) (≡-trans (≡-sym (resp eq₂)) ey))
                                (≡-cong (y′ ∷_)
                                        (filter-head-false {f = f} {x = x′} ys (≡-trans (≡-sym (resp eq₁)) ex)))))
                (H.prep eq₂ (filter-permᴿ f resp p)))
      (λ ey → subst₂ (H.Permutation R)
                (≡-sym (≡-trans (filter-head-false {f = f} {x = x} (y ∷ xs) ex)
                                (filter-head-false {f = f} {x = y} xs ey)))
                (≡-sym (≡-trans (filter-head-false {f = f} {x = y′} (x′ ∷ ys) (≡-trans (≡-sym (resp eq₂)) ey))
                                (filter-head-false {f = f} {x = x′} ys (≡-trans (≡-sym (resp eq₁)) ex))))
                (filter-permᴿ f resp p)))
filter-permᴿ f resp (H.trans p q) = H.trans (filter-permᴿ f resp p) (filter-permᴿ f resp q)

partition-permᴿ : ∀ {a r} {A : Set a} {R : A → A → Set r} (f : A → Bool) →
                  (∀ {x y} → R x y → f x ≡ f y) →
                  {xs ys : List A} → H.Permutation R xs ys →
                  H.Permutation R (proj₁ (partitionᵇ f xs)) (proj₁ (partitionᵇ f ys))
                  × H.Permutation R (proj₂ (partitionᵇ f xs)) (proj₂ (partitionᵇ f ys))
partition-permᴿ {R = R} f resp {xs} {ys} p =
  subst₂ (λ u v → H.Permutation R (proj₁ u) (proj₁ v))
         (≡-sym (partition-filter f xs)) (≡-sym (partition-filter f ys))
         (filter-permᴿ f resp p) ,
  subst₂ (λ u v → H.Permutation R (proj₂ u) (proj₂ v))
         (≡-sym (partition-filter f xs)) (≡-sym (partition-filter f ys))
         (filter-permᴿ (λ x → not (f x)) (λ rxy → ≡-cong not (resp rxy)) p)

filter-++ : ∀ {a} {A : Set a} (f : A → Bool) (xs ys : List A) →
            filterᵇ f (xs ++ ys) ≡ filterᵇ f xs ++ filterᵇ f ys
filter-++ f []       ys = ≡-refl
filter-++ f (x ∷ xs) ys =
  bool-case (f x)
    (λ ef → ≡-trans (filter-head-true {f = f} {x = x} (xs ++ ys) ef)
            (≡-trans (≡-cong (x ∷_) (filter-++ f xs ys))
                     (≡-cong (_++ filterᵇ f ys) (≡-sym (filter-head-true {f = f} {x = x} xs ef)))))
    (λ ef → ≡-trans (filter-head-false {f = f} {x = x} (xs ++ ys) ef)
            (≡-trans (filter-++ f xs ys)
                     (≡-cong (_++ filterᵇ f ys) (≡-sym (filter-head-false {f = f} {x = x} xs ef)))))

filter-none : ∀ {a} {A : Set a} {f : A → Bool} {xs : List A} →
              All (λ x → f x ≡ Bool.false) xs → filterᵇ f xs ≡ []
filter-none []              = ≡-refl
filter-none (_∷_ {x} h hs) rewrite h = filter-none hs

filter-concat : ∀ {a} {A : Set a} (f : A → Bool) (xss : List (List A)) →
                filterᵇ f (concat xss) ≡ concat (map (filterᵇ f) xss)
filter-concat f []         = ≡-refl
filter-concat f (xs ∷ xss) =
  ≡-trans (filter-++ f xs (concat xss)) (≡-cong (filterᵇ f xs ++_) (filter-concat f xss))

filter-comm : ∀ {a} {A : Set a} (f g : A → Bool) (xs : List A) →
              filterᵇ f (filterᵇ g xs) ≡ filterᵇ g (filterᵇ f xs)
filter-comm f g []       = ≡-refl
filter-comm f g (x ∷ xs) =
  bool-case (g x)
    (λ eg → bool-case (f x)
      (λ ef →
        ≡-trans (≡-cong (filterᵇ f) (filter-head-true {f = g} {x = x} xs eg))
        (≡-trans (filter-head-true {f = f} {x = x} (filterᵇ g xs) ef)
        (≡-trans (≡-cong (x ∷_) (filter-comm f g xs))
        (≡-sym (≡-trans (≡-cong (filterᵇ g) (filter-head-true {f = f} {x = x} xs ef))
                        (filter-head-true {f = g} {x = x} (filterᵇ f xs) eg))))))
      (λ ef →
        ≡-trans (≡-cong (filterᵇ f) (filter-head-true {f = g} {x = x} xs eg))
        (≡-trans (filter-head-false {f = f} {x = x} (filterᵇ g xs) ef)
        (≡-trans (filter-comm f g xs)
        (≡-sym (≡-cong (filterᵇ g) (filter-head-false {f = f} {x = x} xs ef)))))))
    (λ eg → bool-case (f x)
      (λ ef →
        ≡-trans (≡-cong (filterᵇ f) (filter-head-false {f = g} {x = x} xs eg))
        (≡-trans (filter-comm f g xs)
        (≡-sym (≡-trans (≡-cong (filterᵇ g) (filter-head-true {f = f} {x = x} xs ef))
                        (filter-head-false {f = g} {x = x} (filterᵇ f xs) eg)))))
      (λ ef →
        ≡-trans (≡-cong (filterᵇ f) (filter-head-false {f = g} {x = x} xs eg))
        (≡-trans (filter-comm f g xs)
        (≡-sym (≡-cong (filterᵇ g) (filter-head-false {f = f} {x = x} xs ef))))))

any-filterᵇ-∧ : ∀ {a} {A : Set a} (f g : A → Bool) (xs : List A) →
                any f (filterᵇ g xs) ≡ any (λ x → g x Bool.∧ f x) xs
any-filterᵇ-∧ f g []       = ≡-refl
any-filterᵇ-∧ f g (x ∷ xs) =
  bool-case (g x)
    (λ eg → ≡-trans (≡-cong (any f) (filter-head-true {f = g} {x = x} xs eg))
            (≡-trans (≡-cong (f x ∨_) (any-filterᵇ-∧ f g xs))
                     (≡-sym (≡-cong (λ b → (b Bool.∧ f x) ∨ any (λ x' → g x' Bool.∧ f x') xs) eg))))
    (λ eg → ≡-trans (≡-cong (any f) (filter-head-false {f = g} {x = x} xs eg))
            (≡-trans (any-filterᵇ-∧ f g xs)
                     (≡-sym (≡-cong (λ b → (b Bool.∧ f x) ∨ any (λ x' → g x' Bool.∧ f x') xs) eg))))

filter-avoid : ∀ {a} {A : Set a} (f g : A → Bool) (xs : List A) →
               any (λ x → g x Bool.∧ f x) xs ≡ Bool.false →
               filterᵇ f (filterᵇ (λ x → not (g x)) xs) ≡ filterᵇ f xs
filter-avoid f g []       h = ≡-refl
filter-avoid f g (x ∷ xs) h with ∨-false (g x Bool.∧ f x) (any (λ x' → g x' Bool.∧ f x') xs) h
... | (hx , hxs) =
  bool-case (g x)
    (λ eg →
      ≡-trans (≡-cong (filterᵇ f) (filter-head-false {x = x} xs (≡-cong not eg)))
      (≡-trans (filter-avoid f g xs hxs)
               (≡-sym (filter-head-false {f = f} {x = x} xs
                        (≡-trans (≡-sym (≡-cong (Bool._∧ f x) eg)) hx)))))
    (λ eg →
      ≡-trans (≡-cong (filterᵇ f) (filter-head-true {x = x} xs (≡-cong not eg)))
      (≡-trans (bool-case (f x)
        (λ ef → ≡-trans (filter-head-true {f = f} {x = x} (filterᵇ (λ x' → not (g x')) xs) ef)
                (≡-trans (≡-cong (x ∷_) (filter-avoid f g xs hxs))
                         (≡-sym (filter-head-true {f = f} {x = x} xs ef))))
        (λ ef → ≡-trans (filter-head-false {f = f} {x = x} (filterᵇ (λ x' → not (g x')) xs) ef)
                (≡-trans (filter-avoid f g xs hxs)
                         (≡-sym (filter-head-false {f = f} {x = x} xs ef)))))
               ≡-refl))

filter-exchange : ∀ {a} {A : Set a} (f g : A → Bool) (xs : List A) →
                  (filterᵇ g xs ++ filterᵇ f (filterᵇ (λ x → not (g x)) xs)) ↭
                  (filterᵇ f xs ++ filterᵇ g (filterᵇ (λ x → not (f x)) xs))
filter-exchange f g []       = ↭-refl
filter-exchange f g (x ∷ xs) =
  bool-case (g x)
    (λ eg → bool-case (f x)
      (λ ef →
        ↭-trans (↭-reflexive (≡-cong₂ _++_ (filter-head-true {f = g} {x = x} xs eg)
                   (≡-cong (filterᵇ f) (filter-head-false {x = x} xs (≡-cong not eg)))))
        (↭-trans (↭.prep x (filter-exchange f g xs))
                 (↭-reflexive (≡-sym (≡-cong₂ _++_ (filter-head-true {f = f} {x = x} xs ef)
                    (≡-cong (filterᵇ g) (filter-head-false {x = x} xs (≡-cong not ef))))))))
      (λ ef →
        ↭-trans (↭-reflexive (≡-cong₂ _++_ (filter-head-true {f = g} {x = x} xs eg)
                   (≡-cong (filterᵇ f) (filter-head-false {x = x} xs (≡-cong not eg)))))
        (↭-trans (↭.prep x (filter-exchange f g xs))
        (↭-trans (↭-sym (shift x (filterᵇ f xs) (filterᵇ g (filterᵇ (λ x' → not (f x')) xs))))
                 (↭-reflexive (≡-sym (≡-cong₂ _++_ (filter-head-false {f = f} {x = x} xs ef)
                    (≡-trans (≡-cong (filterᵇ g) (filter-head-true {x = x} xs (≡-cong not ef)))
                             (filter-head-true {f = g} {x = x}
                               (filterᵇ (λ x' → not (f x')) xs) eg)))))))))
    (λ eg → bool-case (f x)
      (λ ef →
        ↭-trans (↭-reflexive (≡-cong₂ _++_ (filter-head-false {f = g} {x = x} xs eg)
                   (≡-trans (≡-cong (filterᵇ f) (filter-head-true {x = x} xs (≡-cong not eg)))
                            (filter-head-true {f = f} {x = x}
                              (filterᵇ (λ x' → not (g x')) xs) ef))))
        (↭-trans (shift x (filterᵇ g xs) (filterᵇ f (filterᵇ (λ x' → not (g x')) xs)))
        (↭-trans (↭.prep x (filter-exchange f g xs))
                 (↭-reflexive (≡-sym (≡-cong₂ _++_ (filter-head-true {f = f} {x = x} xs ef)
                    (≡-cong (filterᵇ g) (filter-head-false {x = x} xs (≡-cong not ef)))))))))
      (λ ef →
        ↭-trans (↭-reflexive (≡-cong₂ _++_ (filter-head-false {f = g} {x = x} xs eg)
                   (≡-trans (≡-cong (filterᵇ f) (filter-head-true {x = x} xs (≡-cong not eg)))
                            (filter-head-false {f = f} {x = x}
                              (filterᵇ (λ x' → not (g x')) xs) ef))))
        (↭-trans (filter-exchange f g xs)
                 (↭-reflexive (≡-sym (≡-cong₂ _++_ (filter-head-false {f = f} {x = x} xs ef)
                    (≡-trans (≡-cong (filterᵇ g) (filter-head-true {x = x} xs (≡-cong not ef)))
                             (filter-head-false {f = g} {x = x}
                               (filterᵇ (λ x' → not (f x')) xs) eg))))))))

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
