{-# OPTIONS --prop --postfix-projections --safe #-}

open import Data.Bool as Bool using (Bool; _∨_)
open import Data.Bool.ListAction using (any)
open import Data.Fin using (Fin)
open import Data.Bool.Properties using (∨-comm; ∧-comm; ∨-assoc)
open import Data.List using (List; []; _∷_; _++_; map; concat; filterᵇ; partitionᵇ)
open import Data.List.Properties using (++-assoc)
import Data.List.Relation.Binary.Permutation.Homogeneous as H
import Data.List.Relation.Binary.Permutation.Propositional as ↭
open ↭ using (_↭_; ↭-refl; ↭-sym; ↭-trans; ↭-reflexive)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties using (map⁺; ++⁺; ++-comm)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_)
  renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans; cong to ≡-cong; cong₂ to ≡-cong₂)
open import signature using (Signature)
open import primitives using (Primitives)
import matrix
import two

-- Groundwork for the maintenance theorem: the moves preserve the invariant that each hidden pair
-- is a region of the hidden set with its summary. Here: summaries are stable under permutation of
-- the region.
module language-operational.maintenance {ℓ} (Sig : Signature ℓ) (𝒫 : Primitives two.semiring Sig) where

open Signature Sig
open Primitives 𝒫
open import language-syntax Sig renaming (_,_ to _▸_)
open import language-operational.evaluation Sig 𝒫
open import language-operational.path Sig 𝒫
open import language-operational.graph Sig 𝒫
open import language-operational.hide Sig 𝒫
open import language-operational.topological-order Sig 𝒫

private
  module M = matrix.Mat two.semiring

private
  ∨-swap : ∀ a b c → (a ∨ (b ∨ c)) ≡ (b ∨ (a ∨ c))
  ∨-swap Bool.false b c = ≡-refl
  ∨-swap Bool.true Bool.false c = ≡-refl
  ∨-swap Bool.true Bool.true c = ≡-refl

  any-perm : ∀ {a} {A : Set a} (f : A → Bool) {rs rs' : List A} →
             rs ↭ rs' → any f rs ≡ any f rs'
  any-perm f ↭.refl = ≡-refl
  any-perm f (↭.prep r p) = ≡-cong (f r ∨_) (any-perm f p)
  any-perm f (↭.swap a b p) =
    ≡-trans (≡-cong (λ z → f a ∨ (f b ∨ z)) (any-perm f p)) (∨-swap (f a) (f b) _)
  any-perm f (↭.trans p q) = ≡-trans (any-perm f p) (any-perm f q)

member-perm : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]}
              (q : Path D) {C C' : List (Path D)} → C ↭ C' → member q C ≡ member q C'
member-perm q = any-perm (eq-path q)

member-vertex-perm : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]}
                     (x : Vertex D) {C C' : List (Path D)} → C ↭ C' →
                     member-vertex x C ≡ member-vertex x C'
member-vertex-perm env    p = ≡-refl
member-vertex-perm (at q) p = member-perm q p

-- Restriction reads the region only through membership, so respects permutation.
restrict-perm : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]}
                (G : Graph D) {C C' : List (Path D)} → C ↭ C' →
                ∀ x y (i : Fin (vertex-width y)) (j : Fin (vertex-width x)) →
                restrict G C x y i j ≡ restrict G C' x y i j
restrict-perm G p x y i j =
  ≡-cong (λ b → when b (G x y) i j)
         (≡-cong₂ _∨_ (member-vertex-perm x p) (member-vertex-perm y p))

-- Restriction only zeroes entries, so preserves the forward-edge property.
restrict-forward : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]}
                   {G : Graph D} (C : List (Path D)) → Forward G → Forward (restrict G C)
restrict-forward C fwd x y i j with member-vertex x C ∨ member-vertex y C
... | Bool.true  = fwd x y i j
... | Bool.false = λ ()

-- Summaries are stable under permutation of the region: restriction is membership-based, and the
-- hiding order is immaterial on the restricted graph, which is forward.
summary-perm : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} (D : γ , t ⇓ v [ R ])
               {C C' : List (Path D)} → C ↭ C' →
               ∀ x y (i : Fin (vertex-width y)) (j : Fin (vertex-width x)) →
               summary D C x y i j ≡ summary D C' x y i j
summary-perm D {C} {C'} p x y i j =
  ≡-trans (hide-all-cong (map at C) (restrict-perm (fo-graph D) p) x y i j)
          (hide-all-perm (restrict-forward C' (fo-forward D)) (map⁺ at p) x y i j)

-- Region lists that agree up to reordering of the regions and of the members within each.
_≈ᵣ_ : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]} →
       List (List (Path D)) → List (List (Path D)) → Set ℓ
_≈ᵣ_ = H.Permutation _↭_

private
  ++-swap : ∀ {a} {A : Set a} (xs ys zs : List A) → xs ++ (ys ++ zs) ↭ ys ++ (xs ++ zs)
  ++-swap xs ys zs =
    ↭-trans (↭-reflexive (≡-sym (++-assoc xs ys zs)))
            (↭-trans (++⁺ (++-comm xs ys) ↭-refl) (↭-reflexive (++-assoc ys xs zs)))

  concat-resp : ∀ {a} {A : Set a} {rss rss' : List (List A)} →
                H.Permutation _↭_ rss rss' → concat rss ↭ concat rss'
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

-- The congruence step of the regions computation: equivalent prior regions give equivalent
-- regions after a vertex is added, since adjacency of the vertex reads regions only through
-- membership and the merged members only through concatenation.
regions-prep : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]}
               (G : Graph D) (w : Path D) {ws ws' : List (Path D)} →
               regions G ws ≈ᵣ regions G ws' →
               regions G (w ∷ ws) ≈ᵣ regions G (w ∷ ws')
regions-prep G w ih =
  H.prep (↭.prep w (concat-resp (proj₁ tp))) (proj₂ tp)
  where tp = partition-resp (any (λ q → adjacent G (at w) (at q)))
                            (any-perm (λ q → adjacent G (at w) (at q)))
                            ih

private
  pw-refl : ∀ {a} {A : Set a} (xss : List (List A)) → Pointwise _↭_ xss xss
  pw-refl []         = []
  pw-refl (xs ∷ xss) = ↭-refl ∷ pw-refl xss

  perm-of-≡ : ∀ {a} {A : Set a} {xss yss : List (List A)} →
              xss ≡ yss → H.Permutation _↭_ xss yss
  perm-of-≡ ≡-refl = H.refl (pw-refl _)

  ∨-false : ∀ x y → (x ∨ y) ≡ Bool.false → (x ≡ Bool.false) × (y ≡ Bool.false)
  ∨-false Bool.false y h = ≡-refl , h

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

-- Adding two vertices to a region list in either order gives equivalent regions. Both orders
-- merge exactly when the vertices are adjacent or some region is adjacent to both; in that case
-- the merged region collects the regions adjacent to either vertex, and otherwise the two new
-- regions absorb disjoint groups.
private
  module Step {a} (A : Set a) (adjA adjB : A → Bool) (aElt bElt : A)
              (sym-ab : adjA bElt ≡ adjB aElt) where
    fA fB : List A → Bool
    fA = any adjA
    fB = any adjB

    stepA stepB stepA' stepB' : List (List A) → List (List A)
    stepA  R = (aElt ∷ concat (proj₁ (partitionᵇ fA R))) ∷ proj₂ (partitionᵇ fA R)
    stepB  R = (bElt ∷ concat (proj₁ (partitionᵇ fB R))) ∷ proj₂ (partitionᵇ fB R)
    stepA' R = (aElt ∷ concat (filterᵇ fA R)) ∷ filterᵇ (λ C → Bool.not (fA C)) R
    stepB' R = (bElt ∷ concat (filterᵇ fB R)) ∷ filterᵇ (λ C → Bool.not (fB C)) R

    stepA≡ : ∀ R → stepA R ≡ stepA' R
    stepA≡ R = ≡-cong₂ _∷_ (≡-cong (λ z → aElt ∷ concat z) (part₁-filter fA R)) (part₂-filter fA R)

    stepB≡ : ∀ R → stepB R ≡ stepB' R
    stepB≡ R = ≡-cong₂ _∷_ (≡-cong (λ z → bElt ∷ concat z) (part₁-filter fB R)) (part₂-filter fB R)

    -- The merge test is symmetric: either vertex merges with the other's region exactly when they
    -- are adjacent or some prior region is adjacent to both.
    β-sym : ∀ R → fA (bElt ∷ concat (filterᵇ fB R)) ≡ fB (aElt ∷ concat (filterᵇ fA R))
    β-sym R =
      ≡-cong₂ _∨_ sym-ab
        (≡-trans (any-concat adjA (filterᵇ fB R))
        (≡-trans (any-filter fB fA R)
        (≡-trans (any-cong (λ C → ∧-comm (fB C) (fA C)) R)
                 (≡-sym (≡-trans (any-concat adjB (filterᵇ fA R)) (any-filter fA fB R))))))

    tails : ∀ R → filterᵇ (λ C → Bool.not (fA C)) (filterᵇ (λ C → Bool.not (fB C)) R)
                ≡ filterᵇ (λ C → Bool.not (fB C)) (filterᵇ (λ C → Bool.not (fA C)) R)
    tails R =
      ≡-trans (filter-filter (λ C → Bool.not (fB C)) (λ C → Bool.not (fA C)) R)
      (≡-trans (filter-cong (λ C → ∧-comm (Bool.not (fB C)) (Bool.not (fA C))) R)
               (≡-sym (filter-filter (λ C → Bool.not (fA C)) (λ C → Bool.not (fB C)) R)))

    step-comm' : ∀ R → H.Permutation _↭_ (stepA' (stepB' R)) (stepB' (stepA' R))
    step-comm' R with fA (bElt ∷ concat (filterᵇ fB R)) in eqA
                    | fB (aElt ∷ concat (filterᵇ fA R)) in eqB
    ... | Bool.true  | Bool.true  =
      H.prep (↭.swap aElt bElt
               (↭-trans (concat-select fB fA R)
                (↭-trans (↭-reflexive (≡-cong concat (filter-cong (λ C → ∨-comm (fB C) (fA C)) R)))
                         (↭-sym (concat-select fA fB R)))))
             (perm-of-≡ (tails R))
    ... | Bool.true  | Bool.false with ≡-trans (≡-sym eqA) (≡-trans (β-sym R) eqB)
    ...   | ()
    step-comm' R | Bool.false | Bool.true with ≡-trans (≡-sym eqB) (≡-trans (≡-sym (β-sym R)) eqA)
    ...   | ()
    step-comm' R | Bool.false | Bool.false =
      H.swap (↭-reflexive (≡-cong (λ z → aElt ∷ concat z) absorbA))
             (↭-reflexive (≡-cong (λ z → bElt ∷ concat z) (≡-sym absorbB)))
             (perm-of-≡ (tails R))
      where
        hAB : any (λ C → fB C Bool.∧ fA C) R ≡ Bool.false
        hAB = ≡-trans (≡-sym (≡-trans (any-concat adjA (filterᵇ fB R)) (any-filter fB fA R)))
                      (proj₂ (∨-false (adjA bElt) _ eqA))

        absorbA : filterᵇ fA (filterᵇ (λ C → Bool.not (fB C)) R) ≡ filterᵇ fA R
        absorbA = filter-absorb fB fA R hAB

        absorbB : filterᵇ fB (filterᵇ (λ C → Bool.not (fA C)) R) ≡ filterᵇ fB R
        absorbB = filter-absorb fA fB R (≡-trans (any-cong (λ C → ∧-comm (fA C) (fB C)) R) hAB)

    step-comm : ∀ R → H.Permutation _↭_ (stepA (stepB R)) (stepB (stepA R))
    step-comm R =
      H.trans (perm-of-≡ (≡-trans (≡-cong stepA (stepB≡ R)) (stepA≡ (stepB' R))))
      (H.trans (step-comm' R)
               (perm-of-≡ (≡-sym (≡-trans (≡-cong stepB (stepA≡ R)) (stepB≡ (stepA' R))))))

adjacent-sym : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]}
               (G : Graph D) (x y : Vertex D) → adjacent G x y ≡ adjacent G y x
adjacent-sym G x y = ∨-comm (nonzero (G x y)) (nonzero (G y x))

-- Adding two vertices in either order gives equivalent regions.
regions-swap : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]}
               (G : Graph D) (a b : Path D) (ws : List (Path D)) →
               regions G (a ∷ b ∷ ws) ≈ᵣ regions G (b ∷ a ∷ ws)
regions-swap G a b ws =
  Step.step-comm _ (λ q → adjacent G (at a) (at q)) (λ q → adjacent G (at b) (at q))
                 a b (adjacent-sym G (at a) (at b)) (regions G ws)

-- Order-independence of the regions computation.
regions-perm : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]}
               (G : Graph D) {ws ws' : List (Path D)} → ws ↭ ws' →
               regions G ws ≈ᵣ regions G ws'
regions-perm G ↭.refl       = H.refl (pw-refl _)
regions-perm G (↭.prep w p) = regions-prep G w (regions-perm G p)
regions-perm G (↭.swap {xs = ws} {ys = ws'} a b p) =
  H.trans (regions-swap G a b ws)
          (regions-prep G b {a ∷ ws} {a ∷ ws'} (regions-prep G a {ws} {ws'} (regions-perm G p)))
regions-perm G (↭.trans p q) = H.trans (regions-perm G p) (regions-perm G q)
