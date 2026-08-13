{-# OPTIONS --prop --postfix-projections --safe #-}

open import Data.Fin as Fin using (Fin)
open import Data.List using (List; []; _∷_; foldl)
open import Data.List.Relation.Unary.All using (All; []; _∷_) renaming (map to All-map)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_)
  renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans; cong to ≡-cong; cong₂ to ≡-cong₂)
import matrix
import two

-- Hiding as join algebra, generic in the vertex set: entrywise laws for hide-all on graphs that
-- agree on the hidden rows and columns. No rank or forwardness is assumed.
module interaction.hide-algebra where

private
  module M = matrix.Mat two.semiring

open two using (Two; O; I; _⊔_; ⊔-idem; ⊔-comm; ⊔-runit; ⊔-assoc)

module Hide {ℓ} (V : Set ℓ) (w : V → ℕ) where
  Gr : Set ℓ
  Gr = (x y : V) → M.Matrix (w y) (w x)

  h : Gr → V → Gr
  h G r x y = G x y M.+ₘ (G r y M.∘ G x r)

  _≈g_ : Gr → Gr → Set ℓ
  G ≈g G' = ∀ x y (i : Fin (w y)) (j : Fin (w x)) → G x y i j ≡ G' x y i j

  private
    ⊔-absorbˡ : ∀ a b → (a ⊔ (a ⊔ b)) ≡ (a ⊔ b)
    ⊔-absorbˡ O b = ≡-refl
    ⊔-absorbˡ I b = ≡-refl

    ⊔-absorbʳ : ∀ a b → (a ⊔ (b ⊔ a)) ≡ (b ⊔ a)
    ⊔-absorbʳ O b = ≡-refl
    ⊔-absorbʳ I O = ≡-refl
    ⊔-absorbʳ I I = ≡-refl

    absorb-mono : ∀ x y z → x ≡ (y ⊔ x) → (z ⊔ y) ≡ y → x ≡ (z ⊔ x)
    absorb-mono x y O p q = ≡-refl
    absorb-mono x O I p ()
    absorb-mono x I I p ≡-refl = p

    ⊔-shift : ∀ a s c → ((a ⊔ s) ⊔ c) ≡ ((a ⊔ c) ⊔ s)
    ⊔-shift O s c = ⊔-comm s c
    ⊔-shift I s c = ≡-refl

    ⊔-insert : ∀ a b c → (a ⊔ b) ≡ b → (b ⊔ c) ≡ (b ⊔ (a ⊔ c))
    ⊔-insert O b c q = ≡-refl
    ⊔-insert I O c ()
    ⊔-insert I I c ≡-refl = ≡-refl

  private
    Σ-O : ∀ {n} (f : Fin n → Two) → (∀ k → f k ≡ O) → M.Σ f ≡ O
    Σ-O {zero}  f z = ≡-refl
    Σ-O {suc n} f z =
      ≡-cong₂ _⊔_ (z Fin.zero) (Σ-O (λ k → f (Fin.suc k)) (λ k → z (Fin.suc k)))

    ⊓-O : ∀ x → (x two.⊓ O) ≡ O
    ⊓-O O = ≡-refl
    ⊓-O I = ≡-refl

  -- Zero rows and columns persist under hiding: every new entry into the row or column of r₀
  -- factors through an entry of that row or column.
  zero-fold : ∀ {G : Gr} rs r₀ →
              (((z : V) (i : Fin (w z)) (j : Fin (w r₀)) → G r₀ z i j ≡ O) ×
               ((z : V) (i : Fin (w r₀)) (j : Fin (w z)) → G z r₀ i j ≡ O)) →
              (((z : V) (i : Fin (w z)) (j : Fin (w r₀)) → foldl h G rs r₀ z i j ≡ O) ×
               ((z : V) (i : Fin (w r₀)) (j : Fin (w z)) → foldl h G rs z r₀ i j ≡ O))
  zero-fold []           r₀ zz        = zz
  zero-fold {G} (r ∷ rs) r₀ (zr , zc) = zero-fold {h G r} rs r₀ (zr' , zc')
    where
    zr' : (z : V) (i : Fin (w z)) (j : Fin (w r₀)) → h G r r₀ z i j ≡ O
    zr' z i j =
      ≡-cong₂ _⊔_ (zr z i j)
        (Σ-O (λ k → G r z i k two.⊓ G r₀ r k j)
             (λ k → ≡-trans (≡-cong (G r z i k two.⊓_) (zr r k j)) (⊓-O (G r z i k))))

    zc' : (z : V) (i : Fin (w r₀)) (j : Fin (w z)) → h G r z r₀ i j ≡ O
    zc' z i j =
      ≡-cong₂ _⊔_ (zc z i j)
        (Σ-O (λ k → G r r₀ i k two.⊓ G z r k j)
             (λ k → ≡-cong (two._⊓ G z r k j) (zc r i k)))

  -- Hiding only adds entries.
  increasing : ∀ {G : Gr} rs x y (i : Fin (w y)) (j : Fin (w x)) →
               foldl h G rs x y i j ≡ (G x y i j ⊔ foldl h G rs x y i j)
  increasing []           x y i j = ≡-sym ⊔-idem
  increasing {G} (r ∷ rs) x y i j =
    absorb-mono (foldl h (h G r) rs x y i j) (h G r x y i j) (G x y i j)
                (increasing rs x y i j)
                (⊔-absorbˡ (G x y i j) ((G r y M.∘ G x r) i j))

  h-cong : ∀ {G G'} r → G ≈g G' → h G r ≈g h G' r
  h-cong r p x y i j =
    ≡-cong₂ _⊔_ (p x y i j) (M.Σ-cong-≡ (λ k → ≡-cong₂ two._⊓_ (p r y i k) (p x r k j)))

  fold-cong : ∀ {G G'} rs → G ≈g G' → foldl h G rs ≈g foldl h G' rs
  fold-cong []       p = p
  fold-cong (r ∷ rs) p = fold-cong rs (h-cong r p)

  -- A summand with no entries at the hidden vertices passes through hiding them: every new
  -- composite routes through a hidden row and column, which the summand lacks.
  add-inert : ∀ {G S : Gr} rs →
              All (λ r → ((z : V) (i : Fin (w z)) (j : Fin (w r)) → S r z i j ≡ O)
                       × ((z : V) (i : Fin (w r)) (j : Fin (w z)) → S z r i j ≡ O)) rs →
              ∀ x y (i : Fin (w y)) (j : Fin (w x)) →
              foldl h (λ x' y' → G x' y' M.+ₘ S x' y') rs x y i j ≡
              (foldl h G rs x y i j ⊔ S x y i j)
  add-inert []               []               x y i j = ≡-refl
  add-inert {G} {S} (r ∷ rs) ((zr , zc) ∷ zs) x y i j =
    ≡-trans (fold-cong rs step x y i j) (add-inert {h G r} {S} rs zs x y i j)
    where
    step : h (λ x' y' → G x' y' M.+ₘ S x' y') r ≈g (λ x' y' → h G r x' y' M.+ₘ S x' y')
    step x' y' i' j' =
      ≡-trans
        (≡-cong ((G x' y' i' j' ⊔ S x' y' i' j') ⊔_)
          (M.Σ-cong-≡ (λ k → ≡-cong₂ two._⊓_
            (≡-trans (≡-cong (G r y' i' k ⊔_) (zr y' i' k)) (⊔-runit {G r y' i' k}))
            (≡-trans (≡-cong (G x' r k j' ⊔_) (zc x' k j')) (⊔-runit {G x' r k j'})))))
        (⊔-shift (G x' y' i' j') (S x' y' i' j') ((G r y' M.∘ G x' r) i' j'))

  -- Hiding vertices at which a larger graph agrees with a smaller one adds only its extra
  -- entries: every new composite routes through agreed rows and columns, so already arises in
  -- the smaller graph.
  agree-add : ∀ {G G' : Gr} rs →
              (∀ x y (i : Fin (w y)) (j : Fin (w x)) → (G x y i j ⊔ G' x y i j) ≡ G' x y i j) →
              All (λ r → ((z : V) (i : Fin (w z)) (j : Fin (w r)) → G' r z i j ≡ G r z i j)
                       × ((z : V) (i : Fin (w r)) (j : Fin (w z)) → G' z r i j ≡ G z r i j)) rs →
              ∀ x y (i : Fin (w y)) (j : Fin (w x)) →
              foldl h G' rs x y i j ≡ (G' x y i j ⊔ foldl h G rs x y i j)
  agree-add {G} {G'} []       sub _              x y i j =
    ≡-sym (≡-trans (⊔-comm (G' x y i j) (G x y i j)) (sub x y i j))
  agree-add {G} {G'} (r ∷ rs) sub ((ar , ac) ∷ as) x y i j =
    ≡-trans (agree-add {h G r} {h G' r} rs sub' all' x y i j)
    (≡-trans (≡-cong (_⊔ foldl h (h G r) rs x y i j) (step x y i j))
    (≡-trans (⊔-assoc (G' x y i j) (h G r x y i j) (foldl h (h G r) rs x y i j))
             (≡-cong (G' x y i j ⊔_) (≡-sym (increasing rs x y i j)))))
    where
    step : ∀ x' y' (i' : Fin (w y')) (j' : Fin (w x')) →
           h G' r x' y' i' j' ≡ (G' x' y' i' j' ⊔ h G r x' y' i' j')
    step x' y' i' j' =
      ≡-trans
        (≡-cong (G' x' y' i' j' ⊔_)
          (M.Σ-cong-≡ (λ k → ≡-cong₂ two._⊓_ (ar y' i' k) (ac x' k j'))))
        (⊔-insert (G x' y' i' j') (G' x' y' i' j') ((G r y' M.∘ G x' r) i' j')
                  (sub x' y' i' j'))

    sub' : ∀ x' y' (i' : Fin (w y')) (j' : Fin (w x')) →
           (h G r x' y' i' j' ⊔ h G' r x' y' i' j') ≡ h G' r x' y' i' j'
    sub' x' y' i' j' =
      ≡-trans (≡-cong (h G r x' y' i' j' ⊔_) (step x' y' i' j'))
      (≡-trans (⊔-absorbʳ (h G r x' y' i' j') (G' x' y' i' j')) (≡-sym (step x' y' i' j')))

    all' : All (λ r' → ((z : V) (i' : Fin (w z)) (j' : Fin (w r')) →
                        h G' r r' z i' j' ≡ h G r r' z i' j')
                     × ((z : V) (i' : Fin (w r')) (j' : Fin (w z)) →
                        h G' r z r' i' j' ≡ h G r z r' i' j')) rs
    all' = All-map
      (λ {r'} (ar' , ac') →
        (λ z i' j' → ≡-trans (step r' z i' j')
                     (≡-trans (≡-cong (_⊔ h G r r' z i' j') (ar' z i' j'))
                              (⊔-absorbˡ (G r' z i' j') ((G r z M.∘ G r' r) i' j')))) ,
        (λ z i' j' → ≡-trans (step z r' i' j')
                     (≡-trans (≡-cong (_⊔ h G r z r' i' j') (ac' z i' j'))
                              (⊔-absorbˡ (G z r' i' j') ((G r r' M.∘ G z r) i' j')))))
      as
