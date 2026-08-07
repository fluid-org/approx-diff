{-# OPTIONS --prop --postfix-projections --safe #-}

open import Data.Bool using (true; false)
open import Data.Fin using (Fin; splitAt; toℕ)
open import Data.Nat using (ℕ; zero; suc; _+_; _≡ᵇ_)
open import Data.Nat.Properties using (+-assoc; +-identityʳ)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.List using (List; []; _∷_; _++_; length; map; concatMap; allFin)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import signature using (Signature)
open import primitives using (Primitives)
import matrix
import two

-- Dependence graphs over intermediates, and dependences over them, as explicit adjacency lists: a
-- dependence carries one edge relation per earlier vertex, so the graph is read off directly rather than
-- decoded from a block matrix.
module language-operational.dependence-graph
  {ℓ} (Sig : Signature ℓ) (𝒫 : Primitives two.semiring Sig) where

open import language-syntax Sig renaming (_,_ to _▸_)
open import language-operational.evaluation Sig 𝒫 using (Val; width; width-env)

private
  module M = matrix.Mat two.semiring

open import categories using (Category; HasProducts)
open import cmon-enriched using ()

private
  products : HasProducts M.cat
  products = cmon-enriched.biproducts→products M.cmon M.biproduct

open HasProducts products using () renaming (pair to ⟨_,_⟩)

-- Cast a matrix along an equality of its domain (column) width.
ccast : ∀ {t m n} → m ≡ n → M.Matrix t m → M.Matrix t n
ccast refl A = A

------------------------------------------------------------------------
-- Graphs and dependences.

mutual
  data Graph (g : ℕ) : Set ℓ where
    ∅    : Graph g
    snoc : (G : Graph g) {τ : type 0} (v : Val τ) → Dep g G (width v) → Graph g

  -- A dependence over G with codomain n: an environment relation and one edge relation per vertex,
  -- oldest first. ⟨ R₀ ∣⟩ is (R₀ ∣ ε); D ∣ R′ appends the edge R′ into the newest vertex.
  data Dep (g : ℕ) : Graph g → ℕ → Set ℓ where
    ⟨_∣⟩ : ∀ {n} → M.Matrix n g → Dep g ∅ n
    _∣_  : ∀ {G n τ} {v : Val τ} {S : Dep g G (width v)} →
           Dep g G n → M.Matrix n (width v) → Dep g (snoc G v S) n

infixl 30 _∣_

-- Total width of a graph's vertices.
gwidth : ∀ {g} → Graph g → ℕ
gwidth ∅            = 0
gwidth (snoc G v _) = gwidth G + width v

dcast : ∀ {g} {G : Graph g} {m n} → m ≡ n → Dep g G m → Dep g G n
dcast refl D = D

------------------------------------------------------------------------
-- Basic operations, mirroring the paper.

-- Post-compose the codomain of every relation.
mapCod : ∀ {g G m n} → M.Matrix n m → Dep g G m → Dep g G n
mapCod f ⟨ R₀ ∣⟩ = ⟨ f M.∘ R₀ ∣⟩
mapCod f (D ∣ R′) = mapCod f D ∣ (f M.∘ R′)

-- The dependence with environment relation A and no edges: (A ∣ 0, …, 0).
constDep : ∀ {g n} (G : Graph g) → M.Matrix n g → Dep g G n
constDep ∅            A = ⟨ A ∣⟩
constDep (snoc G v _) A = constDep G A ∣ M.εₘ

-- Pointwise pairing of two dependences over the same graph: codomains sum.
pairDep : ∀ {g G m n} → Dep g G m → Dep g G n → Dep g G (m + n)
pairDep ⟨ A ∣⟩   ⟨ B ∣⟩   = ⟨ ⟨ A , B ⟩ ∣⟩
pairDep (D ∣ R) (E ∣ S)  = pairDep D E ∣ ⟨ R , S ⟩

-- Pointwise union of two dependences over the same graph.
addDep : ∀ {g G n} → Dep g G n → Dep g G n → Dep g G n
addDep ⟨ A ∣⟩   ⟨ B ∣⟩   = ⟨ A M.+ₘ B ∣⟩
addDep (D ∣ R) (E ∣ S)  = addDep D E ∣ (R M.+ₘ S)

mutual
  _++G_ : ∀ {g} → Graph g → Graph g → Graph g
  G ++G ∅          = G
  G ++G snoc H v S = snoc (G ++G H) v (inject G S)

  inject : ∀ {g} (G : Graph g) {H : Graph g} {n} → Dep g H n → Dep g (G ++G H) n
  inject G ⟨ R₀ ∣⟩  = constDep G R₀
  inject G (S ∣ Rk) = inject G S ∣ Rk

infixl 25 _++G_

_⊗_ : ∀ {g} {G H : Graph g} {m n} → Dep g G m → Dep g H n → Dep g (G ++G H) (m + n)
_⊗_ {G = G} R ⟨ S₀ ∣⟩ = pairDep R (constDep G S₀)
R ⊗ (S ∣ Sk)          = (R ⊗ S) ∣ ⟨ M.εₘ , Sk ⟩

infixl 26 _⊗_

------------------------------------------------------------------------
-- Graph extension, for widening a dependence as the graph grows.

data _⊒_ {g} : Graph g → Graph g → Set ℓ where
  done : ∀ {G} → G ⊒ G
  more : ∀ {G G′ τ} {v : Val τ} {S : Dep g G′ (width v)} → G′ ⊒ G → snoc G′ v S ⊒ G

⊒-trans : ∀ {g} {G G′ G″ : Graph g} → G″ ⊒ G′ → G′ ⊒ G → G″ ⊒ G
⊒-trans done      e = e
⊒-trans (more e′) e = more (⊒-trans e′ e)

-- Extend a dependence over G to one over any G′ ⊒ G, with zero edges to the new vertices.
widen : ∀ {g} {G G′ : Graph g} {n} → G′ ⊒ G → Dep g G n → Dep g G′ n
widen done     D = D
widen (more e) D = widen e D ∣ M.εₘ

------------------------------------------------------------------------
-- Collapse: eliminate the vertices, composing each dependence through the vertex it points into.

collapse : ∀ {g G n} → Dep g G n → M.Matrix n g
collapse ⟨ R₀ ∣⟩            = R₀
collapse (_∣_ {S = S} D R′) = collapse (addDep D (mapCod R′ S))

------------------------------------------------------------------------
-- Substitution: reroute a dependence computed under environment g′ through a frame E, whose codomain is
-- g′, and rebase its graph onto the ambient graph Φ.

mutual
  substGraph : ∀ {g} {Φ : Graph g} {g′} (E : Dep g Φ g′) (Ψ : Graph g′) →
               Σ (Graph g) λ Φ′ → Φ′ ⊒ Φ
  substGraph {Φ = Φ} E ∅ = Φ , done
  substGraph E (snoc Ψ w Sw) =
    let Φ′ , e = substGraph E Ψ in snoc Φ′ w (substDep E Sw) , more e

  substDep : ∀ {g} {Φ : Graph g} {g′} (E : Dep g Φ g′) {Ψ : Graph g′} {m} →
             Dep g′ Ψ m → Dep g (proj₁ (substGraph E Ψ)) m
  substDep E ⟨ S₀ ∣⟩ = mapCod S₀ E
  substDep E (S ∣ Rn) = substDep E S ∣ Rn

------------------------------------------------------------------------
-- Reading off the graph: values, edges, and edge labels.

-- Boolean matrix as its list of set entries.
ents : ∀ {m n} → M.Matrix m n → List (ℕ × ℕ)
ents {m} {n} A = concatMap (λ i → concatMap (λ j → keep i j (A i j)) (allFin n)) (allFin m)
  where
    keep : Fin m → Fin n → two.Two → List (ℕ × ℕ)
    keep i j two.I = (toℕ i , toℕ j) ∷ []
    keep _ _ two.O = []

-- The values of the intermediates, oldest first.
seq-vals : ∀ {g} → Graph g → List (Σ (type 0) Val)
seq-vals ∅            = []
seq-vals (snoc G {τ} v _) = seq-vals G ++ (τ , v) ∷ []

-- Edges of one vertex's dependence: (source index, entries), oldest source first.
private
  dep-blocks : ∀ {g G n} → Dep g G n → List (ℕ × List (ℕ × ℕ))
  dep-blocks ⟨ _ ∣⟩ = []
  dep-blocks (D ∣ R′) =
    let es = dep-blocks D in es ++ (length es , map (λ e → proj₂ e , proj₁ e) (ents R′)) ∷ []

  -- Per-vertex edge lists of a graph, newest vertex last, tagged with the vertex index.
  graph-blocks : ∀ {g} → Graph g → List (ℕ × List (ℕ × List (ℕ × ℕ)))
  graph-blocks ∅ = []
  graph-blocks (snoc G _ S) = let bs = graph-blocks G in bs ++ (length bs , dep-blocks S) ∷ []

-- An edge i → j when vertex j's block at source i is non-empty.
dep-edges : ∀ {g} → Graph g → List (ℕ × ℕ)
dep-edges G = concatMap vertex-edges (graph-blocks G)
  where
    nonempty : List (ℕ × ℕ) → List (ℕ × ℕ) → List (ℕ × ℕ)
    nonempty [] _ = []
    nonempty (_ ∷ _) e = e

    vertex-edges : ℕ × List (ℕ × List (ℕ × ℕ)) → List (ℕ × ℕ)
    vertex-edges (j , bs) = concatMap (λ p → nonempty (proj₂ p) ((proj₁ p , j) ∷ [])) bs

-- The relation carried by the edge i → j: pairs (p , q) with position p of vertex i related to q of j.
edge-rel : ∀ {g} → Graph g → ℕ → ℕ → List (ℕ × ℕ)
edge-rel G i j = concatMap (vertex-block) (graph-blocks G)
  where
    at-source : ℕ × List (ℕ × ℕ) → List (ℕ × ℕ)
    at-source (i′ , es) with i′ ≡ᵇ i
    ... | true = es
    ... | false = []

    vertex-block : ℕ × List (ℕ × List (ℕ × ℕ)) → List (ℕ × ℕ)
    vertex-block (j′ , bs) with j′ ≡ᵇ j
    ... | true = concatMap at-source bs
    ... | false = []
