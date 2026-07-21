{-# OPTIONS --prop --postfix-projections --safe #-}

import Level
open import Data.Fin using (Fin; splitAt; toℕ; _↑ˡ_; _↑ʳ_)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _<ᵇ_; _≡ᵇ_)
open import Data.Bool using () renaming (if_then_else_ to ifᵇ_then_else_)
open import Data.Nat.Properties using (+-assoc; +-identityʳ)
open import Relation.Binary.PropositionalEquality using (trans; cong)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Maybe using (Maybe; just; nothing)
import Data.List
open import Data.List using (List; []; _∷_; _++_; length; concatMap; allFin)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import prop-setoid using (Setoid)
open import commutative-semiring using (CommutativeSemiring)
open import every using (Every; []; _∷_)
open import signature using (Signature)
open import primitives using (Primitives)
import matrix
import two

-- Instrumentation of evaluation derivations: a marking of the derivation selects the nodes whose values
-- become intermediates.
module language-operational.instrument
  {ℓ} (Sig : Signature ℓ) (𝒫 : Primitives two.semiring Sig) where

open Signature Sig
open Primitives 𝒫
open prop-setoid._⇒_ using (func)
open import language-syntax Sig renaming (_,_ to _▸_)
open import language-operational.evaluation Sig 𝒫
open import type-substitution Sig using (unfold₁; unfold₁-inst)

private
  module CS = CommutativeSemiring two.semiring
  module M = matrix.Mat two.semiring

open import categories using (Category; HasProducts)
open Category M.cat using (_∘_)
open HasProducts products using (p₁; p₂)

------------------------------------------------------------------------
-- Matrix plumbing over concatenated domains.

-- Zero-pad a matrix over g to g + e.
pad : ∀ {t} (g e : ℕ) → M.Matrix t g → M.Matrix t (g + e)
pad g e A i j with splitAt g j
... | inj₁ a = A i a
... | inj₂ _ = CS.ε

-- Zero-pad a matrix over g + p to g + (p + k).
widen : ∀ {t} (g p k : ℕ) → M.Matrix t (g + p) → M.Matrix t (g + (p + k))
widen g p k A i j with splitAt g j
... | inj₁ a = A i (a ↑ˡ p)
... | inj₂ b with splitAt p b
...   | inj₁ c = A i (g ↑ʳ c)
...   | inj₂ _ = CS.ε

-- Stack two matrices with a common domain.
stack : ∀ {c} (a b : ℕ) → M.Matrix a c → M.Matrix b c → M.Matrix (a + b) c
stack a b A B i j with splitAt a i
... | inj₁ x = A x j
... | inj₂ y = B y j

-- Injection of the final w columns of g + (n + w).
inj-last : ∀ (g n w : ℕ) → M.Matrix w (g + (n + w))
inj-last g n w i j with splitAt g j
... | inj₁ _ = CS.ε
... | inj₂ b with splitAt n b
...   | inj₁ _ = CS.ε
...   | inj₂ c = M.I i c

-- Substitute a frame E for the environment block, passing the k newest intermediates through: the block
-- matrix [E 0; 0 I].
frame-emb : ∀ {g'} (g p k : ℕ) → M.Matrix g' (g + p) → M.Matrix (g' + k) (g + (p + k))
frame-emb {g'} g p k E = stack g' k (widen g p k E) (inj-last g p k)

-- The identity frame, for premises under the same environment.
id-frame : ∀ (g p : ℕ) → M.Matrix g (g + p)
id-frame g p = pad g p M.I

------------------------------------------------------------------------
-- Sequences of intermediates.

data Seq (g : ℕ) : ℕ → Set ℓ where
  ∅    : Seq g 0
  snoc : ∀ {n} (Φ : Seq g n) {τ : type 0} (w : Val τ) (Sm : M.Matrix (width w) (g + n)) →
         Seq g (n + width w)

-- The values of the intermediates, oldest first.
seq-vals : ∀ {g n} → Seq g n → List (Σ (type 0) Val)
seq-vals ∅             = []
seq-vals (snoc Φ {τ} w _) = seq-vals Φ ++ (τ , w) ∷ []

------------------------------------------------------------------------
-- Collapse: eliminate the intermediates from the domain, most recent first.

elim-mat : ∀ (g n w : ℕ) → M.Matrix w (g + n) → M.Matrix (g + (n + w)) (g + n)
elim-mat g n w Sm r c with splitAt g r
... | inj₁ a = M.I (a ↑ˡ n) c
... | inj₂ b with splitAt n b
...   | inj₁ d = M.I (g ↑ʳ d) c
...   | inj₂ x = Sm x c

collapse : ∀ {g n t} → Seq g n → M.Matrix t (g + n) → M.Matrix t g
collapse {g} ∅ A i j = A i (j ↑ˡ 0)
collapse {g} (snoc {n} Φ w Sm) A = collapse Φ (A M.∘ elim-mat g n (width w) Sm)

------------------------------------------------------------------------
-- Boolean matrices as entry lists, comparable by refl.

ents : ∀ {m n} → M.Matrix m n → List (ℕ × ℕ)
ents {m} {n} A =
  concatMap (λ i → concatMap (λ j → keep i j (A i j)) (allFin n)) (allFin m)
  where
    keep : ∀ {m n} → Fin m → Fin n → two.Two → List (ℕ × ℕ)
    keep i j two.I = (toℕ i , toℕ j) ∷ []
    keep i j two.O = []

------------------------------------------------------------------------
-- The dependence graph over the intermediates.

private
  -- Index of the entry containing an intermediate position, given the widths of the entries.
  locate : List ℕ → ℕ → ℕ
  locate []       _ = 0
  locate (w ∷ ws) p = ifᵇ p <ᵇ w then 0 else suc (locate ws (p ∸ w))

  entry-ents : ∀ {g n} → Seq g n → List (ℕ × List (ℕ × ℕ))
  entry-ents ∅             = []
  entry-ents (snoc Φ w Sm) = entry-ents Φ ++ (width w , ents Sm) ∷ []

-- The intermediates graph: an edge i → j when the block of S_j at entry i is non-empty. A simple
-- graph, so at most one edge per pair, however many positions relate.
dep-edges : ∀ {g n} → Seq g n → List (ℕ × ℕ)
dep-edges {g} Φ = go [] (entry-ents Φ)
  where
  insert : ℕ → List ℕ → List ℕ
  insert i []       = i ∷ []
  insert i (k ∷ ks) = ifᵇ i ≡ᵇ k then k ∷ ks else k ∷ insert i ks

  sources : List ℕ → List (ℕ × ℕ) → List ℕ
  sources ws = go′ []
    where
    go′ : List ℕ → List (ℕ × ℕ) → List ℕ
    go′ acc []             = acc
    go′ acc ((_ , c) ∷ es) =
      go′ (ifᵇ c <ᵇ g then acc else insert (locate ws (c ∸ g)) acc) es

  go : List ℕ → List (ℕ × List (ℕ × ℕ)) → List (ℕ × ℕ)
  go ws []               = []
  go ws ((w , es) ∷ Φe) =
    Data.List.map (λ i → i , length ws) (sources ws es) ++ go (ws ++ w ∷ []) Φe

-- The relation on positions carried by the edge i → j: pairs (p , q) with position p of entry i
-- related to position q of entry j.
edge-rel : ∀ {g n} → Seq g n → ℕ → ℕ → List (ℕ × ℕ)
edge-rel {g} Φ i j = go 0 [] (entry-ents Φ)
  where
  pick : List ℕ → ℕ × ℕ → List (ℕ × ℕ)
  pick ws (r , c) =
    ifᵇ c <ᵇ g then [] else
      (ifᵇ locate ws (c ∸ g) ≡ᵇ i then (offset-in ws (c ∸ g) , r) ∷ [] else [])
    where
    offset-in : List ℕ → ℕ → ℕ
    offset-in []       p = p
    offset-in (w ∷ ws) p = ifᵇ p <ᵇ w then p else offset-in ws (p ∸ w)

  go : ℕ → List ℕ → List (ℕ × List (ℕ × ℕ)) → List (ℕ × ℕ)
  go _ ws []               = []
  go k ws ((w , es) ∷ Φe) =
    (ifᵇ k ≡ᵇ j then concatMap (pick ws) es else []) ++ go (suc k) (ws ++ w ∷ []) Φe

seq-cast : ∀ {g m n} → m ≡ n → Seq g m → Seq g n
seq-cast refl Φ = Φ

mcast : ∀ {t} (g : ℕ) {m n} → m ≡ n → M.Matrix t (g + m) → M.Matrix t (g + n)
mcast g refl A = A

-- Append a sequence produced under environment g', rewriting each entry's environment block by the frame E.
append-subst : ∀ {g g' p n} → Seq g p → M.Matrix g' (g + p) → Seq g' n → Seq g (p + n)
append-subst {p = p} Φ E ∅ = seq-cast (sym (+-identityʳ p)) Φ
append-subst {g} {g'} {p} Φ E (snoc {n} Ψ w Sm) =
  seq-cast (+-assoc p n (width w))
    (snoc (append-subst Φ E Ψ) w (Sm M.∘ frame-emb g p n E))

------------------------------------------------------------------------
-- Markings of derivations.

mutual
  data MarkedD : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v : Val τ} {R} →
                 γ , t ⇓ v [ R ] → Set ℓ where
    doc      : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]} →
               first-order τ → MarkedD D → MarkedD D
    ⇓-var    : ∀ {Γ τ} {γ : Env Γ} (x : Γ ∋ τ) → MarkedD (⇓-var {γ = γ} x)
    ⇓-unit   : ∀ {Γ} {γ : Env Γ} → MarkedD (⇓-unit {γ = γ})
    ⇓-inl    : ∀ {Γ τ₁ τ₂} {γ : Env Γ} {t : Γ ⊢ τ₁} {v R} {D : γ , t ⇓ v [ R ]} →
               MarkedD D → MarkedD (⇓-inl {τ₂ = τ₂} D)
    ⇓-inr    : ∀ {Γ τ₁ τ₂} {γ : Env Γ} {t : Γ ⊢ τ₂} {v R} {D : γ , t ⇓ v [ R ]} →
               MarkedD D → MarkedD (⇓-inr {τ₁ = τ₁} D)
    ⇓-case-l : ∀ {Γ τ₁ τ₂ τ} {γ : Env Γ} {s : Γ ⊢ τ₁ [+] τ₂} {t₁ : Γ ▸ τ₁ ⊢ τ} {t₂ : Γ ▸ τ₂ ⊢ τ}
               {v u R S} {Ds : γ , s ⇓ inl v [ R ]} {D₁ : γ · v , t₁ ⇓ u [ S ]} →
               MarkedD Ds → MarkedD D₁ → MarkedD (⇓-case-l {t₂ = t₂} Ds D₁)
    ⇓-case-r : ∀ {Γ τ₁ τ₂ τ} {γ : Env Γ} {s : Γ ⊢ τ₁ [+] τ₂} {t₁ : Γ ▸ τ₁ ⊢ τ} {t₂ : Γ ▸ τ₂ ⊢ τ}
               {v u R S} {Ds : γ , s ⇓ inr v [ R ]} {D₂ : γ · v , t₂ ⇓ u [ S ]} →
               MarkedD Ds → MarkedD D₂ → MarkedD (⇓-case-r {t₁ = t₁} Ds D₂)
    ⇓-pair   : ∀ {Γ τ₁ τ₂} {γ : Env Γ} {s : Γ ⊢ τ₁} {t : Γ ⊢ τ₂} {v u R S}
               {D₁ : γ , s ⇓ v [ R ]} {D₂ : γ , t ⇓ u [ S ]} →
               MarkedD D₁ → MarkedD D₂ → MarkedD (⇓-pair D₁ D₂)
    ⇓-fst    : ∀ {Γ τ₁ τ₂} {γ : Env Γ} {t : Γ ⊢ τ₁ [×] τ₂} {v u R} {D : γ , t ⇓ pair v u [ R ]} →
               MarkedD D → MarkedD (⇓-fst D)
    ⇓-snd    : ∀ {Γ τ₁ τ₂} {γ : Env Γ} {t : Γ ⊢ τ₁ [×] τ₂} {v u R} {D : γ , t ⇓ pair v u [ R ]} →
               MarkedD D → MarkedD (⇓-snd D)
    ⇓-lam    : ∀ {Γ σ τ} {γ : Env Γ} {t : Γ ▸ σ ⊢ τ} → MarkedD (⇓-lam {γ = γ} {t = t})
    ⇓-app    : ∀ {Γ Γ' σ τ} {γ : Env Γ} {γ' : Env Γ'} {s : Γ ⊢ σ [→] τ} {t t' v u R S T}
               {Ds : γ , s ⇓ clo {Γ'} γ' t' [ R ]} {Dt : γ , t ⇓ v [ S ]}
               {Db : γ' · v , t' ⇓ u [ T ]} →
               MarkedD Ds → MarkedD Dt → MarkedD Db → MarkedD (⇓-app Ds Dt Db)
    ⇓-bop    : ∀ {Γ is o'} {γ : Env Γ} {ω : op is o'} {Ms : Every (λ s → Γ ⊢ base s) is} {vs R}
               {Es : γ , Ms ⇓s vs [ R ]} → MarkedDs Es → MarkedD (⇓-bop {ω = ω} Es)
    ⇓-brel   : ∀ {Γ is} {γ : Env Γ} {ω : rel is} {Ms : Every (λ s → Γ ⊢ base s) is} {vs R}
               {Es : γ , Ms ⇓s vs [ R ]} → MarkedDs Es → MarkedD (⇓-brel {ω = ω} Es)
    ⇓-roll   : ∀ {Γ} {τ : type 1} {γ : Env Γ} {t : Γ ⊢ τ [ μ τ ]} {v R} {D : γ , t ⇓ v [ R ]} →
               MarkedD D → MarkedD (⇓-roll {τ = τ} D)
    ⇓-fold   : ∀ {Γ} {τ : type 1} {σ : type 0} {γ : Env Γ} {s : Γ ▸ τ [ σ ] ⊢ σ} {t : Γ ⊢ μ τ}
               {v u R R'} {Dt : γ , t ⇓ v [ R ]} {Dm : Map γ {τ} {σ} s (var Fin.zero) v R u R'} →
               MarkedD Dt → MarkedM Dm → MarkedD (⇓-fold Dt Dm)

  data MarkedDs {Γ} {γ : Env Γ} : ∀ {is} {Ms : Every (λ s → Γ ⊢ base s) is} {vs Rs} →
                γ , Ms ⇓s vs [ Rs ] → Set ℓ where
    []  : MarkedDs []
    _∷_ : ∀ {i is v vs R Rs} {M : Γ ⊢ base i} {Ms : Every (λ s → Γ ⊢ base s) is}
          {E : γ , M ⇓ const v [ R ]} {Es : γ , Ms ⇓s vs [ Rs ]} →
          MarkedD E → MarkedDs Es → MarkedDs (E ∷ Es)

  data MarkedM {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr} :
               ∀ {σ' : type 1} {v : Val (σ' [ μ τ₀ ])} {R : M.Matrix (width v) (width-env γ)}
               {v' : Val (σ' [ σr ])} {R' : M.Matrix (width v') (width-env γ)} →
               Map γ s σ' v R v' R' → Set ℓ where
    m-rec   : ∀ {w w' u R R' S} {Dm : Map γ s τ₀ w R w' R'} {Db : γ · w' , s ⇓ u [ S ]} →
              MarkedM Dm → MarkedD Db → MarkedM (m-rec Dm Db)
    m-unit  : ∀ {v R} → MarkedM (m-unit {v = v} {R = R})
    m-base  : ∀ {b v R} → MarkedM (m-base {b = b} {v = v} {R = R})
    m-arrow : ∀ {σ₁ σ₂ v R} → MarkedM (m-arrow {σ₁ = σ₁} {σ₂ = σ₂} {v = v} {R = R})
    m-inl   : ∀ {σ₁ σ₂ v v' R R'} {Dm : Map γ s σ₁ v R v' R'} →
              MarkedM Dm → MarkedM (m-inl {σ₂ = σ₂} Dm)
    m-inr   : ∀ {σ₁ σ₂ v v' R R'} {Dm : Map γ s σ₂ v R v' R'} →
              MarkedM Dm → MarkedM (m-inr {σ₁ = σ₁} Dm)
    m-pair  : ∀ {σ₁ σ₂ v v' u u' R S T}
              {Dm₁ : Map γ s σ₁ v (p₁ ∘ R) v' S} {Dm₂ : Map γ s σ₂ u (p₂ ∘ R) u' T} →
              MarkedM Dm₁ → MarkedM Dm₂ → MarkedM (m-pair Dm₁ Dm₂)
    m-mu    : ∀ {τ' : type 2} {w w' R R'} {Dm : Map γ s (unfold₁ τ') w R w' R'} →
              MarkedM Dm → MarkedM (m-mu {τ' = τ'} Dm)

------------------------------------------------------------------------
-- Paths addressing the nodes of a derivation, as plain data so that a path can be checked against a
-- derivation without normalising it.

data Dir : Set where
  inl inr roll fst snd pair₁ pair₂ case₁ case₂ app₁ app₂ app₃ bop brel fold₁ fold₂ : Dir
  hd tl rec₁ rec₂ m-inj m-pair₁ m-pair₂ m-mu : Dir

Path : Set
Path = List Dir

------------------------------------------------------------------------
-- The blank overlay.

mutual
  unmarked-d : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} (D : γ , t ⇓ v [ R ]) → MarkedD D
  unmarked-d (⇓-var x)          = ⇓-var x
  unmarked-d ⇓-unit             = ⇓-unit
  unmarked-d ⇓-lam              = ⇓-lam
  unmarked-d (⇓-inl D)          = ⇓-inl (unmarked-d D)
  unmarked-d (⇓-inr D)          = ⇓-inr (unmarked-d D)
  unmarked-d (⇓-roll D)         = ⇓-roll (unmarked-d D)
  unmarked-d (⇓-fst D)          = ⇓-fst (unmarked-d D)
  unmarked-d (⇓-snd D)          = ⇓-snd (unmarked-d D)
  unmarked-d (⇓-pair D₁ D₂)     = ⇓-pair (unmarked-d D₁) (unmarked-d D₂)
  unmarked-d (⇓-case-l Ds D₁)   = ⇓-case-l (unmarked-d Ds) (unmarked-d D₁)
  unmarked-d (⇓-case-r Ds D₂)   = ⇓-case-r (unmarked-d Ds) (unmarked-d D₂)
  unmarked-d (⇓-app Ds Dt Db)   = ⇓-app (unmarked-d Ds) (unmarked-d Dt) (unmarked-d Db)
  unmarked-d (⇓-bop Es)         = ⇓-bop (unmarked-ds Es)
  unmarked-d (⇓-brel Es)        = ⇓-brel (unmarked-ds Es)
  unmarked-d (⇓-fold Dt Dm)     = ⇓-fold (unmarked-d Dt) (unmarked-dm Dm)

  unmarked-ds : ∀ {Γ is} {Ms : Every (λ s → Γ ⊢ base s) is} {γ : Env Γ} {vs Rs}
                (Ds : γ , Ms ⇓s vs [ Rs ]) → MarkedDs Ds
  unmarked-ds []       = []
  unmarked-ds (E ∷ Es) = unmarked-d E ∷ unmarked-ds Es

  unmarked-dm : ∀ {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr}
                {σ' : type 1} {v : Val (σ' [ μ τ₀ ])} {R : M.Matrix (width v) (width-env γ)}
                {v' : Val (σ' [ σr ])} {R' : M.Matrix (width v') (width-env γ)}
                (Dm : Map γ s σ' v R v' R') → MarkedM Dm
  unmarked-dm (m-rec Dm Db)    = m-rec (unmarked-dm Dm) (unmarked-d Db)
  unmarked-dm m-unit           = m-unit
  unmarked-dm m-base           = m-base
  unmarked-dm m-arrow          = m-arrow
  unmarked-dm (m-inl Dm)       = m-inl (unmarked-dm Dm)
  unmarked-dm (m-inr Dm)       = m-inr (unmarked-dm Dm)
  unmarked-dm (m-pair Dm₁ Dm₂) = m-pair (unmarked-dm Dm₁) (unmarked-dm Dm₂)
  unmarked-dm (m-mu Dm)        = m-mu (unmarked-dm Dm)

------------------------------------------------------------------------
-- The overlay marking every first-order node.

private
  first-order? : ∀ {Δ} (τ : type Δ) → Maybe (first-order τ)
  first-order? (var i)   = just (var i)
  first-order? unit      = just unit
  first-order? (base s)  = just (base s)
  first-order? (σ [+] τ) with first-order? σ | first-order? τ
  ... | just a  | just b  = just (a [+] b)
  ... | _       | _       = nothing
  first-order? (σ [×] τ) with first-order? σ | first-order? τ
  ... | just a  | just b  = just (a [×] b)
  ... | _       | _       = nothing
  first-order? (σ [→] τ) = nothing
  first-order? (μ τ) with first-order? τ
  ... | just a  = just (μ a)
  ... | nothing = nothing

mutual
  marked-all-d : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} (D : γ , t ⇓ v [ R ]) → MarkedD D
  marked-all-d {τ = τ} D with first-order? τ
  ... | just fo = doc fo (marked-all-d′ D)
  ... | nothing = marked-all-d′ D

  private
    marked-all-d′ : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} (D : γ , t ⇓ v [ R ]) → MarkedD D
    marked-all-d′ (⇓-var x)        = ⇓-var x
    marked-all-d′ ⇓-unit           = ⇓-unit
    marked-all-d′ ⇓-lam            = ⇓-lam
    marked-all-d′ (⇓-inl D)        = ⇓-inl (marked-all-d D)
    marked-all-d′ (⇓-inr D)        = ⇓-inr (marked-all-d D)
    marked-all-d′ (⇓-roll D)       = ⇓-roll (marked-all-d D)
    marked-all-d′ (⇓-fst D)        = ⇓-fst (marked-all-d D)
    marked-all-d′ (⇓-snd D)        = ⇓-snd (marked-all-d D)
    marked-all-d′ (⇓-pair D₁ D₂)   = ⇓-pair (marked-all-d D₁) (marked-all-d D₂)
    marked-all-d′ (⇓-case-l Ds D₁) = ⇓-case-l (marked-all-d Ds) (marked-all-d D₁)
    marked-all-d′ (⇓-case-r Ds D₂) = ⇓-case-r (marked-all-d Ds) (marked-all-d D₂)
    marked-all-d′ (⇓-app Ds Dt Db) = ⇓-app (marked-all-d Ds) (marked-all-d Dt) (marked-all-d Db)
    marked-all-d′ (⇓-bop Es)       = ⇓-bop (marked-all-ds Es)
    marked-all-d′ (⇓-brel Es)      = ⇓-brel (marked-all-ds Es)
    marked-all-d′ (⇓-fold Dt Dm)   = ⇓-fold (marked-all-d Dt) (marked-all-dm Dm)

    marked-all-ds : ∀ {Γ is} {Ms : Every (λ s → Γ ⊢ base s) is} {γ : Env Γ} {vs Rs}
                    (Ds : γ , Ms ⇓s vs [ Rs ]) → MarkedDs Ds
    marked-all-ds []       = []
    marked-all-ds (E ∷ Es) = marked-all-d E ∷ marked-all-ds Es

    marked-all-dm : ∀ {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr}
                    {σ' : type 1} {v : Val (σ' [ μ τ₀ ])} {R : M.Matrix (width v) (width-env γ)}
                    {v' : Val (σ' [ σr ])} {R' : M.Matrix (width v') (width-env γ)}
                    (Dm : Map γ s σ' v R v' R') → MarkedM Dm
    marked-all-dm (m-rec Dm Db)    = m-rec (marked-all-dm Dm) (marked-all-d Db)
    marked-all-dm m-unit           = m-unit
    marked-all-dm m-base           = m-base
    marked-all-dm m-arrow          = m-arrow
    marked-all-dm (m-inl Dm)       = m-inl (marked-all-dm Dm)
    marked-all-dm (m-inr Dm)       = m-inr (marked-all-dm Dm)
    marked-all-dm (m-pair Dm₁ Dm₂) = m-pair (marked-all-dm Dm₁) (marked-all-dm Dm₂)
    marked-all-dm (m-mu Dm)        = m-mu (marked-all-dm Dm)

------------------------------------------------------------------------
-- Mark or unmark the node at a path. Marking is idempotent and unmarking strips every mark at the node; a
-- path step that does not match the derivation, or a mark at a higher-order node, leaves the overlay
-- unchanged.

private
  mark-here : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]} →
              MarkedD D → MarkedD D
  mark-here (doc f m) = doc f m
  mark-here {τ = τ} m with first-order? τ
  ... | just fo = doc fo m
  ... | nothing = m

  unmark-here : ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]} →
                MarkedD D → MarkedD D
  unmark-here (doc f m) = unmark-here m
  unmark-here m = m

mark-at :
  ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]} →
  Path → MarkedD D → MarkedD D
mark-at-s :
  ∀ {Γ is} {Ms : Every (λ s → Γ ⊢ base s) is} {γ : Env Γ} {vs Rs}
  {Ds : γ , Ms ⇓s vs [ Rs ]} →
  Path → MarkedDs Ds → MarkedDs Ds
mark-at-m :
  ∀ {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr}
  {σ' : type 1} {v : Val (σ' [ μ τ₀ ])} {R : M.Matrix (width v) (width-env γ)}
  {v' : Val (σ' [ σr ])} {R' : M.Matrix (width v') (width-env γ)}
  {Dm : Map γ s σ' v R v' R'} →
  Path → MarkedM Dm → MarkedM Dm

mark-at [] m = mark-here m
mark-at (d ∷ p) (doc f m)                 = doc f (mark-at (d ∷ p) m)
mark-at (inl ∷ p) (⇓-inl mD)              = ⇓-inl (mark-at p mD)
mark-at (inr ∷ p) (⇓-inr mD)              = ⇓-inr (mark-at p mD)
mark-at (roll ∷ p) (⇓-roll mD)            = ⇓-roll (mark-at p mD)
mark-at (fst ∷ p) (⇓-fst mD)              = ⇓-fst (mark-at p mD)
mark-at (snd ∷ p) (⇓-snd mD)              = ⇓-snd (mark-at p mD)
mark-at (pair₁ ∷ p) (⇓-pair mD₁ mD₂)      = ⇓-pair (mark-at p mD₁) mD₂
mark-at (pair₂ ∷ p) (⇓-pair mD₁ mD₂)      = ⇓-pair mD₁ (mark-at p mD₂)
mark-at (case₁ ∷ p) (⇓-case-l mDs mD₁)    = ⇓-case-l (mark-at p mDs) mD₁
mark-at (case₁ ∷ p) (⇓-case-r mDs mD₂)    = ⇓-case-r (mark-at p mDs) mD₂
mark-at (case₂ ∷ p) (⇓-case-l mDs mD₁)    = ⇓-case-l mDs (mark-at p mD₁)
mark-at (case₂ ∷ p) (⇓-case-r mDs mD₂)    = ⇓-case-r mDs (mark-at p mD₂)
mark-at (app₁ ∷ p) (⇓-app mDs mDt mDb)    = ⇓-app (mark-at p mDs) mDt mDb
mark-at (app₂ ∷ p) (⇓-app mDs mDt mDb)    = ⇓-app mDs (mark-at p mDt) mDb
mark-at (app₃ ∷ p) (⇓-app mDs mDt mDb)    = ⇓-app mDs mDt (mark-at p mDb)
mark-at (bop ∷ p) (⇓-bop mEs)             = ⇓-bop (mark-at-s p mEs)
mark-at (brel ∷ p) (⇓-brel mEs)           = ⇓-brel (mark-at-s p mEs)
mark-at (fold₁ ∷ p) (⇓-fold mDt mDm)      = ⇓-fold (mark-at p mDt) mDm
mark-at (fold₂ ∷ p) (⇓-fold mDt mDm)      = ⇓-fold mDt (mark-at-m p mDm)
mark-at (_ ∷ _) m = m

mark-at-s (hd ∷ p) (mE ∷ mEs) = mark-at p mE ∷ mEs
mark-at-s (tl ∷ p) (mE ∷ mEs) = mE ∷ mark-at-s p mEs
mark-at-s _ mEs = mEs

mark-at-m (rec₁ ∷ p) (m-rec mDm mDb)      = m-rec (mark-at-m p mDm) mDb
mark-at-m (rec₂ ∷ p) (m-rec mDm mDb)      = m-rec mDm (mark-at p mDb)
mark-at-m (m-inj ∷ p) (m-inl mDm)         = m-inl (mark-at-m p mDm)
mark-at-m (m-inj ∷ p) (m-inr mDm)         = m-inr (mark-at-m p mDm)
mark-at-m (m-pair₁ ∷ p) (m-pair mDm₁ mDm₂) = m-pair (mark-at-m p mDm₁) mDm₂
mark-at-m (m-pair₂ ∷ p) (m-pair mDm₁ mDm₂) = m-pair mDm₁ (mark-at-m p mDm₂)
mark-at-m (m-mu ∷ p) (m-mu mDm)           = m-mu (mark-at-m p mDm)
mark-at-m _ mDm = mDm

unmark-at :
  ∀ {Γ τ} {γ : Env Γ} {t : Γ ⊢ τ} {v R} {D : γ , t ⇓ v [ R ]} →
  Path → MarkedD D → MarkedD D
unmark-at-s :
  ∀ {Γ is} {Ms : Every (λ s → Γ ⊢ base s) is} {γ : Env Γ} {vs Rs}
  {Ds : γ , Ms ⇓s vs [ Rs ]} →
  Path → MarkedDs Ds → MarkedDs Ds
unmark-at-m :
  ∀ {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr}
  {σ' : type 1} {v : Val (σ' [ μ τ₀ ])} {R : M.Matrix (width v) (width-env γ)}
  {v' : Val (σ' [ σr ])} {R' : M.Matrix (width v') (width-env γ)}
  {Dm : Map γ s σ' v R v' R'} →
  Path → MarkedM Dm → MarkedM Dm

unmark-at [] m = unmark-here m
unmark-at (d ∷ p) (doc f m)                 = doc f (unmark-at (d ∷ p) m)
unmark-at (inl ∷ p) (⇓-inl mD)              = ⇓-inl (unmark-at p mD)
unmark-at (inr ∷ p) (⇓-inr mD)              = ⇓-inr (unmark-at p mD)
unmark-at (roll ∷ p) (⇓-roll mD)            = ⇓-roll (unmark-at p mD)
unmark-at (fst ∷ p) (⇓-fst mD)              = ⇓-fst (unmark-at p mD)
unmark-at (snd ∷ p) (⇓-snd mD)              = ⇓-snd (unmark-at p mD)
unmark-at (pair₁ ∷ p) (⇓-pair mD₁ mD₂)      = ⇓-pair (unmark-at p mD₁) mD₂
unmark-at (pair₂ ∷ p) (⇓-pair mD₁ mD₂)      = ⇓-pair mD₁ (unmark-at p mD₂)
unmark-at (case₁ ∷ p) (⇓-case-l mDs mD₁)    = ⇓-case-l (unmark-at p mDs) mD₁
unmark-at (case₁ ∷ p) (⇓-case-r mDs mD₂)    = ⇓-case-r (unmark-at p mDs) mD₂
unmark-at (case₂ ∷ p) (⇓-case-l mDs mD₁)    = ⇓-case-l mDs (unmark-at p mD₁)
unmark-at (case₂ ∷ p) (⇓-case-r mDs mD₂)    = ⇓-case-r mDs (unmark-at p mD₂)
unmark-at (app₁ ∷ p) (⇓-app mDs mDt mDb)    = ⇓-app (unmark-at p mDs) mDt mDb
unmark-at (app₂ ∷ p) (⇓-app mDs mDt mDb)    = ⇓-app mDs (unmark-at p mDt) mDb
unmark-at (app₃ ∷ p) (⇓-app mDs mDt mDb)    = ⇓-app mDs mDt (unmark-at p mDb)
unmark-at (bop ∷ p) (⇓-bop mEs)             = ⇓-bop (unmark-at-s p mEs)
unmark-at (brel ∷ p) (⇓-brel mEs)           = ⇓-brel (unmark-at-s p mEs)
unmark-at (fold₁ ∷ p) (⇓-fold mDt mDm)      = ⇓-fold (unmark-at p mDt) mDm
unmark-at (fold₂ ∷ p) (⇓-fold mDt mDm)      = ⇓-fold mDt (unmark-at-m p mDm)
unmark-at (_ ∷ _) m = m

unmark-at-s (hd ∷ p) (mE ∷ mEs) = unmark-at p mE ∷ mEs
unmark-at-s (tl ∷ p) (mE ∷ mEs) = mE ∷ unmark-at-s p mEs
unmark-at-s _ mEs = mEs

unmark-at-m (rec₁ ∷ p) (m-rec mDm mDb)      = m-rec (unmark-at-m p mDm) mDb
unmark-at-m (rec₂ ∷ p) (m-rec mDm mDb)      = m-rec mDm (unmark-at p mDb)
unmark-at-m (m-inj ∷ p) (m-inl mDm)         = m-inl (unmark-at-m p mDm)
unmark-at-m (m-inj ∷ p) (m-inr mDm)         = m-inr (unmark-at-m p mDm)
unmark-at-m (m-pair₁ ∷ p) (m-pair mDm₁ mDm₂) = m-pair (unmark-at-m p mDm₁) mDm₂
unmark-at-m (m-pair₂ ∷ p) (m-pair mDm₁ mDm₂) = m-pair mDm₁ (unmark-at-m p mDm₂)
unmark-at-m (m-mu ∷ p) (m-mu mDm)           = m-mu (unmark-at-m p mDm)
unmark-at-m _ mDm = mDm

------------------------------------------------------------------------
-- Instrumentation.

Out : (g p t : ℕ) → Set ℓ
Out g p t = Σ ℕ λ k → Seq g (p + k) × M.Matrix t (g + (p + k))

private
  leaf : ∀ {g p t} → Seq g p → M.Matrix t g → Out g p t
  leaf {g} {p} Φ A = 0 , seq-cast (sym (+-identityʳ p)) Φ , pad g (p + 0) A

  assoc3 : ∀ p a b c → ((p + a) + b) + c ≡ p + ((a + b) + c)
  assoc3 p a b c = trans (cong (_+ c) (+-assoc p a b)) (+-assoc p (a + b) c)

  rowcast : ∀ {c m n} → m ≡ n → M.Matrix m c → M.Matrix n c
  rowcast refl A = A

instrument-d :
  ∀ {Γ τ} {t : Γ ⊢ τ} {γ : Env Γ} {v R} {p} {D : γ , t ⇓ v [ R ]} →
  MarkedD D → Seq (width-env γ) p → Out (width-env γ) p (width v)
instrument-ds :
  ∀ {Γ is} {Ms : Every (λ s → Γ ⊢ base s) is} {γ : Env Γ} {vs Rs} {p}
  {Ds : γ , Ms ⇓s vs [ Rs ]} →
  MarkedDs Ds → Seq (width-env γ) p → Out (width-env γ) p (bases-width is)
instrument-dm :
  ∀ {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr}
  {σ' : type 1} {v : Val (σ' [ μ τ₀ ])} {R : M.Matrix (width v) (width-env γ)}
  {v' : Val (σ' [ σr ])} {R' : M.Matrix (width v') (width-env γ)} {p}
  {Dm : Map γ s σ' v R v' R'} →
  MarkedM Dm → Seq (width-env γ) p → M.Matrix (width v) (width-env γ + p) →
  Out (width-env γ) p (width v')

instrument-d {γ = γ} {v = v} {p = p} (doc fo mD) Φ
  with instrument-d mD Φ
... | k , Φ' , R' =
  k + width v
  , seq-cast (+-assoc p k (width v)) (snoc Φ' v R')
  , mcast (width-env γ) (+-assoc p k (width v)) (inj-last (width-env γ) (p + k) (width v))
instrument-d {γ = γ} (⇓-var x) Φ = leaf Φ (proj-var x γ)
instrument-d ⇓-unit Φ = leaf Φ M.εₘ
instrument-d ⇓-lam Φ = leaf Φ M.I
instrument-d (⇓-inl mD) Φ = instrument-d mD Φ
instrument-d (⇓-inr mD) Φ = instrument-d mD Φ
instrument-d (⇓-roll mD) Φ = instrument-d mD Φ
instrument-d (⇓-fst mD) Φ with instrument-d mD Φ
... | k , Φ' , R' = k , Φ' , M.p₁ M.∘ R'
instrument-d (⇓-snd mD) Φ with instrument-d mD Φ
... | k , Φ' , R' = k , Φ' , M.p₂ M.∘ R'
instrument-d {γ = γ} {p = p} (⇓-pair mD₁ mD₂) Φ
  with instrument-d mD₁ Φ
... | k₁ , Φ₁ , R₁
  with instrument-d mD₂ Φ₁
... | k₂ , Φ₂ , R₂ =
  k₁ + k₂
  , seq-cast (+-assoc p k₁ k₂) Φ₂
  , mcast (width-env γ) (+-assoc p k₁ k₂)
      (stack _ _ (widen (width-env γ) (p + k₁) k₂ R₁) R₂)
instrument-d {γ = γ} {p = p} (⇓-case-l mDs mD₁) Φ
  with instrument-d mDs Φ
... | k₁ , Φ₁ , R₁
  with instrument-d mD₁ ∅
... | k₂ , Φ₂ , Sb =
  k₁ + k₂
  , seq-cast (+-assoc p k₁ k₂)
      (append-subst Φ₁ (stack _ _ (id-frame (width-env γ) (p + k₁)) R₁) Φ₂)
  , mcast (width-env γ) (+-assoc p k₁ k₂)
      (Sb M.∘ frame-emb (width-env γ) (p + k₁) k₂
              (stack _ _ (id-frame (width-env γ) (p + k₁)) R₁))
instrument-d {γ = γ} {p = p} (⇓-case-r mDs mD₂) Φ
  with instrument-d mDs Φ
... | k₁ , Φ₁ , R₁
  with instrument-d mD₂ ∅
... | k₂ , Φ₂ , Sb =
  k₁ + k₂
  , seq-cast (+-assoc p k₁ k₂)
      (append-subst Φ₁ (stack _ _ (id-frame (width-env γ) (p + k₁)) R₁) Φ₂)
  , mcast (width-env γ) (+-assoc p k₁ k₂)
      (Sb M.∘ frame-emb (width-env γ) (p + k₁) k₂
              (stack _ _ (id-frame (width-env γ) (p + k₁)) R₁))
instrument-d {γ = γ} {p = p} (⇓-app mDs mDt mDb) Φ
  with instrument-d mDs Φ
... | k₁ , Φ₁ , R
  with instrument-d mDt Φ₁
... | k₂ , Φ₂ , Sa
  with instrument-d mDb ∅
... | k₃ , Φ₃ , Tb =
  (k₁ + k₂) + k₃
  , seq-cast (assoc3 p k₁ k₂ k₃)
      (append-subst Φ₂ (stack _ _ (widen (width-env γ) (p + k₁) k₂ R) Sa) Φ₃)
  , mcast (width-env γ) (assoc3 p k₁ k₂ k₃)
      (Tb M.∘ frame-emb (width-env γ) ((p + k₁) + k₂) k₃
              (stack _ _ (widen (width-env γ) (p + k₁) k₂ R) Sa))
instrument-d (⇓-bop {ω = ω} {vs = vs} mEs) Φ
  with instrument-ds mEs Φ
... | k , Φ' , Rs = k , Φ' , op-deps ω .func vs M.∘ Rs
instrument-d {γ = γ} {p = p} (⇓-brel {ω = ω} {vs = vs} mEs) Φ
  with instrument-ds mEs Φ
... | k , Φ' , Rs =
  k , Φ' , pad (width-env γ) (p + k) (brel-mat γ (rel-pred ω .func vs))
instrument-d {γ = γ} {p = p} (⇓-fold mDt mDm) Φ
  with instrument-d mDt Φ
... | k₁ , Φ₁ , R₁
  with instrument-dm mDm Φ₁ R₁
... | k₂ , Φ₂ , R₂ =
  k₁ + k₂ , seq-cast (+-assoc p k₁ k₂) Φ₂ , mcast (width-env γ) (+-assoc p k₁ k₂) R₂

instrument-ds [] Φ = leaf Φ M.εₘ
instrument-ds {γ = γ} {p = p} (mE ∷ mEs) Φ
  with instrument-d mE Φ
... | k₁ , Φ₁ , R₁
  with instrument-ds mEs Φ₁
... | k₂ , Φ₂ , Rs =
  k₁ + k₂
  , seq-cast (+-assoc p k₁ k₂) Φ₂
  , mcast (width-env γ) (+-assoc p k₁ k₂)
      (stack _ _ (widen (width-env γ) (p + k₁) k₂ R₁) Rs)

instrument-dm {γ = γ} {p = p} m-unit Φ Rin =
  0 , seq-cast (sym (+-identityʳ p)) Φ , widen (width-env γ) p 0 Rin
instrument-dm {γ = γ} {p = p} m-base Φ Rin =
  0 , seq-cast (sym (+-identityʳ p)) Φ , widen (width-env γ) p 0 Rin
instrument-dm {γ = γ} {p = p} m-arrow Φ Rin =
  0 , seq-cast (sym (+-identityʳ p)) Φ , widen (width-env γ) p 0 Rin
instrument-dm (m-inl mDm) Φ Rin = instrument-dm mDm Φ Rin
instrument-dm (m-inr mDm) Φ Rin = instrument-dm mDm Φ Rin
instrument-dm {γ = γ} {p = p} (m-pair mDm₁ mDm₂) Φ Rin
  with instrument-dm mDm₁ Φ (M.p₁ M.∘ Rin)
... | k₁ , Φ₁ , S₁
  with instrument-dm mDm₂ Φ₁ (widen (width-env γ) p k₁ (M.p₂ M.∘ Rin))
... | k₂ , Φ₂ , S₂ =
  k₁ + k₂
  , seq-cast (+-assoc p k₁ k₂) Φ₂
  , mcast (width-env γ) (+-assoc p k₁ k₂)
      (stack _ _ (widen (width-env γ) (p + k₁) k₂ S₁) S₂)
instrument-dm {γ = γ} {p = p} (m-rec mDm mDb) Φ Rin
  with instrument-dm mDm Φ Rin
... | k₁ , Φ₁ , R₁
  with instrument-d mDb ∅
... | k₂ , Φ₂ , Sb =
  k₁ + k₂
  , seq-cast (+-assoc p k₁ k₂)
      (append-subst Φ₁ (stack _ _ (id-frame (width-env γ) (p + k₁)) R₁) Φ₂)
  , mcast (width-env γ) (+-assoc p k₁ k₂)
      (Sb M.∘ frame-emb (width-env γ) (p + k₁) k₂
              (stack _ _ (id-frame (width-env γ) (p + k₁)) R₁))
instrument-dm {γ = γ} {τ₀ = τ₀} {σr = σr} (m-mu {τ' = τ'} {w = w} {w' = w'} mDm) Φ Rin
  with instrument-dm mDm Φ (rowcast (width-subst (unfold₁-inst τ' (μ τ₀)) w) Rin)
... | k , Φ' , S' =
  k , Φ' , rowcast (sym (width-subst (unfold₁-inst τ' σr) w')) S'

