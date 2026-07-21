{-# OPTIONS --prop --postfix-projections --safe #-}

import Level
open import Data.Fin using (Fin; splitAt; toℕ; _↑ˡ_; _↑ʳ_)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _<ᵇ_; _≡ᵇ_)
open import Data.Bool using () renaming (if_then_else_ to ifᵇ_then_else_)
open import Data.Nat.Properties using (+-assoc; +-identityʳ)
open import Relation.Binary.PropositionalEquality using (trans; cong)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum using (inj₁; inj₂)
import Data.List
open import Data.List using (List; []; _∷_; _++_; length; concatMap; allFin)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym) renaming (subst to ≡-subst)
open import prop-setoid using (Setoid)
open import commutative-semiring using (CommutativeSemiring)
open import every using (Every; []; _∷_)
open import signature using (Signature)
open import primitives using (Primitives)
import matrix
import two

-- Instrumentation of evaluation derivations: given a marking of the term, computes the sequence of
-- intermediates and the dependency matrix over the extended domain, the data of the instrumented judgement,
-- by structural recursion on the derivation. Markings flow through values, so that the body run at an
-- application site carries the marking captured by its closure.
module language-operational.instrument
  {ℓ} (Sig : Signature ℓ) (𝒫 : Primitives two.semiring Sig) where

open Signature Sig
open Primitives 𝒫
open prop-setoid._⇒_ using (func)
open import language-syntax Sig renaming (_,_ to _▸_)
open import language-operational.evaluation Sig 𝒫
open import type-substitution Sig using (unfold₁; unfold₁-inst)
open import language-operational.marking Sig

private
  module CS = CommutativeSemiring two.semiring
  module M = matrix.Mat two.semiring

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
-- Markings of values and environments: closures capture their body's marking.

mutual
  data MarkedV : ∀ {τ} → Val τ → Set ℓ where
    unit  : MarkedV unit
    const : ∀ {s} {c : sort-val s} → MarkedV (const c)
    inl   : ∀ {σ τ} {v : Val σ} → MarkedV v → MarkedV (inl {τ₂ = τ} v)
    inr   : ∀ {σ τ} {v : Val τ} → MarkedV v → MarkedV (inr {τ₁ = σ} v)
    pair  : ∀ {σ τ} {v : Val σ} {u : Val τ} → MarkedV v → MarkedV u → MarkedV (pair v u)
    clo   : ∀ {Γ σ τ} {γ : Env Γ} {t : Γ ▸ σ ⊢ τ} →
            MarkedE γ → Marked t → MarkedV (clo γ t)
    roll  : ∀ {τ} {v : Val (τ [ μ τ ])} → MarkedV v → MarkedV (roll {τ} v)

  data MarkedE : ∀ {Γ} → Env Γ → Set ℓ where
    emp : MarkedE emp
    _·_ : ∀ {Γ τ} {γ : Env Γ} {v : Val τ} → MarkedE γ → MarkedV v → MarkedE (γ · v)

lookupM : ∀ {Γ τ} (x : Γ ∋ τ) {γ : Env Γ} → MarkedE γ → MarkedV (lookup x γ)
lookupM zero     {γ · v} (mγ · mv) = mv
lookupM (succ x) {γ · v} (mγ · mv) = lookupM x mγ

boolM : ∀ b → MarkedV (bool→val b)
boolM (inj₁ _) = inl unit
boolM (inj₂ _) = inr unit

mvcast : ∀ {τ τ'} (e : τ ≡ τ') {v : Val τ} → MarkedV v → MarkedV (≡-subst Val e v)
mvcast refl mv = mv

------------------------------------------------------------------------
-- Instrumentation.

Out : (g p t : ℕ) → Set ℓ
Out g p t = Σ ℕ λ k → Seq g (p + k) × M.Matrix t (g + (p + k))

private
  leaf : ∀ {g p t} → Seq g p → M.Matrix t g → Out g p t
  leaf {g} {p} Φ A = 0 , seq-cast (sym (+-identityʳ p)) Φ , pad g (p + 0) A

instrument :
  ∀ {Γ τ} {t : Γ ⊢ τ} {γ : Env Γ} {v R} {p} →
  Marked t → MarkedE γ → γ , t ⇓ v [ R ] → Seq (width-env γ) p →
  MarkedV v × Out (width-env γ) p (width v)
instrument-s :
  ∀ {Γ is} {Ms : Every (λ s → Γ ⊢ base s) is} {γ : Env Γ} {vs Rs} {p} →
  MarkedS Ms → MarkedE γ → γ , Ms ⇓s vs [ Rs ] → Seq (width-env γ) p →
  Out (width-env γ) p (bases-width is)
instrument-map :
  ∀ {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr}
  {σ' : type 1} {v : Val (σ' [ μ τ₀ ])} {R : M.Matrix (width v) (width-env γ)}
  {v' : Val (σ' [ σr ])} {R' : M.Matrix (width v') (width-env γ)} {p} →
  Marked s → MarkedE γ → MarkedV v → Map γ s σ' v R v' R' →
  Seq (width-env γ) p → M.Matrix (width v) (width-env γ + p) →
  MarkedV v' × Out (width-env γ) p (width v')

private
  assoc3 : ∀ p a b c → ((p + a) + b) + c ≡ p + ((a + b) + c)
  assoc3 p a b c = trans (cong (_+ c) (+-assoc p a b)) (+-assoc p (a + b) c)

  rowcast : ∀ {c m n} → m ≡ n → M.Matrix m c → M.Matrix n c
  rowcast refl A = A

  mv-uncast : ∀ {τ τ'} (e : τ ≡ τ') {v : Val τ} → MarkedV (≡-subst Val e v) → MarkedV v
  mv-uncast refl mv = mv

instrument {γ = γ} {v = v} {p = p} (doc fo m) mγ D Φ
  with instrument m mγ D Φ
... | mv , (k , Φ' , R') =
  mv , (k + width v
       , seq-cast (+-assoc p k (width v)) (snoc Φ' v R')
       , mcast (width-env γ) (+-assoc p k (width v)) (inj-last (width-env γ) (p + k) (width v)))
instrument {γ = γ} (var x) mγ (⇓-var .x) Φ = lookupM x mγ , leaf Φ (proj-var x γ)
instrument unit mγ ⇓-unit Φ = unit , leaf Φ M.εₘ
instrument (lam m) mγ ⇓-lam Φ = clo mγ m , leaf Φ M.I
instrument (inl m) mγ (⇓-inl D) Φ with instrument m mγ D Φ
... | mv , out = inl mv , out
instrument (inr m) mγ (⇓-inr D) Φ with instrument m mγ D Φ
... | mv , out = inr mv , out
instrument (roll m) mγ (⇓-roll D) Φ with instrument m mγ D Φ
... | mv , out = roll mv , out
instrument (fst m) mγ (⇓-fst D) Φ with instrument m mγ D Φ
... | pair mv₁ mv₂ , (k , Φ' , R') = mv₁ , (k , Φ' , M.p₁ M.∘ R')
instrument (snd m) mγ (⇓-snd D) Φ with instrument m mγ D Φ
... | pair mv₁ mv₂ , (k , Φ' , R') = mv₂ , (k , Φ' , M.p₂ M.∘ R')
instrument {γ = γ} {p = p} (pair m₁ m₂) mγ (⇓-pair D₁ D₂) Φ
  with instrument m₁ mγ D₁ Φ
... | mv₁ , (k₁ , Φ₁ , R₁)
  with instrument m₂ mγ D₂ Φ₁
... | mv₂ , (k₂ , Φ₂ , R₂) =
  pair mv₁ mv₂ ,
  (k₁ + k₂
  , seq-cast (+-assoc p k₁ k₂) Φ₂
  , mcast (width-env γ) (+-assoc p k₁ k₂)
      (stack _ _ (widen (width-env γ) (p + k₁) k₂ R₁) R₂))
instrument {γ = γ} {p = p} (case ms m₁ m₂) mγ (⇓-case-l Ds D₁) Φ
  with instrument ms mγ Ds Φ
... | inl mv , (k₁ , Φ₁ , R₁)
  with instrument m₁ (mγ · mv) D₁ ∅
... | mvU , (k₂ , Φ₂ , Sb) =
  mvU ,
  (k₁ + k₂
  , seq-cast (+-assoc p k₁ k₂)
      (append-subst Φ₁ (stack _ _ (id-frame (width-env γ) (p + k₁)) R₁) Φ₂)
  , mcast (width-env γ) (+-assoc p k₁ k₂)
      (Sb M.∘ frame-emb (width-env γ) (p + k₁) k₂
              (stack _ _ (id-frame (width-env γ) (p + k₁)) R₁)))
instrument {γ = γ} {p = p} (case ms m₁ m₂) mγ (⇓-case-r Ds D₂) Φ
  with instrument ms mγ Ds Φ
... | inr mv , (k₁ , Φ₁ , R₁)
  with instrument m₂ (mγ · mv) D₂ ∅
... | mvU , (k₂ , Φ₂ , Sb) =
  mvU ,
  (k₁ + k₂
  , seq-cast (+-assoc p k₁ k₂)
      (append-subst Φ₁ (stack _ _ (id-frame (width-env γ) (p + k₁)) R₁) Φ₂)
  , mcast (width-env γ) (+-assoc p k₁ k₂)
      (Sb M.∘ frame-emb (width-env γ) (p + k₁) k₂
              (stack _ _ (id-frame (width-env γ) (p + k₁)) R₁)))
instrument {γ = γ} {p = p} (app ms mt) mγ (⇓-app Ds Dt Db) Φ
  with instrument ms mγ Ds Φ
... | clo mE mt' , (k₁ , Φ₁ , R)
  with instrument mt mγ Dt Φ₁
... | mvA , (k₂ , Φ₂ , Sa)
  with instrument mt' (mE · mvA) Db ∅
... | mvU , (k₃ , Φ₃ , Tb) =
  mvU ,
  ((k₁ + k₂) + k₃
  , seq-cast (assoc3 p k₁ k₂ k₃)
      (append-subst Φ₂ (stack _ _ (widen (width-env γ) (p + k₁) k₂ R) Sa) Φ₃)
  , mcast (width-env γ) (assoc3 p k₁ k₂ k₃)
      (Tb M.∘ frame-emb (width-env γ) ((p + k₁) + k₂) k₃
              (stack _ _ (widen (width-env γ) (p + k₁) k₂ R) Sa)))
instrument (bop ms) mγ (⇓-bop {ω = ω} {vs = vs} Es) Φ
  with instrument-s ms mγ Es Φ
... | (k , Φ' , Rs) = const , (k , Φ' , op-deps ω .func vs M.∘ Rs)
instrument {γ = γ} {p = p} (brel ms) mγ (⇓-brel {ω = ω} {vs = vs} Es) Φ
  with instrument-s ms mγ Es Φ
... | (k , Φ' , Rs) =
  boolM (rel-pred ω .func vs) ,
  (k , Φ' , pad (width-env γ) (p + k) (brel-mat γ (rel-pred ω .func vs)))
instrument {γ = γ} {p = p} (fold m-s m-t) mγ (⇓-fold Dt Dm) Φ
  with instrument m-t mγ Dt Φ
... | mvV , (k₁ , Φ₁ , R₁)
  with instrument-map m-s mγ mvV Dm Φ₁ R₁
... | mvU , (k₂ , Φ₂ , R₂) =
  mvU , (k₁ + k₂ , seq-cast (+-assoc p k₁ k₂) Φ₂ , mcast (width-env γ) (+-assoc p k₁ k₂) R₂)

instrument-s [] mγ [] Φ = leaf Φ M.εₘ
instrument-s {γ = γ} {p = p} (m ∷ ms) mγ (E ∷ Es) Φ
  with instrument m mγ E Φ
... | _ , (k₁ , Φ₁ , R₁)
  with instrument-s ms mγ Es Φ₁
... | (k₂ , Φ₂ , Rs) =
  (k₁ + k₂
  , seq-cast (+-assoc p k₁ k₂) Φ₂
  , mcast (width-env γ) (+-assoc p k₁ k₂)
      (stack _ _ (widen (width-env γ) (p + k₁) k₂ R₁) Rs))

instrument-map {γ = γ} {v = v} {R = R} {p = p} m-s mγ mv m-unit Φ Rin =
  mv , (0 , seq-cast (sym (+-identityʳ p)) Φ , widen (width-env γ) p 0 Rin)
instrument-map {γ = γ} {v = v} {R = R} {p = p} m-s mγ mv m-base Φ Rin =
  mv , (0 , seq-cast (sym (+-identityʳ p)) Φ , widen (width-env γ) p 0 Rin)
instrument-map {γ = γ} {v = v} {R = R} {p = p} m-s mγ mv m-arrow Φ Rin =
  mv , (0 , seq-cast (sym (+-identityʳ p)) Φ , widen (width-env γ) p 0 Rin)
instrument-map m-s mγ (inl mv) (m-inl Dm) Φ Rin
  with instrument-map m-s mγ mv Dm Φ Rin
... | mvO , out = inl mvO , out
instrument-map m-s mγ (inr mv) (m-inr Dm) Φ Rin
  with instrument-map m-s mγ mv Dm Φ Rin
... | mvO , out = inr mvO , out
instrument-map {γ = γ} {p = p} m-s mγ (pair mv₁ mv₂) (m-pair Dm₁ Dm₂) Φ Rin
  with instrument-map m-s mγ mv₁ Dm₁ Φ (M.p₁ M.∘ Rin)
... | mvO₁ , (k₁ , Φ₁ , S₁)
  with instrument-map m-s mγ mv₂ Dm₂ Φ₁ (widen (width-env γ) p k₁ (M.p₂ M.∘ Rin))
... | mvO₂ , (k₂ , Φ₂ , S₂) =
  pair mvO₁ mvO₂ ,
  (k₁ + k₂
  , seq-cast (+-assoc p k₁ k₂) Φ₂
  , mcast (width-env γ) (+-assoc p k₁ k₂)
      (stack _ _ (widen (width-env γ) (p + k₁) k₂ S₁) S₂))
instrument-map {γ = γ} {p = p} m-s mγ (roll mv) (m-rec Dm Db) Φ Rin
  with instrument-map m-s mγ mv Dm Φ Rin
... | mvW , (k₁ , Φ₁ , R₁)
  with instrument m-s (mγ · mvW) Db ∅
... | mvU , (k₂ , Φ₂ , Sb) =
  mvU ,
  (k₁ + k₂
  , seq-cast (+-assoc p k₁ k₂)
      (append-subst Φ₁ (stack _ _ (id-frame (width-env γ) (p + k₁)) R₁) Φ₂)
  , mcast (width-env γ) (+-assoc p k₁ k₂)
      (Sb M.∘ frame-emb (width-env γ) (p + k₁) k₂
              (stack _ _ (id-frame (width-env γ) (p + k₁)) R₁)))
instrument-map {γ = γ} {τ₀ = τ₀} {σr = σr} m-s mγ (roll mv)
  (m-mu {τ' = τ'} {w = w} {w' = w'} Dm) Φ Rin
  with instrument-map m-s mγ (mv-uncast (unfold₁-inst τ' (μ τ₀)) mv) Dm Φ
         (rowcast (width-subst (unfold₁-inst τ' (μ τ₀)) w) Rin)
... | mvO , (k , Φ' , S') =
  roll (mvcast (unfold₁-inst τ' σr) mvO) ,
  (k , Φ' , rowcast (sym (width-subst (unfold₁-inst τ' σr) w')) S')
