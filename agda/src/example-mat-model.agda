{-# OPTIONS --postfix-projections --prop --safe #-}

module example-mat-model where

open import Level using (0ℓ; lift)
open import Data.Unit using (tt)
open import indexed-family using (module _⇒f_; module Fam)
open Fam using (fm)
open import categories using (Category; HasInitial; HasProducts; HasTerminal)
open import cmon-enriched using (biproducts→products)
import cmon-enriched as CMon

open import ho-model using (module MatRep)
module Mat = Category MatRep.cat
open Mat using (≈-refl; ≈-sym; ≈-trans; ∘-cong; id-left; id-right; assoc)

products-mat = biproducts→products MatRep.cmon MatRep.biproduct

open HasProducts products-mat using (prod; p₁; p₂; pair-cong; pair-p₁; pair-p₂; pair-natural; pair-ext; prod-m; pair-compose) renaming (pair to pairM)
open CMon.CMonEnriched MatRep.cmon using (_+m_)

unit-mor : HasTerminal.witness MatRep.terminal Mat.⇒ 1
unit-mor = HasInitial.from-initial MatRep.initial {1}

conjunct : prod 1 1 Mat.⇒ 1
conjunct = _+m_ {x = prod 1 1} {y = 1} (p₁ {1} {1}) (p₂ {1} {1})

open import example-signature-interpretation
  MatRep.cat products-mat MatRep.terminal 1 unit-mor conjunct public
    hiding (_⇒_; _∘_; id)
open Category Fam⟨𝒞⟩.cat using () renaming (_⇒_ to _⇒f_; _∘_ to _∘f_; id to idf)
open Mat using (_⇒_; _∘_; id; _≈_)

-- Trace-side op-ℛ: 𝒞-level morphism `list→product ⟦sort⟧-𝒞 is ⇒ ⟦sort⟧-𝒞 o`. BaseInterp's `⟦op⟧`
-- is the Fam-wrapped equivalent. For sorts the two interpretations collapse to ⟦sort⟧-𝒞.
open import signature using (FPCat; FPC[_,_,_])
open FPCat (FPC[ MatRep.cat , MatRep.terminal , products-mat ]) using (list→product)

op-ℛ : ∀ {is o} (ω : op is o) → list→product ⟦sort⟧-𝒞 is ⇒ ⟦sort⟧-𝒞 o
op-ℛ op-zero = unit-mor
op-ℛ add     = conjunct
op-ℛ mult    = conjunct
op-ℛ (lbl _) = id 0

------------------------------------------------------------------------
-- Edge type and matrix decoder.

open import Data.Fin using (Fin; toℕ)
open import Data.List using (List; []; _∷_; map; concatMap; concat; length; _++_; splitAt; applyUpTo; allFin)
open import Data.Product using (_,_; proj₁; proj₂; _×_)
open import Data.String using (String) renaming (_++_ to _++ˢ_)
open import Data.Nat using (ℕ; zero; suc; _+_)
import two
open two using (Two; O; I)
import matrix
open matrix.Mat two.semiring using () renaming (Matrix to TwoMatrix)

Edge : Set
Edge = String × ℕ × ℕ

matrix-entries : ∀ {m n} → TwoMatrix m n → List (Fin m × Fin n)
matrix-entries {m} {n} M' =
  concatMap (λ i → concatMap (λ j → keep i j (M' i j)) (allFin n)) (allFin m)
  where
    keep : Fin m → Fin n → Two → List (Fin m × Fin n)
    keep i j I = (i , j) ∷ []
    keep i j O = []

open Fam⟨𝒞⟩.Obj using (idx; fam) public
open Fam⟨𝒞⟩.Mor using (idxf; famf) public

module FamP = HasProducts (Fam⟨𝒞⟩.products.products products-mat)

------------------------------------------------------------------------
-- Operational denotation: a derivation tree where each node carries a MatRep.cat morphism — its local
-- dependency relation.

open import every using (Every; []; _∷_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
import Data.Nat.Show as ℕ-Show
open import prop-setoid using (Setoid; IsEquivalence)
open Setoid using (Carrier)
open prop-setoid._⇒_ using (func)

open import categories using (HasTerminal)
open HasTerminal MatRep.terminal using (to-terminal)

open import example-signature using (Alg) public
open signature.Algebra Alg using (op-fun; rel-pred)
open import language-fo-evaluation Sig Alg public

-- Per-sort value tuple matching `list→product` on sorts. Operational, from Algebra.
Bases-input : List sort → Set
Bases-input = signature.sort-vals (example-signature.sort-val)

width : ∀ τ → Val τ → ℕ
width unit         _         = 0
width (base s)     _         = ⟦sort⟧-𝒞 s
width (τ₁ [×] τ₂)  (v , u) = width τ₁ v + width τ₂ u
width (τ₁ [+] τ₂)  (inj₁ v)  = width τ₁ v
width (τ₁ [+] τ₂)  (inj₂ v)  = width τ₂ v
width (list τ)     []        = 0
width (list τ)     (v ∷ vs)  = width τ v + width (list τ) vs

width-ctxt : ∀ Γ → Env Γ → ℕ
width-ctxt emp       _       = 0
width-ctxt (Γ · τ)  (γ , v) = width-ctxt Γ γ + width τ v

proj-var : ∀ {Γ τ} (x : Γ ∋ τ) (γ : Env Γ) → width-ctxt Γ γ ⇒ width τ (lookup x γ)
proj-var {Γ · τ} zero (γ , v) = p₂ {width-ctxt Γ γ} {width τ v}
proj-var {Γ · τ'} {τ} (succ x) (γ , v) =
  _∘_ {x = width-ctxt Γ γ + width τ' v} {y = width-ctxt Γ γ} {z = width τ (lookup x γ)}
      (proj-var x γ) (p₁ {width-ctxt Γ γ} {width τ' v})

-- Both branches of `unit [+] unit` have width 0, so this is essentially `to-terminal`
-- with its codomain expressed at the abstract `width (unit [+] unit) v` type. Pattern matching
-- on v lets Agda see width-reduction for each branch.
brel-rel : ∀ {Γ} (γ : Env Γ) (v : Val (unit [+] unit)) → width-ctxt Γ γ ⇒ width (unit [+] unit) v
brel-rel {Γ} γ (inj₁ _) = to-terminal {width-ctxt Γ γ}
brel-rel {Γ} γ (inj₂ _) = to-terminal {width-ctxt Γ γ}

------------------------------------------------------------------------
-- Big=step operational semantics: each Eval node carries the per-step MatRep dependency
-- relation as a type index.
data _,_⇓_,_ : ∀ {Γ τ} (γ : Env Γ) (M : Γ ⊢ τ) (v : Val τ) (ℛ : width-ctxt Γ γ ⇒ width τ v) → Set 0ℓ
infix 4 _,_⇓_,_
data EvalBases {Γ : ctxt} (γ : Env Γ) : ∀ {σs} (Ms : Every (λ σ → Γ ⊢ base σ) σs)
               (vs : Bases-input σs) (ℛ : width-ctxt Γ γ ⇒ list→product ⟦sort⟧-𝒞 σs) → Set 0ℓ
data EvalIters {Γ : ctxt} {τ₁ τ₂ : type} (M₁ : Γ ⊢ τ₂) (M₂ : (Γ · τ₁) · τ₂ ⊢ τ₂)
               (γ : Env Γ) (v-nil : Val τ₂) (ℛ : width-ctxt Γ γ ⇒ width τ₂ v-nil) :
               (ys : Val (list τ₁)) (final : Val τ₂) (𝒮 : width-ctxt Γ γ ⇒ width (list τ₁) ys)
               (ℛ₂ : width-ctxt Γ γ ⇒ width τ₂ final) → Set 0ℓ

data _,_⇓_,_ where

  eval-var   : ∀ {Γ τ} (x : Γ ∋ τ) (γ : Env Γ) → γ , var x ⇓ lookup x γ , (proj-var x γ)

  eval-unit  : ∀ {Γ} {γ : Env Γ} → γ , unit {Γ} ⇓ lift tt , to-terminal {width-ctxt Γ γ}
  eval-nil   : ∀ {Γ τ} {γ : Env Γ} → γ , nil {Γ} {τ} ⇓ [] , to-terminal {width-ctxt Γ γ}

  eval-pair  : ∀ {Γ τ₁ τ₂} {M : Γ ⊢ τ₁} {N : Γ ⊢ τ₂} {γ : Env Γ} {v u ℛ₁ ℛ₂} →
               γ , M ⇓ v , ℛ₁ → γ , N ⇓ u , ℛ₂ →
               γ , pair M N ⇓ (v , u) , pairM {x = width-ctxt Γ γ} {y = width τ₁ v} {z = width τ₂ u} ℛ₁ ℛ₂

  eval-fst   : ∀ {Γ τ₁ τ₂} {M : Γ ⊢ τ₁ [×] τ₂} {γ : Env Γ} {v u ℛ} →
               γ , M ⇓ (v , u) , ℛ →
               γ , fst M ⇓ v ,
                     (_∘_ {x = width-ctxt Γ γ} {y = width τ₁ v + width τ₂ u} {z = width τ₁ v}
                              (p₁ {width τ₁ v} {width τ₂ u}) ℛ)
  eval-snd   : ∀ {Γ τ₁ τ₂} {M : Γ ⊢ τ₁ [×] τ₂} {γ : Env Γ} {v u ℛ} →
               γ , M ⇓ (v , u) , ℛ →
               γ , snd M ⇓ u ,
                     (_∘_ {x = width-ctxt Γ γ} {y = width τ₁ v + width τ₂ u} {z = width τ₂ u}
                              (p₂ {width τ₁ v} {width τ₂ u}) ℛ)

  eval-inl   : ∀ {Γ τ₁ τ₂} {M : Γ ⊢ τ₁} {γ : Env Γ} {v ℛ} → γ , M ⇓ v , ℛ → γ , inl {τ₂ = τ₂} M ⇓ inj₁ v , ℛ
  eval-inr   : ∀ {Γ τ₁ τ₂} {M : Γ ⊢ τ₂} {γ : Env Γ} {v ℛ} → γ , M ⇓ v , ℛ → γ , inr {τ₁ = τ₁} M ⇓ inj₂ v , ℛ

  eval-cons  : ∀ {Γ τ} {M : Γ ⊢ τ} {N : Γ ⊢ list τ} {γ : Env Γ} {v u ℛ₁ ℛ₂} →
               γ , M ⇓ v , ℛ₁ → γ , N ⇓ u , ℛ₂ →
               γ , cons M N ⇓ (v ∷ u) , pairM {x = width-ctxt Γ γ} {y = width τ v} {z = width (list τ) u} ℛ₁ ℛ₂

  eval-case-l : ∀ {Γ τ₁ τ₂ τ} {M : Γ ⊢ τ₁ [+] τ₂} {N₁ : Γ · τ₁ ⊢ τ} {N₂ : Γ · τ₂ ⊢ τ}
                {γ : Env Γ} {v u ℛ 𝒮} → γ , M ⇓ inj₁ v , ℛ → (γ , v) , N₁ ⇓ u , 𝒮 →
                γ , case M N₁ N₂ ⇓ u ,
                    (_∘_ {x = width-ctxt Γ γ} {y = width-ctxt Γ γ + width τ₁ v} {z = width τ u}
                        𝒮 (pairM {x = width-ctxt Γ γ} {y = width-ctxt Γ γ} {z = width τ₁ v}
                                  (id (width-ctxt Γ γ)) ℛ))
  eval-case-r : ∀ {Γ τ₁ τ₂ τ} {M : Γ ⊢ τ₁ [+] τ₂} {N₁ : Γ · τ₁ ⊢ τ} {N₂ : Γ · τ₂ ⊢ τ}
                {γ : Env Γ} {v u ℛ 𝒮} → γ , M ⇓ inj₂ v , ℛ → (γ , v) , N₂ ⇓ u , 𝒮 →
                γ , case M N₁ N₂ ⇓ u ,
                    (_∘_ {x = width-ctxt Γ γ} {y = width-ctxt Γ γ + width τ₂ v} {z = width τ u}
                        𝒮 (pairM {x = width-ctxt Γ γ} {y = width-ctxt Γ γ} {z = width τ₂ v}
                                  (id (width-ctxt Γ γ)) ℛ))

  -- bop's morphism is the model's op composed with the stacked subterms' morphism.
  eval-bop   : ∀ {Γ is o} {Ms : Every (λ σ → Γ ⊢ base σ) is} {γ : Env Γ} {vs ℛ}
               (ω : op is o) → EvalBases γ Ms vs ℛ →
               γ , bop ω Ms ⇓ op-fun ω vs ,
                   _∘_ {x = width-ctxt Γ γ} {y = list→product ⟦sort⟧-𝒞 is} {z = ⟦sort⟧-𝒞 o} (op-ℛ ω) ℛ
  -- brel's output has width 0; morphism collapses to the terminal.
  eval-brel  : ∀ {Γ is} {Ms : Every (λ σ → Γ ⊢ base σ) is} {γ : Env Γ} {vs ℛ}
               (ω : rel is) → EvalBases γ Ms vs ℛ →
               γ , brel ω Ms ⇓ rel-pred ω vs , brel-rel γ (rel-pred ω vs)

  -- fold: the iter chain accumulates the final morphism from seed (M₁'s) and list (M's).
  eval-fold  : ∀ {Γ τ₁ τ₂} {M₁ : Γ ⊢ τ₂} {M₂ : (Γ · τ₁) · τ₂ ⊢ τ₂} {M : Γ ⊢ list τ₁}
               {γ : Env Γ} {v-nil ys final ℛ 𝒮 ℛ₂} →
               γ , M₁ ⇓ v-nil , ℛ →
               γ , M ⇓ ys , 𝒮 → EvalIters M₁ M₂ γ v-nil ℛ ys final 𝒮 ℛ₂ → γ , fold M₁ M₂ M ⇓ final , ℛ₂

data EvalBases {Γ} γ where
  []-bases  : EvalBases γ [] (lift tt) (to-terminal {width-ctxt Γ γ})
  _∷-bases_ : ∀ {σ is} {M : Γ ⊢ base σ} {Ms : Every (λ σ → Γ ⊢ base σ) is}
              {v vs ℛ₁ ℛ₂} → γ , M ⇓ v , ℛ₁ → EvalBases γ Ms vs ℛ₂ →
              EvalBases γ (M ∷ Ms) (v , vs)
                        (pairM {x = width-ctxt Γ γ} {y = ⟦sort⟧-𝒞 σ} {z = list→product ⟦sort⟧-𝒞 is} ℛ₁ ℛ₂)

data EvalIters {Γ} {τ₁} {τ₂} M₁ M₂ γ v-nil ℛ where
  nil-iter  : ∀ {𝒮} → EvalIters M₁ M₂ γ v-nil ℛ [] v-nil 𝒮 ℛ
  cons-iter : ∀ {y ys acc-rest acc-this ℛ₃ 𝒮₂}
              (𝒮 : width-ctxt Γ γ ⇒ (width τ₁ y + width (list τ₁) ys)) →
              EvalIters M₁ M₂ γ v-nil ℛ ys acc-rest
                           (_∘_ {x = width-ctxt Γ γ} {y = width τ₁ y + width (list τ₁) ys} {z = width (list τ₁) ys}
                                (p₂ {width τ₁ y} {width (list τ₁) ys}) 𝒮) ℛ₃ →
              ((γ , y) , acc-rest) , M₂ ⇓ acc-this , 𝒮₂ →
              EvalIters M₁ M₂ γ v-nil ℛ (y ∷ ys) acc-this 𝒮
                           (_∘_ {x = width-ctxt Γ γ} {y = (width-ctxt Γ γ + width τ₁ y) + width τ₂ acc-rest}
                                {z = width τ₂ acc-this} 𝒮₂
                                (pairM {x = width-ctxt Γ γ} {y = width-ctxt Γ γ + width τ₁ y}
                                       {z = width τ₂ acc-rest}
                                       (pairM {x = width-ctxt Γ γ} {y = width-ctxt Γ γ} {z = width τ₁ y}
                                              (id (width-ctxt Γ γ))
                                              (_∘_ {x = width-ctxt Γ γ} {y = width τ₁ y + width (list τ₁) ys}
                                                   {z = width τ₁ y}
                                                   (p₁ {width τ₁ y} {width (list τ₁) ys}) 𝒮))
                                       ℛ₃))

------------------------------------------------------------------------
-- Eval is inhabited for every term.

open import Data.Product using (∃; ∃-syntax; -,_)

eval        : ∀ {Γ τ} (M : Γ ⊢ τ) (γ : Env Γ) → ∃[ v ] ∃[ ℛ ] γ , M ⇓ v , ℛ
eval-bases  : ∀ {Γ σs} (Ms : Every (λ σ → Γ ⊢ base σ) σs) (γ : Env Γ) → ∃[ vs ] ∃[ ℛ ] EvalBases γ Ms vs ℛ
build-iters : ∀ {Γ τ₁ τ₂} {M₁ : Γ ⊢ τ₂} (M₂ : (Γ · τ₁) · τ₂ ⊢ τ₂)
                {γ : Env Γ} (v-nil : Val τ₂) (ℛ : width-ctxt Γ γ ⇒ width τ₂ v-nil) (ys : Val (list τ₁))
                (𝒮 : width-ctxt Γ γ ⇒ width (list τ₁) ys) →
                ∃[ final ] ∃[ ℛ₂ ] EvalIters M₁ M₂ γ v-nil ℛ ys final 𝒮 ℛ₂

eval (var x) γ = -, -, eval-var x γ
eval unit  γ = -, -, eval-unit
eval nil   γ = -, -, eval-nil
eval (pair M N) γ =
  let _ , _ , E = eval M γ
      _ , _ , F = eval N γ
  in -, -, eval-pair E F
eval (fst M) γ with eval M γ
... | (_ , _) , _ , E = -, -, eval-fst E
eval (snd M) γ with eval M γ
... | (_ , _) , _ , E = -, -, eval-snd E
eval (inl M) γ = let _ , _ , E = eval M γ in -, -, eval-inl E
eval (inr M) γ = let _ , _ , E = eval M γ in -, -, eval-inr E
eval (case M N₁ N₂) γ with eval M γ
... | inj₁ v , _ , EM = let _ , _ , F = eval N₁ (γ , v) in -, -, eval-case-l EM F
... | inj₂ v , _ , EM = let _ , _ , F = eval N₂ (γ , v) in -, -, eval-case-r EM F
eval (cons M N) γ =
  let _ , _ , E = eval M γ
      _ , _ , F = eval N γ
  in -, -, eval-cons E F
eval (bop ω Ms)  γ = let _ , _ , E = eval-bases Ms γ in -, -, eval-bop  ω E
eval (brel ω Ms) γ = let _ , _ , E = eval-bases Ms γ in -, -, eval-brel ω E
eval (fold M₁ M₂ M) γ =
  let v-nil   , ℛ , E₁ = eval M₁ γ
      ys      , 𝒮 , E₂ = eval M γ
      _ , _ , E₃ = build-iters M₂ v-nil ℛ ys 𝒮
  in -, -, eval-fold E₁ E₂ E₃

eval-bases [] γ = -, -, []-bases
eval-bases (M ∷ Ms) γ =
  let _ , _ , E  = eval M γ
      _ , _ , Es = eval-bases Ms γ
  in -, -, E ∷-bases Es

build-iters M₂ v-nil ℛ [] 𝒮 = -, -, nil-iter
build-iters {Γ = Γ} {τ₁ = τ₁} M₂ v-nil ℛ (y ∷ ys) 𝒮 =
  let m   = width-ctxt Γ _
      n-h = width τ₁ y
      n-t = width (list τ₁) ys
      𝒮ₜ = _∘_ {x = m} {y = n-h + n-t} {z = n-t} (p₂ {n-h} {n-t}) 𝒮
      _ , _ , rec = build-iters M₂ v-nil ℛ ys 𝒮ₜ
      _ , _ , F   = eval M₂ ((_ , y) , _)
  in -, -, cons-iter 𝒮 rec F

------------------------------------------------------------------------
-- Trace → edge list (the dependence graph).

open import functor using (Functor)
open Functor using (fobj; fmor; fmor-cong; fmor-id; fmor-comp)

private
  nth : List ℕ → ℕ → ℕ
  nth [] _              = 0
  nth (x ∷ _)  zero     = x
  nth (_ ∷ xs) (suc i)  = nth xs i

  mat-edges : String → (m n : ℕ) → m ⇒ n → List ℕ → List ℕ → List Edge
  mat-edges tag m n f ins outs =
    map (λ p → _,_ tag (_,_ (nth ins (toℕ (proj₂ p))) (nth outs (toℕ (proj₁ p)))))
        (matrix-entries {n} {m} (MatRep.F⁻¹ .fmor f))

  -- State ℕ for fresh port ids + writer for emitted edges.
  GraphWriter : Set → Set
  GraphWriter A = ℕ → A × ℕ × List Edge

  return : ∀ {A} → A → GraphWriter A
  return a next = a , next , []

  _>>=_ : ∀ {A B} → GraphWriter A → (A → GraphWriter B) → GraphWriter B
  (m >>= k) next =
    let a , next₁ , es₁ = m next
        b , next₂ , es₂ = k a next₁
    in b , next₂ , es₁ ++ es₂

  _>>_ : ∀ {A B} → GraphWriter A → GraphWriter B → GraphWriter B
  m >> n = m >>= λ _ → n

  -- Allocate n fresh output ports, emit `mat-edges tag m n r ins outs`, return outs.
  emit : String → (m n : ℕ) → m ⇒ n → List ℕ → GraphWriter (List ℕ)
  emit tag m n r ins next =
    let outs = applyUpTo (next +_) n
    in outs , next + n , mat-edges tag m n r ins outs


------------------------------------------------------------------------
-- Edge-list rendering.

open import Data.String using (intersperse)

showGraph : List Edge → String
showGraph es = intersperse ", " (map edge es)
  where
    edge : Edge → String
    edge (tag , i , j) =
      "(" ++ˢ tag ++ˢ ": " ++ˢ ℕ-Show.show i ++ˢ ", " ++ˢ ℕ-Show.show j ++ˢ ")"

showDot : List Edge → String
showDot es = "digraph G {\n" ++ˢ go es ++ˢ "}\n"
  where
    edge : Edge → String
    edge (tag , i , j) =
      "  " ++ˢ ℕ-Show.show i ++ˢ " -> " ++ˢ ℕ-Show.show j ++ˢ " [label=\"" ++ˢ tag ++ˢ "\"];\n"
    go : List Edge → String
    go []       = ""
    go (e ∷ es) = edge e ++ˢ go es


------------------------------------------------------------------------
-- Eval → edges. Migrated version of the Trace-based edges. Each clause derives the local m, n, r
-- from the constructor's value indices and the corresponding categorical primitive.

-- The Eval r-index is the *composed* env-to-output morphism. For edges we want the *local*
-- per-constructor effect (e.g. p₁ for fst, id for pair) so that node edges connect the immediate
-- inputs (children outputs) to outputs. The local r is recoverable per-constructor from the indices.
edges        : ∀ {Γ τ} {M : Γ ⊢ τ} {γ : Env Γ} {v ℛ} → γ , M ⇓ v , ℛ → List ℕ → GraphWriter (List ℕ)
edges-bases  : ∀ {Γ σs Ms γ vs ℛ} → EvalBases {Γ} γ {σs} Ms vs ℛ → List ℕ →
               GraphWriter (List ℕ)
edges-iters  : ∀ {Γ τ₁ τ₂ M₁ M₂ γ v-nil ℛ ys final 𝒮 ℛ₂} →
               EvalIters {Γ} {τ₁} {τ₂} M₁ M₂ γ v-nil ℛ ys final 𝒮 ℛ₂ →
               List ℕ → List ℕ → List ℕ → GraphWriter (List ℕ)

edges {Γ = Γ} {τ = τ} (eval-var x γ) ctx =
  emit "var" (width-ctxt Γ γ) (width τ (lookup x γ)) (proj-var x γ) ctx
edges eval-unit  _ = emit "unit"  0 0 (id 0) []
edges eval-nil   _ = emit "nil"   0 0 (id 0) []
edges (eval-fst {τ₁ = τ₁} {τ₂ = τ₂} {v = v} {u = u} E) ctx = do
  let n₁ = width τ₁ v; n₂ = width τ₂ u
  Eₒ ← edges E ctx
  emit "fst" (n₁ + n₂) n₁ (p₁ {n₁} {n₂}) Eₒ
edges (eval-snd {τ₁ = τ₁} {τ₂ = τ₂} {v = v} {u = u} E) ctx = do
  let n₁ = width τ₁ v; n₂ = width τ₂ u
  Eₒ ← edges E ctx
  emit "snd" (n₁ + n₂) n₂ (p₂ {n₁} {n₂}) Eₒ
edges (eval-inl {τ₁ = τ₁} {v = v} E) ctx = do
  let n = width τ₁ v
  Eₒ ← edges E ctx
  emit "inl" n n (id n) Eₒ
edges (eval-inr {τ₂ = τ₂} {v = v} E) ctx = do
  let n = width τ₂ v
  Eₒ ← edges E ctx
  emit "inr" n n (id n) Eₒ
edges (eval-pair {τ₁ = τ₁} {τ₂ = τ₂} {v = v} {u = u} E F) ctx = do
  let n = width τ₁ v + width τ₂ u
  Eₒ ← edges E ctx
  Fₒ ← edges F ctx
  emit "pair" n n (id n) (Eₒ ++ Fₒ)
edges (eval-cons {τ = τ} {v = v} {u = u} E F) ctx = do
  let n = width τ v + width (list τ) u
  Eₒ ← edges E ctx
  Fₒ ← edges F ctx
  emit "cons" n n (id n) (Eₒ ++ Fₒ)
edges (eval-case-l {τ₁ = τ₁} {τ = τ} {v = v} {u = u} E F) ctx = do
  let n₁ = width τ₁ v; n₂ = width τ u
  Eₒ ← edges E ctx
  Fₒ ← edges F (ctx ++ Eₒ)
  emit "case-l" (n₁ + n₂) n₂ (p₂ {n₁} {n₂}) (Eₒ ++ Fₒ)
edges (eval-case-r {τ₂ = τ₂} {τ = τ} {v = v} {u = u} E F) ctx = do
  let n₁ = width τ₂ v; n₂ = width τ u
  Eₒ ← edges E ctx
  Fₒ ← edges F (ctx ++ Eₒ)
  emit "case-r" (n₁ + n₂) n₂ (p₂ {n₁} {n₂}) (Eₒ ++ Fₒ)
edges (eval-bop {is = is} {o = o} ω E) ctx = do
  let m = list→product ⟦sort⟧-𝒞 is; n = ⟦sort⟧-𝒞 o
  Eₒ ← edges-bases E ctx
  emit (show-op ω) m n (op-ℛ ω) Eₒ
edges (eval-brel {is = is} ω E) ctx = do
  let m = list→product ⟦sort⟧-𝒞 is
  Eₒ ← edges-bases E ctx
  emit "brel" m 0 (to-terminal {m}) Eₒ
edges (eval-fold {τ₂ = τ₂} {final = final} E₁ E₂ E₃) ctx = do
  let n = width τ₂ final
  Nₒ ← edges E₁ ctx
  Lₒ ← edges E₂ ctx
  Tsₒ ← edges-iters E₃ Lₒ Nₒ ctx
  emit "fold" n n (id n) Tsₒ

edges-bases []-bases       _   = return []
edges-bases (E ∷-bases Es) ctx = do
  Eₒ ← edges E ctx
  Esₒ ← edges-bases Es ctx
  return (Eₒ ++ Esₒ)

edges-iters nil-iter _ seed _ = return seed
edges-iters {τ₁ = τ₁} (cons-iter {y = y} _ rec F) lₒ seed ctx = do
  let e , l-rest = splitAt (width τ₁ y) lₒ
  inner-acc ← edges-iters rec l-rest seed ctx
  edges F (ctx ++ e ++ inner-acc)

dependence-graph : ∀ {Γ τ} (M : Γ ⊢ τ) → Env Γ → List Edge
dependence-graph {Γ} M γ =
  let ctx = fresh-ctxt Γ γ 0
      _ , _ , es = edges (proj₂ (proj₂ (eval M γ))) ctx (width-ctxt Γ γ)
  in es
  where
    fresh-ctxt : ∀ Γ → Env Γ → ℕ → List ℕ
    fresh-ctxt emp _ _ = []
    fresh-ctxt (Γ · τ) (γ , v) next =
      let cxt = fresh-ctxt Γ γ next
          this-start = next + width-ctxt Γ γ
      in cxt ++ applyUpTo (this-start +_) (width τ v)

------------------------------------------------------------------------
-- Eval pretty-printing (ignores morphism index; mirrors the structural shape).

show-eval        : ∀ {Γ τ} {M : Γ ⊢ τ} {γ : Env Γ} {v ℛ} → γ , M ⇓ v , ℛ → String
show-eval-bases  : ∀ {Γ σs Ms γ vs ℛ} → EvalBases {Γ} γ {σs} Ms vs ℛ → List String
show-eval-iters  : ∀ {Γ τ₁ τ₂ M₁ M₂ γ v-nil ℛ ys final 𝒮 ℛ₂} →
                     EvalIters {Γ} {τ₁} {τ₂} M₁ M₂ γ v-nil ℛ ys final 𝒮 ℛ₂ → List String

show-eval (eval-var x _)        = "(var " ++ˢ ℕ-Show.show (var-to-ℕ x) ++ˢ ")"
show-eval eval-unit             = "unit"
show-eval (eval-inl t)          = "(inl " ++ˢ show-eval t ++ˢ ")"
show-eval (eval-inr t)          = "(inr " ++ˢ show-eval t ++ˢ ")"
show-eval (eval-case-l s b)     = "(case-l " ++ˢ show-eval s ++ˢ " " ++ˢ show-eval b ++ˢ ")"
show-eval (eval-case-r s b)     = "(case-r " ++ˢ show-eval s ++ˢ " " ++ˢ show-eval b ++ˢ ")"
show-eval (eval-pair a b)       = "(pair " ++ˢ show-eval a ++ˢ " " ++ˢ show-eval b ++ˢ ")"
show-eval (eval-fst t)          = "(fst " ++ˢ show-eval t ++ˢ ")"
show-eval (eval-snd t)          = "(snd " ++ˢ show-eval t ++ˢ ")"
show-eval (eval-bop ω ts)       = "(bop " ++ˢ show-op ω ++ˢ " (" ++ˢ intersperse " " (show-eval-bases ts) ++ˢ "))"
show-eval (eval-brel _ ts)      = "(brel (" ++ˢ intersperse " " (show-eval-bases ts) ++ˢ "))"
show-eval eval-nil              = "nil"
show-eval (eval-cons h t)       = "(cons " ++ˢ show-eval h ++ˢ " " ++ˢ show-eval t ++ˢ ")"
show-eval (eval-fold n l its)   =
  "(fold " ++ˢ show-eval n ++ˢ " " ++ˢ show-eval l ++ˢ " (" ++ˢ
  intersperse " " (show-eval-iters its) ++ˢ "))"

show-eval-bases []-bases       = []
show-eval-bases (t ∷-bases ts) = show-eval t ∷ show-eval-bases ts

show-eval-iters nil-iter            = []
show-eval-iters (cons-iter _ rec b) = show-eval b ∷ show-eval-iters rec

private
  indent : ℕ → String
  indent zero    = ""
  indent (suc n) = "  " ++ˢ indent n

pp-eval        : ℕ → ∀ {Γ τ} {M : Γ ⊢ τ} {γ : Env Γ} {v ℛ} → γ , M ⇓ v , ℛ → String
pp-eval-bases  : ℕ → ∀ {Γ σs Ms γ vs ℛ} → EvalBases {Γ} γ {σs} Ms vs ℛ → String
pp-eval-iters  : ℕ → ∀ {Γ τ₁ τ₂ M₁ M₂ γ v-nil ℛ ys final 𝒮 ℛ₂} →
                   EvalIters {Γ} {τ₁} {τ₂} M₁ M₂ γ v-nil ℛ ys final 𝒮 ℛ₂ → String

pp-eval d (eval-var x _)       = indent d ++ˢ "var " ++ˢ ℕ-Show.show (var-to-ℕ x)
pp-eval d eval-unit            = indent d ++ˢ "unit"
pp-eval d (eval-inl t)         = indent d ++ˢ "inl\n" ++ˢ pp-eval (suc d) t
pp-eval d (eval-inr t)         = indent d ++ˢ "inr\n" ++ˢ pp-eval (suc d) t
pp-eval d (eval-case-l s b)    = indent d ++ˢ "case-l\n" ++ˢ pp-eval (suc d) s ++ˢ "\n" ++ˢ pp-eval (suc d) b
pp-eval d (eval-case-r s b)    = indent d ++ˢ "case-r\n" ++ˢ pp-eval (suc d) s ++ˢ "\n" ++ˢ pp-eval (suc d) b
pp-eval d (eval-pair a b)      = indent d ++ˢ "pair\n" ++ˢ pp-eval (suc d) a ++ˢ "\n" ++ˢ pp-eval (suc d) b
pp-eval d (eval-fst t)         = indent d ++ˢ "fst\n" ++ˢ pp-eval (suc d) t
pp-eval d (eval-snd t)         = indent d ++ˢ "snd\n" ++ˢ pp-eval (suc d) t
pp-eval d (eval-bop ω ts)      = indent d ++ˢ "bop " ++ˢ show-op ω ++ˢ pp-eval-bases (suc d) ts
pp-eval d (eval-brel _ ts)     = indent d ++ˢ "brel" ++ˢ pp-eval-bases (suc d) ts
pp-eval d eval-nil             = indent d ++ˢ "nil"
pp-eval d (eval-cons h t)      = indent d ++ˢ "cons\n" ++ˢ pp-eval (suc d) h ++ˢ "\n" ++ˢ pp-eval (suc d) t
pp-eval d (eval-fold n l its)  =
  indent d ++ˢ "fold\n" ++ˢ pp-eval (suc d) n ++ˢ "\n" ++ˢ pp-eval (suc d) l ++ˢ pp-eval-iters (suc d) its

pp-eval-bases d []-bases       = ""
pp-eval-bases d (t ∷-bases ts) = "\n" ++ˢ pp-eval d t ++ˢ pp-eval-bases d ts

pp-eval-iters d nil-iter            = ""
pp-eval-iters d (cons-iter _ rec b) = "\n" ++ˢ pp-eval d b ++ˢ pp-eval-iters d rec

show-eval-pretty : ∀ {Γ τ} {M : Γ ⊢ τ} {γ : Env Γ} {v ℛ} → γ , M ⇓ v , ℛ → String
show-eval-pretty = pp-eval zero

