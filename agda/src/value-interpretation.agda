{-# OPTIONS --prop --postfix-projections --safe #-}

-- The interpretation of values at first-order types: an index of the type's interpretation on the
-- first-order side of the higher-order model, and of environments over first-order contexts. A value
-- of a μ-type is a tree whose shape is read off the value at the unfolded type; that value is read
-- under a substitution of closed types for the type variables, so a nested μ-type extends the
-- substitution by its own unfolding and the sort environment by its own sort. The value of an index
-- is read off the tree the same way, so the interpretation is injective at first-order types.
open import Level using (0ℓ; lift)
open import Data.Nat using (ℕ; suc; _+_; _<_; s≤s)
open import Data.Nat.Properties using (≤-reflexive; <-trans; n<1+n; m≤m+n; m≤n+m)
open import Data.Nat.Induction using (<-wellFounded)
open import Induction.WellFounded using (Acc; acc)
open import Data.Fin using (Fin; zero; suc; splitAt; _↑ˡ_)
open import Data.Fin.Properties using (splitAt⁻¹-↑ˡ)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Product using (_,_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Binary.PropositionalEquality.Properties using (subst-subst-sym; subst-sym-subst)
open import prop-setoid using (Setoid)
open import commutative-semiring using (CommutativeSemiring)
open import signature using (Signature)
open import signature.interpretation using (Interpretation)
open import polynomial-functor using (Poly; extend)
import ho-model

module value-interpretation
  {A : Setoid 0ℓ 0ℓ} (S : CommutativeSemiring A) (elim-weight : Setoid.Carrier A)
  (Sig : Signature 0ℓ) (ℐ : Interpretation S Sig)
  where

open Interpretation ℐ using (sort-index)
open import language-syntax Sig renaming (_,_ to _▸_)
open import language-operational.type-substitution Sig using (sub-id; unfold-sub)
open import language-operational.evaluation Sig S ℐ elim-weight
  using (Val; Env; unit; const; inl; inr; pair; roll; emp; _·_; size; size-subst)

module model = ho-model S elim-weight
module interp = model.interp Sig ℐ
open interp using (∅𝒞; fo-as-poly; 𝒞⟦_⟧ty; 𝒞⟦_⟧ctxt)
open model.Fam⟨𝒞⟩μ using (idx; ∣_∣; Sort; mkSort; module Srt)
open Setoid using (Carrier)

private
  module T = model.Fam⟨𝒞⟩μ.Tree ∅𝒞

open T using (⟦_⟧shape; El; W; sup)

-- The values at the substituted variables, as elements of the sort environment, for values below a
-- size bound.
Compat : ∀ {n} → TySub (n + 0) 0 → (Fin n → Fin 0 ⊎ Sort 0) → ℕ → Set
Compat {n} σ η N = ∀ (j : Fin n) (u : Val (σ (j ↑ˡ 0))) → size u < N → El (η j)

extend-compat : ∀ {n} {σ : TySub (n + 0) 0} {η : Fin n → Fin 0 ⊎ Sort 0} {N} {ρ : type 0} {s} →
                ((u : Val ρ) → size u < N → El s) → Compat σ η N → Compat (extend σ ρ) (extend η s) N
extend-compat f₀ f zero    = f₀
extend-compat f₀ f (suc j) = f j

private
  Var : ∀ {n} → (Fin n ⊎ Fin 0) → Poly model.Fam⟨𝒞⟩μ.cat n
  Var s = [ Poly.var , (λ j → Poly.const (∅𝒞 j)) ] s

  shape-var : ∀ {n} (i : Fin (n + 0)) (σ : TySub (n + 0) 0) (η : Fin n → Fin 0 ⊎ Sort 0) (N : ℕ) →
              Compat σ η N → (v : Val (σ i)) → size v < N →
              (s : Fin n ⊎ Fin 0) → splitAt n i ≡ s → ⟦ ∣ Var s ∣ ⟧shape η
  shape-var i σ η N f v p (inj₁ j) eq =
    f j (subst Val (sym (cong σ (splitAt⁻¹-↑ˡ eq))) v) (subst (_< N) (sym (size-subst _ v)) p)
  shape-var i σ η N f v p (inj₂ ()) eq

-- A value at a first-order type under a substitution of closed types, as a shape of the type's
-- polynomial over a sort environment, given the values at the substituted variables. The bound lets
-- the body of a μ-type read the values at its own variable, which are smaller, by the same function.
shape-val : ∀ {n} {τ : type (n + 0)} (fo : first-order τ) (σ : TySub (n + 0) 0)
            (η : Fin n → Fin 0 ⊎ Sort 0) (N : ℕ) → Acc _<_ N → Compat σ η N →
            (v : Val (sub σ τ)) → size v < N → ⟦ ∣ fo-as-poly fo ∅𝒞 ∣ ⟧shape η
shape-val {n} (var i) σ η N a f v p = shape-var i σ η N f v p (splitAt n i) refl
shape-val unit σ η N a f unit p = lift tt
shape-val (base s) σ η N a f (const c) p = c
shape-val (fo₁ [+] fo₂) σ η N a f (inl v) p = inj₁ (shape-val fo₁ σ η N a f v (<-trans (n<1+n _) p))
shape-val (fo₁ [+] fo₂) σ η N a f (inr v) p = inj₂ (shape-val fo₂ σ η N a f v (<-trans (n<1+n _) p))
shape-val (fo₁ [×] fo₂) σ η N a f (pair v u) p =
  shape-val fo₁ σ η N a f v (<-trans (s≤s (m≤m+n (size v) (size u))) p) ,
  shape-val fo₂ σ η N a f u (<-trans (s≤s (m≤n+m (size u) (size v))) p)
shape-val (μ {τ = τ} fo) σ η N (acc rs) f (roll w) p =
  sup (shape-val fo (extend σ (μ B)) (extend η (inj₂ (mkSort ∣ fo-as-poly fo ∅𝒞 ∣ η)))
         (suc (size w)) (rs p)
         (extend-compat (shape-val (μ fo) σ η (suc (size w)) (rs p) (λ j u q → f j u (<-trans q p)))
                        (λ j u q → f j u (<-trans q p)))
         (subst Val (unfold-sub σ τ) w) (s≤s (≤-reflexive (size-subst (unfold-sub σ τ) w))))
  where B = sub (sub-lift σ) τ

⟦_⟧val : ∀ {τ : type 0} (fo : first-order τ) → Val τ → Carrier (𝒞⟦ fo ⟧ty ∅𝒞 .idx)
⟦ unit ⟧val unit = lift tt
⟦ base s ⟧val (const c) = c
⟦ fo₁ [+] fo₂ ⟧val (inl v) = inj₁ (⟦ fo₁ ⟧val v)
⟦ fo₁ [+] fo₂ ⟧val (inr v) = inj₂ (⟦ fo₂ ⟧val v)
⟦ fo₁ [×] fo₂ ⟧val (pair v u) = ⟦ fo₁ ⟧val v , ⟦ fo₂ ⟧val u
⟦ μ {τ = τ} fo ⟧val v =
  shape-val (μ fo) var (λ i → inj₁ i) (suc (size v')) (<-wellFounded _) (λ ()) v' (n<1+n _)
  where v' = subst Val (sym (sub-id (μ τ))) v

⟦_⟧env : ∀ {Γ} (Γ-fo : first-order-ctxt Γ) → Env Γ → Carrier (𝒞⟦ Γ-fo ⟧ctxt .idx)
⟦ emp ⟧env emp = lift tt
⟦ Γ-fo ▸ fo ⟧env (γ · v) = ⟦ Γ-fo ⟧env γ , ⟦ fo ⟧val v

mutual
  W-size : ∀ {k} {Q : Srt.Poly (suc k)} {ρ : Fin k → Fin 0 ⊎ Sort 0} → W Q ρ → ℕ
  W-size {Q = Q} {ρ} (sup x) = suc (shape-size Q (extend ρ (inj₂ (mkSort Q ρ))) x)

  shape-size : ∀ {k} (Q : Srt.Poly k) (η : Fin k → Fin 0 ⊎ Sort 0) → ⟦ Q ⟧shape η → ℕ
  shape-size (Poly.const S) η x        = 1
  shape-size (Poly.var j)   η x        = el-size (η j) x
  shape-size (P Poly.+ Q)   η (inj₁ x) = suc (shape-size P η x)
  shape-size (P Poly.+ Q)   η (inj₂ y) = suc (shape-size Q η y)
  shape-size (P Poly.× Q)   η (x , y)  = suc (shape-size P η x + shape-size Q η y)
  shape-size (Poly.μ Q)     η x        = W-size x

  el-size : (r : Fin 0 ⊎ Sort 0) → El r → ℕ
  el-size (inj₂ (mkSort Q ρ)) x = W-size x

Compat⁻¹ : ∀ {n} → TySub (n + 0) 0 → (Fin n → Fin 0 ⊎ Sort 0) → ℕ → Set
Compat⁻¹ {n} σ η N = ∀ (j : Fin n) (e : El (η j)) → el-size (η j) e < N → Val (σ (j ↑ˡ 0))

extend-compat⁻¹ : ∀ {n} {σ : TySub (n + 0) 0} {η : Fin n → Fin 0 ⊎ Sort 0} {N} {ρ : type 0} {s} →
                  ((e : El s) → el-size s e < N → Val ρ) → Compat⁻¹ σ η N →
                  Compat⁻¹ (extend σ ρ) (extend η s) N
extend-compat⁻¹ f₀ f zero    = f₀
extend-compat⁻¹ f₀ f (suc j) = f j

private
  val-var : ∀ {n} (i : Fin (n + 0)) (σ : TySub (n + 0) 0) (η : Fin n → Fin 0 ⊎ Sort 0) (N : ℕ) →
            Compat⁻¹ σ η N → (s : Fin n ⊎ Fin 0) → splitAt n i ≡ s →
            (x : ⟦ ∣ Var s ∣ ⟧shape η) → shape-size ∣ Var s ∣ η x < N → Val (σ i)
  val-var i σ η N f (inj₁ j) eq x p = subst Val (cong σ (splitAt⁻¹-↑ˡ eq)) (f j x p)
  val-var i σ η N f (inj₂ ()) eq x p

val-shape : ∀ {n} {τ : type (n + 0)} (fo : first-order τ) (σ : TySub (n + 0) 0)
            (η : Fin n → Fin 0 ⊎ Sort 0) (N : ℕ) → Acc _<_ N → Compat⁻¹ σ η N →
            (x : ⟦ ∣ fo-as-poly fo ∅𝒞 ∣ ⟧shape η) → shape-size ∣ fo-as-poly fo ∅𝒞 ∣ η x < N →
            Val (sub σ τ)
val-shape {n} (var i) σ η N a f x p = val-var i σ η N f (splitAt n i) refl x p
val-shape unit σ η N a f x p = unit
val-shape (base s) σ η N a f x p = const x
val-shape (fo₁ [+] fo₂) σ η N a f (inj₁ x) p = inl (val-shape fo₁ σ η N a f x (<-trans (n<1+n _) p))
val-shape (fo₁ [+] fo₂) σ η N a f (inj₂ y) p = inr (val-shape fo₂ σ η N a f y (<-trans (n<1+n _) p))
val-shape (fo₁ [×] fo₂) σ η N a f (x , y) p =
  pair (val-shape fo₁ σ η N a f x (<-trans (s≤s (m≤m+n _ _)) p))
       (val-shape fo₂ σ η N a f y (<-trans (s≤s (m≤n+m _ _)) p))
val-shape (μ {τ = τ} fo) σ η N (acc rs) f (sup x) p =
  roll (subst Val (sym (unfold-sub σ τ))
          (val-shape fo (extend σ (μ B)) η' (suc (shape-size P η' x)) (rs p)
             (extend-compat⁻¹ (val-shape (μ fo) σ η (suc (shape-size P η' x)) (rs p)
                                 (λ j e q → f j e (<-trans q p)))
                              (λ j e q → f j e (<-trans q p)))
             x (n<1+n _)))
  where
  B  = sub (sub-lift σ) τ
  P  = ∣ fo-as-poly fo ∅𝒞 ∣
  η' = extend η (inj₂ (mkSort P η))

⟦_⟧val⁻¹ : ∀ {τ : type 0} (fo : first-order τ) → Carrier (𝒞⟦ fo ⟧ty ∅𝒞 .idx) → Val τ
⟦ unit ⟧val⁻¹ i = unit
⟦ base s ⟧val⁻¹ c = const c
⟦ fo₁ [+] fo₂ ⟧val⁻¹ (inj₁ i) = inl (⟦ fo₁ ⟧val⁻¹ i)
⟦ fo₁ [+] fo₂ ⟧val⁻¹ (inj₂ j) = inr (⟦ fo₂ ⟧val⁻¹ j)
⟦ fo₁ [×] fo₂ ⟧val⁻¹ (i , j) = pair (⟦ fo₁ ⟧val⁻¹ i) (⟦ fo₂ ⟧val⁻¹ j)
⟦ μ {τ = τ} fo ⟧val⁻¹ t =
  subst Val (sub-id (μ τ))
    (val-shape (μ fo) var (λ i → inj₁ i) (suc (W-size t)) (<-wellFounded _) (λ ()) t (n<1+n _))

val-shape-val : ∀ {n} {τ : type (n + 0)} (fo : first-order τ) (σ : TySub (n + 0) 0)
  (η : Fin n → Fin 0 ⊎ Sort 0) {N N'} (a : Acc _<_ N) (a' : Acc _<_ N')
  (f : Compat σ η N') (f' : Compat⁻¹ σ η N) →
  (∀ j (u : Val (σ (j ↑ˡ 0))) (p : size u < N') (q : el-size (η j) (f j u p) < N) → f' j (f j u p) q ≡ u) →
  ∀ (v : Val (sub σ τ)) (p : size v < N')
    (q : shape-size ∣ fo-as-poly fo ∅𝒞 ∣ η (shape-val fo σ η N' a' f v p) < N) →
  val-shape fo σ η N a f' (shape-val fo σ η N' a' f v p) q ≡ v
val-shape-val {n} (var i) σ η a a' f f' inv v p q = go (splitAt n i) refl q
  where
  go : ∀ s eq (q' : shape-size ∣ Var s ∣ η (shape-var i σ η _ f v p s eq) < _) →
       val-var i σ η _ f' s eq (shape-var i σ η _ f v p s eq) q' ≡ v
  go (inj₁ j) eq q' = trans (cong (subst Val E) (inv j _ _ _)) (subst-subst-sym E)
    where E = cong σ (splitAt⁻¹-↑ˡ eq)
  go (inj₂ ()) eq q'
val-shape-val unit σ η a a' f f' inv unit p q = refl
val-shape-val (base s) σ η a a' f f' inv (const c) p q = refl
val-shape-val (fo₁ [+] fo₂) σ η a a' f f' inv (inl v) p q =
  cong inl (val-shape-val fo₁ σ η a a' f f' inv v _ _)
val-shape-val (fo₁ [+] fo₂) σ η a a' f f' inv (inr v) p q =
  cong inr (val-shape-val fo₂ σ η a a' f f' inv v _ _)
val-shape-val (fo₁ [×] fo₂) σ η a a' f f' inv (pair v u) p q =
  cong₂ pair (val-shape-val fo₁ σ η a a' f f' inv v _ _) (val-shape-val fo₂ σ η a a' f f' inv u _ _)
val-shape-val (μ {τ = τ} fo) σ η (acc rs) (acc rs') f f' inv (roll w) p q =
  trans (cong (λ y → roll (subst Val (sym E) y))
           (val-shape-val fo (extend σ (μ B)) η' (rs q) (rs' p) _ _ inv' (subst Val E w) _ _))
        (cong roll (subst-sym-subst E))
  where
  B  = sub (sub-lift σ) τ
  E  = unfold-sub σ τ
  η' = extend η (inj₂ (mkSort ∣ fo-as-poly fo ∅𝒞 ∣ η))
  inv' : ∀ j u p₀ q₀ → _ ≡ u
  inv' zero    u p₀ q₀ = val-shape-val (μ fo) σ η (rs q) (rs' p) _ _ (λ j u p q → inv j u _ _) u p₀ q₀
  inv' (suc j) u p₀ q₀ = inv j u _ _

⟦⟧val⁻¹-val : ∀ {τ : type 0} (fo : first-order τ) (v : Val τ) → ⟦ fo ⟧val⁻¹ (⟦ fo ⟧val v) ≡ v
⟦⟧val⁻¹-val unit unit = refl
⟦⟧val⁻¹-val (base s) (const c) = refl
⟦⟧val⁻¹-val (fo₁ [+] fo₂) (inl v) = cong inl (⟦⟧val⁻¹-val fo₁ v)
⟦⟧val⁻¹-val (fo₁ [+] fo₂) (inr v) = cong inr (⟦⟧val⁻¹-val fo₂ v)
⟦⟧val⁻¹-val (fo₁ [×] fo₂) (pair v u) = cong₂ pair (⟦⟧val⁻¹-val fo₁ v) (⟦⟧val⁻¹-val fo₂ u)
⟦⟧val⁻¹-val (μ {τ = τ} fo) v =
  trans (cong (subst Val (sub-id (μ τ)))
           (val-shape-val (μ fo) var (λ i → inj₁ i) {suc (W-size (⟦ μ fo ⟧val v))} {suc (size v')}
              (<-wellFounded _) (<-wellFounded _) (λ ()) (λ ()) (λ ()) v' (n<1+n _) (n<1+n _)))
        (subst-subst-sym {P = Val} (sub-id (μ τ)) {p = v})
  where v' = subst Val (sym (sub-id (μ τ))) v
