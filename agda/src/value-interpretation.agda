{-# OPTIONS --prop --postfix-projections --safe #-}

-- The interpretation of values at first-order types: an index of the type's interpretation on the
-- first-order side of the higher-order model, and of environments over first-order contexts. A value
-- of a μ-type is a tree whose shape is read off the value at the unfolded type; that value is read
-- under a substitution of closed types for the type variables, so a nested μ-type extends the
-- substitution by its own unfolding and the sort environment by its own sort. The value of an index
-- is read off the tree the same way, so the interpretation is injective at first-order types.
open import Level using (0ℓ; lift)
open import Data.Nat using (ℕ; suc; _+_; _<_; s≤s)
open import Data.Nat.Properties using (≤-reflexive; <-trans; <-irrelevant; n<1+n; m≤m+n; m≤n+m)
open import Data.Nat.Induction using (<-wellFounded)
open import Induction.WellFounded using (Acc; acc)
open import Data.Fin using (Fin; zero; suc; splitAt; _↑ˡ_)
open import Data.Fin.Properties using (splitAt⁻¹-↑ˡ; splitAt-↑ˡ; ↑ˡ-injective)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Product using (_,_; _×_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Binary.PropositionalEquality.Properties using (subst-subst-sym; subst-sym-subst; subst-subst)
open import prop-setoid using (Setoid)
open import commutative-semiring using (CommutativeSemiring)
open import signature using (Signature)
open import signature.interpretation using (Interpretation)
open import polynomial-functor using (Poly; extend)
import ho-model

module value-interpretation
  {A : Setoid 0ℓ 0ℓ} (S : CommutativeSemiring A) (ctrl-weight : Setoid.Carrier A)
  (Sig : Signature 0ℓ) (ℐ : Interpretation S Sig)
  where

open Interpretation ℐ using (sort-index)
open import language-syntax Sig renaming (_,_ to _▸_)
open import language-operational.type-substitution Sig using (sub-id; unfold-sub; sub-ren; ren-sub; sub-sub)
open import language-operational.evaluation Sig S ℐ ctrl-weight
  using (Val; Env; unit; const; inl; inr; pair; roll; emp; _·_; size; size-subst)

module model = ho-model S ctrl-weight
module interp = model.interp Sig ℐ
open interp using (∅𝒞; fo-as-poly; 𝒞⟦_⟧ty; 𝒞⟦_⟧ctxt)
open model.Fam⟨𝒞⟩μ using (idx; ∣_∣; Sort; mkSort; module Srt)
open Setoid using (Carrier)

private
  module T = model.Fam⟨𝒞⟩μ.Tree ∅𝒞

open T using (⟦_⟧shape; El; W; sup)

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

-- The size bound lets the body of a μ-type read the values at its own variable, which are smaller,
-- by the same function.
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

shape-val-irrelevant : ∀ {n} {τ : type (n + 0)} (fo : first-order τ) (σ : TySub (n + 0) 0)
                       (η : Fin n → Fin 0 ⊎ Sort 0) {N N'} (a : Acc _<_ N) (a' : Acc _<_ N')
                       (f : Compat σ η N) (f' : Compat σ η N') →
                       (∀ j (u : Val (σ (j ↑ˡ 0))) (p : size u < N) (q : size u < N') → f j u p ≡ f' j u q) →
                       ∀ (v : Val (sub σ τ)) (p : size v < N) (p' : size v < N') →
                       shape-val fo σ η N a f v p ≡ shape-val fo σ η N' a' f' v p'
shape-val-irrelevant {n} (var i) σ η a a' f f' hyp v p p' = go (splitAt n i) refl
  where
  go : ∀ s eq → shape-var i σ η _ f v p s eq ≡ shape-var i σ η _ f' v p' s eq
  go (inj₁ j) eq = hyp j _ _ _
  go (inj₂ ()) eq
shape-val-irrelevant unit σ η a a' f f' hyp unit p p' = refl
shape-val-irrelevant (base s) σ η a a' f f' hyp (const c) p p' = refl
shape-val-irrelevant (fo₁ [+] fo₂) σ η a a' f f' hyp (inl v) p p' =
  cong inj₁ (shape-val-irrelevant fo₁ σ η a a' f f' hyp v _ _)
shape-val-irrelevant (fo₁ [+] fo₂) σ η a a' f f' hyp (inr v) p p' =
  cong inj₂ (shape-val-irrelevant fo₂ σ η a a' f f' hyp v _ _)
shape-val-irrelevant (fo₁ [×] fo₂) σ η a a' f f' hyp (pair v u) p p' =
  cong₂ _,_ (shape-val-irrelevant fo₁ σ η a a' f f' hyp v _ _)
            (shape-val-irrelevant fo₂ σ η a a' f f' hyp u _ _)
shape-val-irrelevant (μ {τ = τ} fo) σ η (acc rs) (acc rs') f f' hyp (roll w) p p' =
  cong sup (shape-val-irrelevant fo (extend σ (μ B)) η' (rs p) (rs' p') _ _ hyp'
              (subst Val (unfold-sub σ τ) w) _ _)
  where
  B  = sub (sub-lift σ) τ
  η' = extend η (inj₂ (mkSort ∣ fo-as-poly fo ∅𝒞 ∣ η))
  hyp' : ∀ j u p₀ q₀ → _ ≡ _
  hyp' zero    u p₀ q₀ =
    shape-val-irrelevant (μ fo) σ η (rs p) (rs' p') _ _
      (λ j u₁ p₁ q₁ → hyp j u₁ (<-trans p₁ p) (<-trans q₁ p')) u p₀ q₀
  hyp' (suc j) u p₀ q₀ = hyp j u (<-trans p₀ p) (<-trans q₀ p')

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

-- Shapes translate along a renaming of the type variables, given a translation of the shape at
-- each variable. A μ node binds a new sort on each side, so there the per-variable translations
-- extend by the translation of whole trees at the bound sort. The renaming on the polynomial's
-- variables is carried separately, with a proof that the type-level renaming restricts to it.
data RenCompat : ∀ {n₁ n₂} → TyRen (n₁ + 0) (n₂ + 0) → TyRen n₁ n₂ →
                 (Fin n₁ → Fin 0 ⊎ Sort 0) → (Fin n₂ → Fin 0 ⊎ Sort 0) → Set₁ where
  rbase : ∀ {n₁ n₂} {ρ : TyRen (n₁ + 0) (n₂ + 0)} {ρ̂ : TyRen n₁ n₂}
          {η₁ : Fin n₁ → Fin 0 ⊎ Sort 0} {η₂ : Fin n₂ → Fin 0 ⊎ Sort 0} →
          (∀ j → El (η₁ j) → El (η₂ (ρ̂ j))) → (∀ j → ρ (j ↑ˡ 0) ≡ ρ̂ j ↑ˡ 0) →
          RenCompat ρ ρ̂ η₁ η₂
  rbind : ∀ {n₁ n₂} {ρ : TyRen (n₁ + 0) (n₂ + 0)} {ρ̂ : TyRen n₁ n₂}
          {η₁ : Fin n₁ → Fin 0 ⊎ Sort 0} {η₂ : Fin n₂ → Fin 0 ⊎ Sort 0}
          {τ : type (suc n₁ + 0)} (fo : first-order τ) → RenCompat ρ ρ̂ η₁ η₂ →
          RenCompat (extᵗ ρ) (extᵗ ρ̂)
                    (extend η₁ (inj₂ (mkSort ∣ fo-as-poly fo ∅𝒞 ∣ η₁)))
                    (extend η₂ (inj₂ (mkSort ∣ fo-as-poly (fo-ren {ρ = extᵗ ρ} fo) ∅𝒞 ∣ η₂)))

rcoh : ∀ {n₁ n₂} {ρ : TyRen (n₁ + 0) (n₂ + 0)} {ρ̂ : TyRen n₁ n₂}
       {η₁ : Fin n₁ → Fin 0 ⊎ Sort 0} {η₂ : Fin n₂ → Fin 0 ⊎ Sort 0} →
       RenCompat ρ ρ̂ η₁ η₂ → ∀ j → ρ (j ↑ˡ 0) ≡ ρ̂ j ↑ˡ 0
rcoh (rbase g coh) j      = coh j
rcoh (rbind fo r) zero    = refl
rcoh (rbind fo r) (suc j) = cong suc (rcoh r j)

mutual
  ren-tree : ∀ {n₁ n₂} {ρ : TyRen (n₁ + 0) (n₂ + 0)} {ρ̂ : TyRen n₁ n₂}
             {η₁ : Fin n₁ → Fin 0 ⊎ Sort 0} {η₂ : Fin n₂ → Fin 0 ⊎ Sort 0}
             {τ : type (suc n₁ + 0)} (fo : first-order τ) → RenCompat ρ ρ̂ η₁ η₂ →
             W ∣ fo-as-poly fo ∅𝒞 ∣ η₁ → W ∣ fo-as-poly (fo-ren {ρ = extᵗ ρ} fo) ∅𝒞 ∣ η₂
  ren-tree fo r (sup x) = sup (ren-shape fo (rbind fo r) x)

  ren-shape : ∀ {n₁ n₂} {ρ : TyRen (n₁ + 0) (n₂ + 0)} {ρ̂ : TyRen n₁ n₂}
              {η₁ : Fin n₁ → Fin 0 ⊎ Sort 0} {η₂ : Fin n₂ → Fin 0 ⊎ Sort 0}
              {τ : type (n₁ + 0)} (fo : first-order τ) → RenCompat ρ ρ̂ η₁ η₂ →
              ⟦ ∣ fo-as-poly fo ∅𝒞 ∣ ⟧shape η₁ → ⟦ ∣ fo-as-poly (fo-ren {ρ = ρ} fo) ∅𝒞 ∣ ⟧shape η₂
  ren-shape {n₁ = n₁} (var i) r x = ren-var r i (splitAt n₁ i) refl x
  ren-shape unit r x = x
  ren-shape (base s) r x = x
  ren-shape (fo₁ [+] fo₂) r (inj₁ x) = inj₁ (ren-shape fo₁ r x)
  ren-shape (fo₁ [+] fo₂) r (inj₂ y) = inj₂ (ren-shape fo₂ r y)
  ren-shape (fo₁ [×] fo₂) r (x , y) = ren-shape fo₁ r x , ren-shape fo₂ r y
  ren-shape (μ fo) r t = ren-tree fo r t

  ren-var : ∀ {n₁ n₂} {ρ : TyRen (n₁ + 0) (n₂ + 0)} {ρ̂ : TyRen n₁ n₂}
            {η₁ : Fin n₁ → Fin 0 ⊎ Sort 0} {η₂ : Fin n₂ → Fin 0 ⊎ Sort 0} →
            RenCompat ρ ρ̂ η₁ η₂ → (i : Fin (n₁ + 0)) (s : Fin n₁ ⊎ Fin 0) → splitAt n₁ i ≡ s →
            ⟦ ∣ Var s ∣ ⟧shape η₁ → ⟦ ∣ Var (splitAt n₂ (ρ i)) ∣ ⟧shape η₂
  ren-var {n₂ = n₂} {ρ = ρ} {ρ̂ = ρ̂} {η₂ = η₂} r i (inj₁ j) eq x =
    subst (λ s → ⟦ ∣ Var s ∣ ⟧shape η₂)
      (sym (trans (cong (splitAt n₂) (trans (sym (cong ρ (splitAt⁻¹-↑ˡ eq))) (rcoh r j)))
                  (splitAt-↑ˡ n₂ (ρ̂ j) 0)))
      (rapply r j x)
  ren-var r i (inj₂ ()) eq x

  rapply : ∀ {n₁ n₂} {ρ : TyRen (n₁ + 0) (n₂ + 0)} {ρ̂ : TyRen n₁ n₂}
           {η₁ : Fin n₁ → Fin 0 ⊎ Sort 0} {η₂ : Fin n₂ → Fin 0 ⊎ Sort 0} →
           RenCompat ρ ρ̂ η₁ η₂ → ∀ j → El (η₁ j) → El (η₂ (ρ̂ j))
  rapply (rbase g coh) j x = g j x
  rapply (rbind fo r) zero x = ren-tree fo r x
  rapply (rbind fo r) (suc j) x = rapply r j x

weaken-ren : ∀ {n} {η : Fin n → Fin 0 ⊎ Sort 0} {s : Fin 0 ⊎ Sort 0} → RenCompat suc suc η (extend η s)
weaken-ren = rbase (λ j x → x) (λ j → refl)

private
  uip : ∀ {A : Set} {x y : A} (p q : x ≡ y) → p ≡ q
  uip refl refl = refl

  subst-val-inl : ∀ {τ₁ τ₂ τ₁' τ₂' : type 0} (e₁ : τ₁ ≡ τ₁') (e₂ : τ₂ ≡ τ₂')
                  (E : (τ₁ [+] τ₂) ≡ (τ₁' [+] τ₂')) (v : Val τ₁) →
                  subst Val E (inl v) ≡ inl (subst Val e₁ v)
  subst-val-inl refl refl refl v = refl

  subst-val-inr : ∀ {τ₁ τ₂ τ₁' τ₂' : type 0} (e₁ : τ₁ ≡ τ₁') (e₂ : τ₂ ≡ τ₂')
                  (E : (τ₁ [+] τ₂) ≡ (τ₁' [+] τ₂')) (v : Val τ₂) →
                  subst Val E (inr v) ≡ inr (subst Val e₂ v)
  subst-val-inr refl refl refl v = refl

  subst-val-pair : ∀ {τ₁ τ₂ τ₁' τ₂' : type 0} (e₁ : τ₁ ≡ τ₁') (e₂ : τ₂ ≡ τ₂')
                   (E : (τ₁ [×] τ₂) ≡ (τ₁' [×] τ₂')) (v : Val τ₁) (u : Val τ₂) →
                   subst Val E (pair v u) ≡ pair (subst Val e₁ v) (subst Val e₂ u)
  subst-val-pair refl refl refl v u = refl

  subst-val-roll : ∀ {τ τ' : type 1} (e : τ ≡ τ') (E : μ τ ≡ μ τ') (w : Val (τ [ μ τ ])) →
                   subst Val E (roll w) ≡ roll (subst Val (cong (λ υ → υ [ μ υ ]) e) w)
  subst-val-roll refl refl w = refl

  shape-val-cast : ∀ {n} {τ : type (n + 0)} (fo : first-order τ) (σ : TySub (n + 0) 0)
                   (η : Fin n → Fin 0 ⊎ Sort 0) (N : ℕ) (a : Acc _<_ N) (f : Compat σ η N)
                   {v v' : Val (sub σ τ)} (e : v ≡ v') (p : size v < N) →
                   shape-val fo σ η N a f v p ≡ shape-val fo σ η N a f v' (subst (λ u → size u < N) e p)
  shape-val-cast fo σ η N a f refl p = refl

  app-cast : ∀ {X : type 0} {N : ℕ} {B : Set} (g : (u : Val X) → size u < N → B)
             {u u' : Val X} (e : u ≡ u') {p : size u < N} {p' : size u' < N} →
             subst (λ z → size z < N) e p ≡ p' → g u p ≡ g u' p'
  app-cast g refl refl = refl

-- shape-val commutes with the renaming translation: reading a value's shape at the renamed type gives
-- the translation of its shape at the original type, when the closing substitutions agree along the
-- renaming and the compatibility functions agree variablewise. The type-level transports are
-- quantified over arbitrary equality proofs, which uip reconciles at the leaves.
ren-shape-val :
  ∀ {n₁ n₂} {ρ : TyRen (n₁ + 0) (n₂ + 0)} {ρ̂ : TyRen n₁ n₂}
  {η₁ : Fin n₁ → Fin 0 ⊎ Sort 0} {η₂ : Fin n₂ → Fin 0 ⊎ Sort 0}
  {τ : type (n₁ + 0)} (fo : first-order τ) (r : RenCompat ρ ρ̂ η₁ η₂)
  (σ₁ : TySub (n₁ + 0) 0) (σ₂ : TySub (n₂ + 0) 0) (Eσ : ∀ i → σ₂ (ρ i) ≡ σ₁ i)
  {N N' : ℕ} (a : Acc _<_ N) (a' : Acc _<_ N') (f₁ : Compat σ₁ η₁ N) (f₂ : Compat σ₂ η₂ N') →
  (∀ j (u : Val (σ₂ (ρ̂ j ↑ˡ 0))) (q : size u < N') (Ej : σ₂ (ρ̂ j ↑ˡ 0) ≡ σ₁ (j ↑ˡ 0))
     (p : size (subst Val Ej u) < N) →
   f₂ (ρ̂ j) u q ≡ rapply r j (f₁ j (subst Val Ej u) p)) →
  ∀ (E : sub σ₂ (ρ *ᵗ τ) ≡ sub σ₁ τ) (v : Val (sub σ₂ (ρ *ᵗ τ))) (q : size v < N')
    (p : size (subst Val E v) < N) →
  shape-val (fo-ren {ρ = ρ} fo) σ₂ η₂ N' a' f₂ v q
    ≡ ren-shape fo r (shape-val fo σ₁ η₁ N a f₁ (subst Val E v) p)
ren-shape-val {n₁ = n₁} {n₂ = n₂} {ρ = ρ} {ρ̂ = ρ̂} {η₁ = η₁} {η₂ = η₂} (var i) r σ₁ σ₂ Eσ
              {N = N} {N' = N'} a a' f₁ f₂ hyp E v q p =
  go (splitAt n₁ i) refl (splitAt n₂ (ρ i)) refl
  where
  FAM : Fin n₂ ⊎ Fin 0 → Set
  FAM s = ⟦ ∣ Var s ∣ ⟧shape η₂

  go' : ∀ j (eq : splitAt n₁ i ≡ inj₁ j) j₂ (eq₂ : splitAt n₂ (ρ i) ≡ inj₁ j₂) → j₂ ≡ ρ̂ j →
        shape-var (ρ i) σ₂ η₂ N' f₂ v q (inj₁ j₂) eq₂
          ≡ subst FAM eq₂ (ren-var r i (inj₁ j) eq (shape-var i σ₁ η₁ N f₁ (subst Val E v) p (inj₁ j) eq))
  go' j eq .(ρ̂ j) eq₂ refl =
    trans (hyp j u₂ q₂ Ej p*)
          (trans (cong (rapply r j) (app-cast (f₁ j) e-u (subst-subst-sym e-u)))
                 (sym (trans (subst-subst PR)
                             (cong (λ h → subst FAM h (rapply r j (f₁ j u₁ p₁))) (uip (trans PR eq₂) refl)))))
    where
    E₂ = sym (cong σ₂ (splitAt⁻¹-↑ˡ eq₂))
    E₁ = sym (cong σ₁ (splitAt⁻¹-↑ˡ eq))
    u₂ = subst Val E₂ v
    q₂ = subst (_< N') (sym (size-subst E₂ v)) q
    Ej : σ₂ (ρ̂ j ↑ˡ 0) ≡ σ₁ (j ↑ˡ 0)
    Ej = trans (cong σ₂ (sym (rcoh r j)))
               (trans (cong (λ k → σ₂ (ρ k)) (splitAt⁻¹-↑ˡ eq)) (trans E (cong σ₁ (sym (splitAt⁻¹-↑ˡ eq)))))
    u₁ = subst Val E₁ (subst Val E v)
    p₁ = subst (_< N) (sym (size-subst E₁ (subst Val E v))) p
    e-u : subst Val Ej u₂ ≡ u₁
    e-u = trans (subst-subst E₂)
                (trans (cong (λ h → subst Val h v) (uip (trans E₂ Ej) (trans E E₁))) (sym (subst-subst E)))
    p* = subst (λ z → size z < N) (sym e-u) p₁
    PR = sym (trans (cong (splitAt n₂) (trans (sym (cong ρ (splitAt⁻¹-↑ˡ eq))) (rcoh r j)))
                    (splitAt-↑ˡ n₂ (ρ̂ j) 0))

  go : ∀ s (eq : splitAt n₁ i ≡ s) s₂ (eq₂ : splitAt n₂ (ρ i) ≡ s₂) →
       shape-var (ρ i) σ₂ η₂ N' f₂ v q s₂ eq₂
         ≡ subst FAM eq₂ (ren-var r i s eq (shape-var i σ₁ η₁ N f₁ (subst Val E v) p s eq))
  go (inj₁ j) eq (inj₁ j₂) eq₂ =
    go' j eq j₂ eq₂
      (↑ˡ-injective 0 j₂ (ρ̂ j)
        (trans (splitAt⁻¹-↑ˡ eq₂) (trans (cong ρ (sym (splitAt⁻¹-↑ˡ eq))) (rcoh r j))))
  go (inj₁ j) eq (inj₂ ()) eq₂
  go (inj₂ ()) eq s₂ eq₂
ren-shape-val {η₁ = η₁} unit r σ₁ σ₂ Eσ {N = N} a a' f₁ f₂ hyp E unit q p =
  sym (shape-val-cast unit σ₁ η₁ N a f₁ (cong (λ h → subst Val h unit) (uip E refl)) p)
ren-shape-val {η₁ = η₁} (base s) r σ₁ σ₂ Eσ {N = N} a a' f₁ f₂ hyp E (const c) q p =
  sym (shape-val-cast (base s) σ₁ η₁ N a f₁ (cong (λ h → subst Val h (const c)) (uip E refl)) p)
ren-shape-val {ρ = ρ} {η₁ = η₁} {τ = τ₁ [+] τ₂} (fo₁ [+] fo₂) r σ₁ σ₂ Eσ {N = N} a a' f₁ f₂ hyp E (inl v) q p =
  trans (cong inj₁ (ren-shape-val fo₁ r σ₁ σ₂ Eσ a a' f₁ f₂ hyp E₁ v (<-trans (n<1+n _) q)
                      (<-trans (n<1+n _) p̂)))
        (sym (cong (ren-shape (fo₁ [+] fo₂) r) (shape-val-cast (fo₁ [+] fo₂) σ₁ η₁ N a f₁ e-inl p)))
  where
  E₁ = trans (sub-ren σ₂ ρ τ₁) (sub-cong {σ = λ i → σ₂ (ρ i)} {σ' = σ₁} τ₁ Eσ)
  E₂ = trans (sub-ren σ₂ ρ τ₂) (sub-cong {σ = λ i → σ₂ (ρ i)} {σ' = σ₁} τ₂ Eσ)
  e-inl = subst-val-inl E₁ E₂ E v
  p̂ = subst (λ z → size z < N) e-inl p
ren-shape-val {ρ = ρ} {η₁ = η₁} {τ = τ₁ [+] τ₂} (fo₁ [+] fo₂) r σ₁ σ₂ Eσ {N = N} a a' f₁ f₂ hyp E (inr v) q p =
  trans (cong inj₂ (ren-shape-val fo₂ r σ₁ σ₂ Eσ a a' f₁ f₂ hyp E₂ v (<-trans (n<1+n _) q)
                      (<-trans (n<1+n _) p̂)))
        (sym (cong (ren-shape (fo₁ [+] fo₂) r) (shape-val-cast (fo₁ [+] fo₂) σ₁ η₁ N a f₁ e-inr p)))
  where
  E₁ = trans (sub-ren σ₂ ρ τ₁) (sub-cong {σ = λ i → σ₂ (ρ i)} {σ' = σ₁} τ₁ Eσ)
  E₂ = trans (sub-ren σ₂ ρ τ₂) (sub-cong {σ = λ i → σ₂ (ρ i)} {σ' = σ₁} τ₂ Eσ)
  e-inr = subst-val-inr E₁ E₂ E v
  p̂ = subst (λ z → size z < N) e-inr p
ren-shape-val {ρ = ρ} {η₁ = η₁} {τ = τ₁ [×] τ₂} (fo₁ [×] fo₂) r σ₁ σ₂ Eσ {N = N} a a' f₁ f₂ hyp E (pair v u) q p =
  trans (cong₂ _,_ (ren-shape-val fo₁ r σ₁ σ₂ Eσ a a' f₁ f₂ hyp E₁ v
                      (<-trans (s≤s (m≤m+n _ _)) q) (<-trans (s≤s (m≤m+n _ _)) p̂))
                   (ren-shape-val fo₂ r σ₁ σ₂ Eσ a a' f₁ f₂ hyp E₂ u
                      (<-trans (s≤s (m≤n+m _ _)) q) (<-trans (s≤s (m≤n+m _ _)) p̂)))
        (sym (cong (ren-shape (fo₁ [×] fo₂) r) (shape-val-cast (fo₁ [×] fo₂) σ₁ η₁ N a f₁ e-pair p)))
  where
  E₁ = trans (sub-ren σ₂ ρ τ₁) (sub-cong {σ = λ i → σ₂ (ρ i)} {σ' = σ₁} τ₁ Eσ)
  E₂ = trans (sub-ren σ₂ ρ τ₂) (sub-cong {σ = λ i → σ₂ (ρ i)} {σ' = σ₁} τ₂ Eσ)
  e-pair = subst-val-pair E₁ E₂ E v u
  p̂ = subst (λ z → size z < N) e-pair p
ren-shape-val {n₁ = n₁} {n₂ = n₂} {ρ = ρ} {ρ̂ = ρ̂} {η₁ = η₁} {η₂ = η₂} {τ = μ τ} (μ fo) r σ₁ σ₂ Eσ
              {N = N} {N' = N'} (acc rs) (acc rs') f₁ f₂ hyp E (roll w) q p =
  trans (cong sup (ren-shape-val fo (rbind fo r) σ₁' σ₂' Eσ' (rs p̂) (rs' q) F₁ F₂ hyp' E'' vI qI p*))
        (sym (trans (cong (ren-shape (μ fo) r) (shape-val-cast (μ fo) σ₁ η₁ N (acc rs) f₁ e-roll p))
                    (cong (λ z → sup (ren-shape fo (rbind fo r) z))
                          (shape-val-cast fo σ₁' η₁' (suc (size wE)) (rs p̂) F₁ e-in pJ))))
  where
  B₁ = sub (sub-lift σ₁) τ
  B₂ = sub (sub-lift σ₂) (extᵗ ρ *ᵗ τ)
  σ₁' = extend σ₁ (μ B₁)
  σ₂' = extend σ₂ (μ B₂)
  η₁' = extend η₁ (inj₂ (mkSort ∣ fo-as-poly fo ∅𝒞 ∣ η₁))
  pw : ∀ i → sub-lift σ₂ (extᵗ ρ i) ≡ sub-lift σ₁ i
  pw zero    = refl
  pw (suc i) = cong (suc *ᵗ_) (Eσ i)
  e : B₂ ≡ B₁
  e = trans (sub-ren (sub-lift σ₂) (extᵗ ρ) τ)
            (sub-cong {σ = λ i → sub-lift σ₂ (extᵗ ρ i)} {σ' = sub-lift σ₁} τ pw)
  Ew = cong (λ υ → υ [ μ υ ]) e
  wE = subst Val Ew w
  e-roll = subst-val-roll e E w
  p̂ = subst (λ z → size z < N) e-roll p
  f₁c : Compat σ₁ η₁ (suc (size wE))
  f₁c j u q₀ = f₁ j u (<-trans q₀ p̂)
  f₂c : Compat σ₂ η₂ (suc (size w))
  f₂c j u q₀ = f₂ j u (<-trans q₀ q)
  F₁ : Compat σ₁' (extend η₁ (inj₂ (mkSort ∣ fo-as-poly fo ∅𝒞 ∣ η₁))) (suc (size wE))
  F₁ = extend-compat (shape-val (μ fo) σ₁ η₁ (suc (size wE)) (rs p̂) f₁c) f₁c
  F₂ : Compat σ₂' (extend η₂ (inj₂ (mkSort ∣ fo-as-poly (fo-ren {ρ = extᵗ ρ} fo) ∅𝒞 ∣ η₂))) (suc (size w))
  F₂ = extend-compat (shape-val (μ (fo-ren {ρ = extᵗ ρ} fo)) σ₂ η₂ (suc (size w)) (rs' q) f₂c) f₂c
  Eσ' : ∀ i → σ₂' (extᵗ ρ i) ≡ σ₁' i
  Eσ' zero    = E
  Eσ' (suc i) = Eσ i
  E'' : sub σ₂' (extᵗ ρ *ᵗ τ) ≡ sub σ₁' τ
  E'' = trans (sub-ren σ₂' (extᵗ ρ) τ)
              (sub-cong {σ = λ i → σ₂' (extᵗ ρ i)} {σ' = σ₁'} τ Eσ')
  U₁ = unfold-sub σ₁ τ
  U₂ = unfold-sub σ₂ (extᵗ ρ *ᵗ τ)
  vI = subst Val U₂ w
  qI = s≤s (≤-reflexive (size-subst U₂ w))
  pJ = s≤s (≤-reflexive (size-subst U₁ wE))
  e-in : subst Val U₁ wE ≡ subst Val E'' vI
  e-in = trans (subst-subst Ew)
               (trans (cong (λ h → subst Val h w) (uip (trans Ew U₁) (trans U₂ E'')))
                      (sym (subst-subst U₂)))
  p* = subst (λ z → size z < suc (size wE)) e-in pJ
  hyp' : ∀ j (u : Val (σ₂' (extᵗ ρ̂ j ↑ˡ 0))) (q₀ : size u < suc (size w))
         (Ej : σ₂' (extᵗ ρ̂ j ↑ˡ 0) ≡ σ₁' (j ↑ˡ 0)) (p₀ : size (subst Val Ej u) < suc (size wE)) →
         F₂ (extᵗ ρ̂ j) u q₀ ≡ rapply (rbind fo r) j (F₁ j (subst Val Ej u) p₀)
  hyp' zero u q₀ Ej p₀ =
    ren-shape-val (μ fo) r σ₁ σ₂ Eσ (rs p̂) (rs' q) f₁c f₂c
      (λ j u₀ q₁ Ej₁ p₁ → hyp j u₀ (<-trans q₁ q) Ej₁ (<-trans p₁ p̂)) Ej u q₀ p₀
  hyp' (suc j) u q₀ Ej p₀ = hyp j u (<-trans q₀ q) Ej (<-trans p₀ p̂)

-- Shapes also translate along a first-order substitution of the type variables, sending the shape
-- at a variable to a shape of the substituted type. A μ node lifts the substitution, so there the
-- per-variable translations extend by a tree translation at the bound sort and the earlier ones
-- are moved under the binder by the renaming translation at the weakening.
data SubCompat : ∀ {n₁ n₂} {σ : TySub (n₁ + 0) (n₂ + 0)} → (∀ i → first-order (σ i)) →
                 (Fin n₁ → Fin 0 ⊎ Sort 0) → (Fin n₂ → Fin 0 ⊎ Sort 0) → Set₁ where
  sbase : ∀ {n₁ n₂} {σ : TySub (n₁ + 0) (n₂ + 0)} {fσ : ∀ i → first-order (σ i)}
          {η₁ : Fin n₁ → Fin 0 ⊎ Sort 0} {η₂ : Fin n₂ → Fin 0 ⊎ Sort 0} →
          (∀ j → El (η₁ j) → ⟦ ∣ fo-as-poly (fσ (j ↑ˡ 0)) ∅𝒞 ∣ ⟧shape η₂) →
          SubCompat fσ η₁ η₂
  sbind : ∀ {n₁ n₂} {σ : TySub (n₁ + 0) (n₂ + 0)} {fσ : ∀ i → first-order (σ i)}
          {η₁ : Fin n₁ → Fin 0 ⊎ Sort 0} {η₂ : Fin n₂ → Fin 0 ⊎ Sort 0}
          {τ : type (suc n₁ + 0)} (fo : first-order τ) → SubCompat fσ η₁ η₂ →
          SubCompat (fo-lift fσ)
                    (extend η₁ (inj₂ (mkSort ∣ fo-as-poly fo ∅𝒞 ∣ η₁)))
                    (extend η₂ (inj₂ (mkSort ∣ fo-as-poly (fo-sub (fo-lift fσ) fo) ∅𝒞 ∣ η₂)))

mutual
  sub-tree : ∀ {n₁ n₂} {σ : TySub (n₁ + 0) (n₂ + 0)} {fσ : ∀ i → first-order (σ i)}
             {η₁ : Fin n₁ → Fin 0 ⊎ Sort 0} {η₂ : Fin n₂ → Fin 0 ⊎ Sort 0}
             {τ : type (suc n₁ + 0)} (fo : first-order τ) → SubCompat fσ η₁ η₂ →
             W ∣ fo-as-poly fo ∅𝒞 ∣ η₁ → W ∣ fo-as-poly (fo-sub (fo-lift fσ) fo) ∅𝒞 ∣ η₂
  sub-tree fo r (sup x) = sup (sub-shape fo (sbind fo r) x)

  sub-shape : ∀ {n₁ n₂} {σ : TySub (n₁ + 0) (n₂ + 0)} {fσ : ∀ i → first-order (σ i)}
              {η₁ : Fin n₁ → Fin 0 ⊎ Sort 0} {η₂ : Fin n₂ → Fin 0 ⊎ Sort 0}
              {τ : type (n₁ + 0)} (fo : first-order τ) → SubCompat fσ η₁ η₂ →
              ⟦ ∣ fo-as-poly fo ∅𝒞 ∣ ⟧shape η₁ → ⟦ ∣ fo-as-poly (fo-sub fσ fo) ∅𝒞 ∣ ⟧shape η₂
  sub-shape {n₁ = n₁} (var i) r x = sub-var r i (splitAt n₁ i) refl x
  sub-shape unit r x = x
  sub-shape (base s) r x = x
  sub-shape (fo₁ [+] fo₂) r (inj₁ x) = inj₁ (sub-shape fo₁ r x)
  sub-shape (fo₁ [+] fo₂) r (inj₂ y) = inj₂ (sub-shape fo₂ r y)
  sub-shape (fo₁ [×] fo₂) r (x , y) = sub-shape fo₁ r x , sub-shape fo₂ r y
  sub-shape (μ fo) r t = sub-tree fo r t

  sub-var : ∀ {n₁ n₂} {σ : TySub (n₁ + 0) (n₂ + 0)} {fσ : ∀ i → first-order (σ i)}
            {η₁ : Fin n₁ → Fin 0 ⊎ Sort 0} {η₂ : Fin n₂ → Fin 0 ⊎ Sort 0} →
            SubCompat fσ η₁ η₂ → (i : Fin (n₁ + 0)) (s : Fin n₁ ⊎ Fin 0) → splitAt n₁ i ≡ s →
            ⟦ ∣ Var s ∣ ⟧shape η₁ → ⟦ ∣ fo-as-poly (fσ i) ∅𝒞 ∣ ⟧shape η₂
  sub-var {fσ = fσ} {η₂ = η₂} r i (inj₁ j) eq x =
    subst (λ i' → ⟦ ∣ fo-as-poly (fσ i') ∅𝒞 ∣ ⟧shape η₂) (splitAt⁻¹-↑ˡ eq) (sapply r j x)
  sub-var r i (inj₂ ()) eq x

  sapply : ∀ {n₁ n₂} {σ : TySub (n₁ + 0) (n₂ + 0)} {fσ : ∀ i → first-order (σ i)}
           {η₁ : Fin n₁ → Fin 0 ⊎ Sort 0} {η₂ : Fin n₂ → Fin 0 ⊎ Sort 0} →
           SubCompat fσ η₁ η₂ → ∀ j → El (η₁ j) → ⟦ ∣ fo-as-poly (fσ (j ↑ˡ 0)) ∅𝒞 ∣ ⟧shape η₂
  sapply (sbase g) j x = g j x
  sapply (sbind fo r) zero x = sub-tree fo r x
  sapply (sbind {fσ = fσ} fo r) (suc j) x = ren-shape {ρ = suc} (fσ (j ↑ˡ 0)) weaken-ren (sapply r j x)

-- shape-val commutes with the substitution translation: reading a value's shape at the substituted
-- type gives the translation of its shape at the original type, when the closing substitutions agree
-- with the composite and the shape read at each substituted variable is the translation of the value
-- there. In the μ case the bound variable is handled by recursion at the smaller size and the outer
-- variables by ren-shape-val at the weakening renaming.
sub-shape-val :
  ∀ {n₁ n₂} {σᵗ : TySub (n₁ + 0) (n₂ + 0)} {fσ : ∀ i → first-order (σᵗ i)}
  {η₁ : Fin n₁ → Fin 0 ⊎ Sort 0} {η₂ : Fin n₂ → Fin 0 ⊎ Sort 0}
  {τ : type (n₁ + 0)} (fo : first-order τ) (r : SubCompat fσ η₁ η₂)
  (σ₁ : TySub (n₁ + 0) 0) (σ₂ : TySub (n₂ + 0) 0) (Eσ : ∀ i → sub σ₂ (σᵗ i) ≡ σ₁ i)
  {N N' : ℕ} (a : Acc _<_ N) (a' : Acc _<_ N') (f₁ : Compat σ₁ η₁ N) (f₂ : Compat σ₂ η₂ N') →
  (∀ j (u : Val (sub σ₂ (σᵗ (j ↑ˡ 0)))) (q : size u < N') (Ej : sub σ₂ (σᵗ (j ↑ˡ 0)) ≡ σ₁ (j ↑ˡ 0))
     (p : size (subst Val Ej u) < N) →
   shape-val (fσ (j ↑ˡ 0)) σ₂ η₂ N' a' f₂ u q ≡ sapply r j (f₁ j (subst Val Ej u) p)) →
  ∀ (E : sub σ₂ (sub σᵗ τ) ≡ sub σ₁ τ) (v : Val (sub σ₂ (sub σᵗ τ))) (q : size v < N')
    (p : size (subst Val E v) < N) →
  shape-val (fo-sub fσ fo) σ₂ η₂ N' a' f₂ v q
    ≡ sub-shape fo r (shape-val fo σ₁ η₁ N a f₁ (subst Val E v) p)
sub-shape-val {n₁ = n₁} {σᵗ = σᵗ} {fσ = fσ} {η₁ = η₁} {η₂ = η₂} (var i) r σ₁ σ₂ Eσ
              {N = N} {N' = N'} a a' f₁ f₂ hyp E v q p =
  go (splitAt n₁ i) refl
  where
  FAM : Fin (n₁ + 0) → Set
  FAM i' = ⟦ ∣ fo-as-poly (fσ i') ∅𝒞 ∣ ⟧shape η₂

  go' : ∀ i' j (eq : splitAt n₁ i' ≡ inj₁ j) → j ↑ˡ 0 ≡ i' →
        (v' : Val (sub σ₂ (σᵗ i'))) (q' : size v' < N') (E' : sub σ₂ (σᵗ i') ≡ σ₁ i')
        (p' : size (subst Val E' v') < N) →
        shape-val (fσ i') σ₂ η₂ N' a' f₂ v' q'
          ≡ subst FAM (splitAt⁻¹-↑ˡ eq)
              (sapply r j (shape-var i' σ₁ η₁ N f₁ (subst Val E' v') p' (inj₁ j) eq))
  go' .(j ↑ˡ 0) j eq refl v' q' E' p' =
    trans (hyp j v' q' E' p*)
          (trans (cong (sapply r j) (app-cast (f₁ j) e-u (subst-subst-sym e-u)))
                 (cong (λ h → subst FAM h (sapply r j (f₁ j u₁ p₁))) (uip refl (splitAt⁻¹-↑ˡ eq))))
    where
    E₁ = sym (cong σ₁ (splitAt⁻¹-↑ˡ eq))
    u₁ = subst Val E₁ (subst Val E' v')
    p₁ = subst (_< N) (sym (size-subst E₁ (subst Val E' v'))) p'
    e-u : subst Val E' v' ≡ u₁
    e-u = sym (cong (λ h → subst Val h (subst Val E' v')) (uip E₁ refl))
    p* = subst (λ z → size z < N) (sym e-u) p₁

  go : ∀ s (eq : splitAt n₁ i ≡ s) →
       shape-val (fσ i) σ₂ η₂ N' a' f₂ v q
         ≡ sub-var r i s eq (shape-var i σ₁ η₁ N f₁ (subst Val E v) p s eq)
  go (inj₁ j) eq = go' i j eq (splitAt⁻¹-↑ˡ eq) v q E p
  go (inj₂ ()) eq
sub-shape-val {η₁ = η₁} unit r σ₁ σ₂ Eσ {N = N} a a' f₁ f₂ hyp E unit q p =
  sym (shape-val-cast unit σ₁ η₁ N a f₁ (cong (λ h → subst Val h unit) (uip E refl)) p)
sub-shape-val {η₁ = η₁} (base s) r σ₁ σ₂ Eσ {N = N} a a' f₁ f₂ hyp E (const c) q p =
  sym (shape-val-cast (base s) σ₁ η₁ N a f₁ (cong (λ h → subst Val h (const c)) (uip E refl)) p)
sub-shape-val {σᵗ = σᵗ} {η₁ = η₁} {τ = τ₁ [+] τ₂} (fo₁ [+] fo₂) r σ₁ σ₂ Eσ {N = N} a a' f₁ f₂ hyp E (inl v) q p =
  trans (cong inj₁ (sub-shape-val fo₁ r σ₁ σ₂ Eσ a a' f₁ f₂ hyp E₁ v (<-trans (n<1+n _) q)
                      (<-trans (n<1+n _) p̂)))
        (sym (cong (sub-shape (fo₁ [+] fo₂) r) (shape-val-cast (fo₁ [+] fo₂) σ₁ η₁ N a f₁ e-inl p)))
  where
  E₁ = trans (sub-sub σ₂ σᵗ τ₁) (sub-cong {σ = λ i → sub σ₂ (σᵗ i)} {σ' = σ₁} τ₁ Eσ)
  E₂ = trans (sub-sub σ₂ σᵗ τ₂) (sub-cong {σ = λ i → sub σ₂ (σᵗ i)} {σ' = σ₁} τ₂ Eσ)
  e-inl = subst-val-inl E₁ E₂ E v
  p̂ = subst (λ z → size z < N) e-inl p
sub-shape-val {σᵗ = σᵗ} {η₁ = η₁} {τ = τ₁ [+] τ₂} (fo₁ [+] fo₂) r σ₁ σ₂ Eσ {N = N} a a' f₁ f₂ hyp E (inr v) q p =
  trans (cong inj₂ (sub-shape-val fo₂ r σ₁ σ₂ Eσ a a' f₁ f₂ hyp E₂ v (<-trans (n<1+n _) q)
                      (<-trans (n<1+n _) p̂)))
        (sym (cong (sub-shape (fo₁ [+] fo₂) r) (shape-val-cast (fo₁ [+] fo₂) σ₁ η₁ N a f₁ e-inr p)))
  where
  E₁ = trans (sub-sub σ₂ σᵗ τ₁) (sub-cong {σ = λ i → sub σ₂ (σᵗ i)} {σ' = σ₁} τ₁ Eσ)
  E₂ = trans (sub-sub σ₂ σᵗ τ₂) (sub-cong {σ = λ i → sub σ₂ (σᵗ i)} {σ' = σ₁} τ₂ Eσ)
  e-inr = subst-val-inr E₁ E₂ E v
  p̂ = subst (λ z → size z < N) e-inr p
sub-shape-val {σᵗ = σᵗ} {η₁ = η₁} {τ = τ₁ [×] τ₂} (fo₁ [×] fo₂) r σ₁ σ₂ Eσ {N = N} a a' f₁ f₂ hyp E (pair v u) q p =
  trans (cong₂ _,_ (sub-shape-val fo₁ r σ₁ σ₂ Eσ a a' f₁ f₂ hyp E₁ v
                      (<-trans (s≤s (m≤m+n _ _)) q) (<-trans (s≤s (m≤m+n _ _)) p̂))
                   (sub-shape-val fo₂ r σ₁ σ₂ Eσ a a' f₁ f₂ hyp E₂ u
                      (<-trans (s≤s (m≤n+m _ _)) q) (<-trans (s≤s (m≤n+m _ _)) p̂)))
        (sym (cong (sub-shape (fo₁ [×] fo₂) r) (shape-val-cast (fo₁ [×] fo₂) σ₁ η₁ N a f₁ e-pair p)))
  where
  E₁ = trans (sub-sub σ₂ σᵗ τ₁) (sub-cong {σ = λ i → sub σ₂ (σᵗ i)} {σ' = σ₁} τ₁ Eσ)
  E₂ = trans (sub-sub σ₂ σᵗ τ₂) (sub-cong {σ = λ i → sub σ₂ (σᵗ i)} {σ' = σ₁} τ₂ Eσ)
  e-pair = subst-val-pair E₁ E₂ E v u
  p̂ = subst (λ z → size z < N) e-pair p
sub-shape-val {n₁ = n₁} {n₂ = n₂} {σᵗ = σᵗ} {fσ = fσ} {η₁ = η₁} {η₂ = η₂} {τ = μ τ} (μ fo) r σ₁ σ₂ Eσ
              {N = N} {N' = N'} (acc rs) a'@(acc rs') f₁ f₂ hyp E (roll w) q p =
  trans (cong sup (sub-shape-val fo (sbind fo r) σ₁' σ₂' Eσ' (rs p̂) (rs' q) F₁ F₂ hyp' E'' vI qI p*))
        (sym (trans (cong (sub-shape (μ fo) r) (shape-val-cast (μ fo) σ₁ η₁ N (acc rs) f₁ e-roll p))
                    (cong (λ z → sup (sub-shape fo (sbind fo r) z))
                          (shape-val-cast fo σ₁' η₁' (suc (size wE)) (rs p̂) F₁ e-in pJ))))
  where
  B₁ = sub (sub-lift σ₁) τ
  B₂ = sub (sub-lift σ₂) (sub (sub-lift σᵗ) τ)
  σ₁' = extend σ₁ (μ B₁)
  σ₂' = extend σ₂ (μ B₂)
  η₁' = extend η₁ (inj₂ (mkSort ∣ fo-as-poly fo ∅𝒞 ∣ η₁))
  s₂ = inj₂ (mkSort ∣ fo-as-poly (fo-sub (fo-lift fσ) fo) ∅𝒞 ∣ η₂)
  η₂' = extend η₂ s₂
  pw : ∀ i → sub (sub-lift σ₂) (sub-lift σᵗ i) ≡ sub-lift σ₁ i
  pw zero    = refl
  pw (suc i) = trans (sub-ren (sub-lift σ₂) suc (σᵗ i))
                     (trans (sym (ren-sub suc σ₂ (σᵗ i))) (cong (suc *ᵗ_) (Eσ i)))
  e : B₂ ≡ B₁
  e = trans (sub-sub (sub-lift σ₂) (sub-lift σᵗ) τ)
            (sub-cong {σ = λ i → sub (sub-lift σ₂) (sub-lift σᵗ i)} {σ' = sub-lift σ₁} τ pw)
  Ew = cong (λ υ → υ [ μ υ ]) e
  wE = subst Val Ew w
  e-roll = subst-val-roll e E w
  p̂ = subst (λ z → size z < N) e-roll p
  f₁c : Compat σ₁ η₁ (suc (size wE))
  f₁c j u q₀ = f₁ j u (<-trans q₀ p̂)
  f₂c : Compat σ₂ η₂ (suc (size w))
  f₂c j u q₀ = f₂ j u (<-trans q₀ q)
  F₁ : Compat σ₁' η₁' (suc (size wE))
  F₁ = extend-compat (shape-val (μ fo) σ₁ η₁ (suc (size wE)) (rs p̂) f₁c) f₁c
  F₂ : Compat σ₂' η₂' (suc (size w))
  F₂ = extend-compat (shape-val (μ (fo-sub (fo-lift fσ) fo)) σ₂ η₂ (suc (size w)) (rs' q) f₂c) f₂c
  wr : RenCompat suc suc η₂ η₂'
  wr = weaken-ren {η = η₂} {s = s₂}
  Eσ' : ∀ i → sub σ₂' (sub-lift σᵗ i) ≡ σ₁' i
  Eσ' zero    = E
  Eσ' (suc i) = trans (sub-ren σ₂' suc (σᵗ i)) (Eσ i)
  E'' : sub σ₂' (sub (sub-lift σᵗ) τ) ≡ sub σ₁' τ
  E'' = trans (sub-sub σ₂' (sub-lift σᵗ) τ)
              (sub-cong {σ = λ i → sub σ₂' (sub-lift σᵗ i)} {σ' = σ₁'} τ Eσ')
  U₁ = unfold-sub σ₁ τ
  U₂ = unfold-sub σ₂ (sub (sub-lift σᵗ) τ)
  vI = subst Val U₂ w
  qI = s≤s (≤-reflexive (size-subst U₂ w))
  pJ = s≤s (≤-reflexive (size-subst U₁ wE))
  e-in : subst Val U₁ wE ≡ subst Val E'' vI
  e-in = trans (subst-subst Ew)
               (trans (cong (λ h → subst Val h w) (uip (trans Ew U₁) (trans U₂ E'')))
                      (sym (subst-subst U₂)))
  p* = subst (λ z → size z < suc (size wE)) e-in pJ
  hyp-c : ∀ j (u : Val (sub σ₂ (σᵗ (j ↑ˡ 0)))) (q₁ : size u < suc (size w))
          (Ej : sub σ₂ (σᵗ (j ↑ˡ 0)) ≡ σ₁ (j ↑ˡ 0)) (p₁ : size (subst Val Ej u) < suc (size wE)) →
          shape-val (fσ (j ↑ˡ 0)) σ₂ η₂ (suc (size w)) (rs' q) f₂c u q₁
            ≡ sapply r j (f₁c j (subst Val Ej u) p₁)
  hyp-c j u q₁ Ej p₁ =
    trans (shape-val-irrelevant (fσ (j ↑ˡ 0)) σ₂ η₂ (rs' q) a' f₂c f₂
             (λ j₀ u₀ p₀ q₀ → cong (f₂ j₀ u₀) (<-irrelevant (<-trans p₀ q) q₀)) u q₁ (<-trans q₁ q))
          (hyp j u (<-trans q₁ q) Ej (<-trans p₁ p̂))
  hyp-w : ∀ j (u : Val (σ₂' (suc j ↑ˡ 0))) (q₁ : size u < suc (size w))
          (Ej : σ₂' (suc j ↑ˡ 0) ≡ σ₂ (j ↑ˡ 0)) (p₁ : size (subst Val Ej u) < N') →
          F₂ (suc j) u q₁ ≡ rapply wr j (f₂ j (subst Val Ej u) p₁)
  hyp-w j u q₁ Ej p₁ =
    app-cast (f₂ j) (sym (cong (λ h → subst Val h u) (uip Ej refl))) (<-irrelevant _ _)
  hyp' : ∀ j (u : Val (sub σ₂' (sub-lift σᵗ (j ↑ˡ 0)))) (q₀ : size u < suc (size w))
         (Ej : sub σ₂' (sub-lift σᵗ (j ↑ˡ 0)) ≡ σ₁' (j ↑ˡ 0))
         (p₀ : size (subst Val Ej u) < suc (size wE)) →
         shape-val (fo-lift fσ (j ↑ˡ 0)) σ₂' η₂' (suc (size w)) (rs' q) F₂ u q₀
           ≡ sapply (sbind fo r) j (F₁ j (subst Val Ej u) p₀)
  hyp' zero u q₀ Ej p₀ =
    trans (sub-shape-val (μ fo) r σ₁ σ₂ Eσ (rs p̂) (rs' q) f₁c f₂c hyp-c E-z (subst Val E₀ u) q₀' p₀')
          (cong (sub-tree fo r)
                (app-cast (shape-val (μ fo) σ₁ η₁ (suc (size wE)) (rs p̂) f₁c) e-z {p = p₀'} {p' = p₀}
                   (subst-subst-sym {P = λ z → size z < suc (size wE)} e-z)))
    where
    eq₀ : splitAt (suc n₂) zero ≡ inj₁ zero
    eq₀ = refl
    E₀ = sym (cong σ₂' (splitAt⁻¹-↑ˡ {m = suc n₂} {n = 0} {i = zero} {j = zero} eq₀))
    q₀' = subst (_< suc (size w)) (sym (size-subst E₀ u)) q₀
    E-z : sub σ₂ (sub σᵗ (μ τ)) ≡ sub σ₁ (μ τ)
    E-z = trans (sym E₀) Ej
    e-z : subst Val E-z (subst Val E₀ u) ≡ subst Val Ej u
    e-z = trans (subst-subst {P = Val} E₀ {y≡z = E-z} {p = u})
                (cong (λ h → subst Val h u) (uip (trans E₀ E-z) Ej))
    p₀' = subst (λ z → size z < suc (size wE)) (sym e-z) p₀
  hyp' (suc j) u q₀ Ej p₀ =
    trans (ren-shape-val (fσ (j ↑ˡ 0)) wr σ₂ σ₂' (λ i → refl) a' (rs' q) f₂ F₂ hyp-w Eᵣ u q₀ pᵣ)
          (cong (ren-shape (fσ (j ↑ˡ 0)) wr)
                (trans (hyp j (subst Val Eᵣ u) pᵣ Ej' p†)
                       (cong (sapply r j) (app-cast (f₁ j) e-u (subst-subst-sym e-u)))))
    where
    Eᵣ : sub σ₂' (suc *ᵗ σᵗ (j ↑ˡ 0)) ≡ sub σ₂ (σᵗ (j ↑ˡ 0))
    Eᵣ = sub-ren σ₂' suc (σᵗ (j ↑ˡ 0))
    pᵣ = subst (_< N') (sym (size-subst Eᵣ u)) (<-trans q₀ q)
    Ej' : sub σ₂ (σᵗ (j ↑ˡ 0)) ≡ σ₁ (j ↑ˡ 0)
    Ej' = trans (sym Eᵣ) Ej
    e-u : subst Val Ej' (subst Val Eᵣ u) ≡ subst Val Ej u
    e-u = trans (subst-subst Eᵣ) (cong (λ h → subst Val h u) (uip (trans Eᵣ Ej') Ej))
    p† = subst (λ z → size z < N) (sym e-u) (<-trans p₀ p̂)

private
  subst-set-inj₁ : ∀ {ℓ} {A A' B B' : Set ℓ} (e₁ : A ≡ A') (e₂ : B ≡ B')
                   (E : (A ⊎ B) ≡ (A' ⊎ B')) (x : A) →
                   subst (λ X → X) E (inj₁ x) ≡ inj₁ (subst (λ X → X) e₁ x)
  subst-set-inj₁ refl refl refl x = refl

  subst-set-inj₂ : ∀ {ℓ} {A A' B B' : Set ℓ} (e₁ : A ≡ A') (e₂ : B ≡ B')
                   (E : (A ⊎ B) ≡ (A' ⊎ B')) (y : B) →
                   subst (λ X → X) E (inj₂ y) ≡ inj₂ (subst (λ X → X) e₂ y)
  subst-set-inj₂ refl refl refl y = refl

  subst-set-pair : ∀ {ℓ} {A A' B B' : Set ℓ} (e₁ : A ≡ A') (e₂ : B ≡ B')
                   (E : (A × B) ≡ (A' × B')) (x : A) (y : B) →
                   subst (λ X → X) E (x , y) ≡ (subst (λ X → X) e₁ x , subst (λ X → X) e₂ y)
  subst-set-pair refl refl refl x y = refl

val-carrier : ∀ {τ : type 0} (fo : first-order τ) →
              ⟦ ∣ fo-as-poly fo ∅𝒞 ∣ ⟧shape (λ i → inj₁ i) ≡ Carrier (𝒞⟦ fo ⟧ty ∅𝒞 .idx)
val-carrier (var ())
val-carrier unit          = refl
val-carrier (base s)      = refl
val-carrier (fo₁ [+] fo₂) = cong₂ _⊎_ (val-carrier fo₁) (val-carrier fo₂)
val-carrier (fo₁ [×] fo₂) = cong₂ _×_ (val-carrier fo₁) (val-carrier fo₂)
val-carrier (μ fo)        = refl

id-shape-val : ∀ {τ : type 0} (fo : first-order τ) {N} (a : Acc _<_ N)
               (f : Compat var (λ i → inj₁ i) N) (E : τ ≡ sub var τ) (v : Val τ)
               (p : size (subst Val E v) < N) →
               subst (λ X → X) (val-carrier fo)
                 (shape-val fo var (λ i → inj₁ i) N a f (subst Val E v) p)
                 ≡ ⟦ fo ⟧val v
id-shape-val (var ())
id-shape-val unit a f E unit p =
  shape-val-cast unit var (λ i → inj₁ i) _ a f (cong (λ h → subst Val h unit) (uip E refl)) p
id-shape-val (base s) a f E (const c) p =
  shape-val-cast (base s) var (λ i → inj₁ i) _ a f (cong (λ h → subst Val h (const c)) (uip E refl)) p
id-shape-val {τ = τ₁ [+] τ₂} (fo₁ [+] fo₂) a f E (inl v) p =
  trans (cong (subst (λ X → X) (val-carrier (fo₁ [+] fo₂)))
              (shape-val-cast (fo₁ [+] fo₂) var (λ i → inj₁ i) _ a f (subst-val-inl e₁ e₂ E v) p))
  (trans (subst-set-inj₁ (val-carrier fo₁) (val-carrier fo₂) (val-carrier (fo₁ [+] fo₂)) _)
         (cong inj₁ (id-shape-val fo₁ a f e₁ v _)))
  where
  e₁ = sym (sub-id τ₁)
  e₂ = sym (sub-id τ₂)
id-shape-val {τ = τ₁ [+] τ₂} (fo₁ [+] fo₂) a f E (inr v) p =
  trans (cong (subst (λ X → X) (val-carrier (fo₁ [+] fo₂)))
              (shape-val-cast (fo₁ [+] fo₂) var (λ i → inj₁ i) _ a f (subst-val-inr e₁ e₂ E v) p))
  (trans (subst-set-inj₂ (val-carrier fo₁) (val-carrier fo₂) (val-carrier (fo₁ [+] fo₂)) _)
         (cong inj₂ (id-shape-val fo₂ a f e₂ v _)))
  where
  e₁ = sym (sub-id τ₁)
  e₂ = sym (sub-id τ₂)
id-shape-val {τ = τ₁ [×] τ₂} (fo₁ [×] fo₂) a f E (pair v u) p =
  trans (cong (subst (λ X → X) (val-carrier (fo₁ [×] fo₂)))
              (shape-val-cast (fo₁ [×] fo₂) var (λ i → inj₁ i) _ a f (subst-val-pair e₁ e₂ E v u) p))
  (trans (subst-set-pair (val-carrier fo₁) (val-carrier fo₂) (val-carrier (fo₁ [×] fo₂)) _ _)
         (cong₂ _,_ (id-shape-val fo₁ a f e₁ v _) (id-shape-val fo₂ a f e₂ u _)))
  where
  e₁ = sym (sub-id τ₁)
  e₂ = sym (sub-id τ₂)
id-shape-val {τ = μ τ} (μ fo) a f E v p =
  trans (shape-val-cast (μ fo) var (λ i → inj₁ i) _ a f e-v p)
        (shape-val-irrelevant (μ fo) var (λ i → inj₁ i) a (<-wellFounded _) f (λ ()) (λ ())
           (subst Val (sym (sub-id (μ τ))) v) _ _)
  where
  e-v = cong (λ h → subst Val h v) (uip E (sym (sub-id (μ τ))))
