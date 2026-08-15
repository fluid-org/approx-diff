{-# OPTIONS --prop --postfix-projections --safe #-}

open import signature using (Signature)
open import primitives using (Primitives)
open import commutative-semiring using (CommutativeSemiring)
import matrix
import two

-- Agreement for the fold action: collapsing a fold-action graph recovers the action's three
-- dependence relations, on the environment, on the source and on the input value.
module interaction.control-agreement-fold {ℓ} (Sig : Signature ℓ) (𝒫 : Primitives two.semiring Sig) where

open Signature Sig
open Primitives 𝒫
open import language-syntax Sig renaming (_,_ to _▸_)
open import language-operational.type-substitution Sig using (unfold₁; unfold₁-inst)
open import language-operational.evaluation Sig two.semiring 𝒫 two.I
  using (Val; Env; width; width-env; width-subst; lookup; bool→val; ctrl-row; proj-var;
         brel-deps)
open Val
open Env
open import language-operational.control Sig two.semiring 𝒫 two.I
open import interaction.control-path Sig 𝒫
open import interaction.control-graph Sig 𝒫
open import interaction.control-hide Sig 𝒫

private
  module M = matrix.Mat two.semiring

open CommutativeSemiring two.semiring
  using (+-comm; +-cong; +-lunit; +-assoc; +-interchange; refl; trans)
import Data.Bool as Bool
import Data.Nat as Nat
open import Data.List using (List; []; _∷_; _++_; map)
open import every using (Every; []; _∷_)
open import Data.List.Properties using (map-++)
open import Data.List.Relation.Unary.All using (All; []; _∷_; universal)
open import Data.List.Relation.Unary.All.Properties using (map⁺; ++⁺)
open import Relation.Binary.PropositionalEquality using (_≡_; subst)
  renaming (refl to ≡-refl; cong to ≡-cong; trans to ≡-trans; sym to ≡-sym)
open import prop-setoid using () renaming (_⇒_ to _⇒ₛ_)
open _⇒ₛ_ using (func)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit.Polymorphic using () renaming (⊤ to ⊤')
open import Level using (0ℓ)
open import categories using (Category; HasTerminal)
open Category M.cat
  using (_⇒_; _∘_; _≈_; ∘-cong; ∘-cong₁; ∘-cong₂; assoc; id-left; id-right;
         ≈-refl; ≈-sym; ≈-trans; isEquiv)
  renaming (id to idm)
open HasTerminal M.terminal using (to-terminal)
open import interaction.control-agreement-algebra Sig 𝒫

-- The mu action: one premise at the unfolded type, with width casts on the input row and the
-- root edge.
module MMu {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr}
           {τ' : type 2} {w : Val (unfold₁ τ' [ μ τ₀ ])} {R : Nat.suc (width-env γ) ⇒ width w}
           {w' : Val (unfold₁ τ' [ σr ])} {R' : Nat.suc (width-env γ) ⇒ width w'}
           {D : Map γ s (unfold₁ τ') w R w' R'} where

  private
    C = m-mu {τ' = τ'} D

    eᵥ : width w ≡ width (subst Val (unfold₁-inst τ' (μ τ₀)) w)
    eᵥ = ≡-sym (width-subst (unfold₁-inst τ' (μ τ₀)) w)

    e' : width w' ≡ width (subst Val (unfold₁-inst τ' σr) w')
    e' = ≡-sym (width-subst (unfold₁-inst τ' σr) w')

    P : M.Matrix (width (subst Val (unfold₁-inst τ' σr) w')) (width w')
    P = rcast e' M.I

  record Embeds (G : GraphM C) (H : GraphM D) : Set ℓ where
    field
      env-embed   : ∀ q → G env (at (m-mu q)) ≈ H env (at q)
      src-embed   : ∀ q → G src (at (m-mu q)) ≈ H src (at q)
      input-embed : ∀ q → G input (at (m-mu q)) ≈ ccast eᵥ (H input (at q))
      embed-embed : ∀ p q → G (at (m-mu p)) (at (m-mu q)) ≈ H (at p) (at q)
      env-root    : G env (at ε) ≈ (P ∘ H env (at ε))
      source-root : G src (at ε) ≈ (P ∘ H src (at ε))
      input-root  : G input (at ε) ≈ (P ∘ ccast eᵥ (H input (at ε)))
      embed-root  : ∀ p → is-ε-m p ≡ Bool.false →
                    G (at (m-mu p)) (at ε) ≈ (P ∘ H (at p) (at ε))

  open Embeds

  embeds-hide : ∀ {G H} (x : PathM D) → is-ε-m x ≡ Bool.false →
                Embeds G H → Embeds (hide-m G (at (m-mu x))) (hide-m H (at x))
  embeds-hide x nw r .env-embed q =
    +ₘ-cong (r .env-embed q) (∘-cong (r .embed-embed x q) (r .env-embed x))
  embeds-hide x nw r .src-embed q =
    +ₘ-cong (r .src-embed q) (∘-cong (r .embed-embed x q) (r .src-embed x))
  embeds-hide x nw r .input-embed q =
    ccast-step eᵥ (r .input-embed q) (r .embed-embed x q) (r .input-embed x)
  embeds-hide x nw r .embed-embed p q =
    +ₘ-cong (r .embed-embed p q) (∘-cong (r .embed-embed x q) (r .embed-embed p x))
  embeds-hide x nw r .env-root =
    root-step {P = P} (r .env-root) (r .embed-root x nw) (r .env-embed x)
  embeds-hide x nw r .source-root =
    root-step {P = P} (r .source-root) (r .embed-root x nw) (r .src-embed x)
  embeds-hide x nw r .input-root =
    root-step-cast eᵥ P (r .input-root) (r .embed-root x nw) (r .input-embed x)
  embeds-hide x nw r .embed-root p np =
    root-step {P = P} (r .embed-root p np) (r .embed-root x nw) (r .embed-embed p x)

  embeds-hide-all : ∀ {G H} (ws : List (PathM D)) → All (λ x → is-ε-m x ≡ Bool.false) ws →
                    Embeds G H →
                    Embeds (hide-all-m G (map at (map m-mu ws))) (hide-all-m H (map at ws))
  embeds-hide-all []       []         r = r
  embeds-hide-all (x ∷ ws) (nw ∷ nws) r = embeds-hide-all ws nws (embeds-hide x nw r)

  private
    embeds₀ : Embeds (hide-m (hide-m (graph-m C) (at ε)) (at (m-mu ε)))
                     (hide-m (graph-m D) (at ε))
    embeds₀ .env-embed q = hide-hide-root-m C (at (m-mu ε)) env (at (m-mu q))
    embeds₀ .src-embed q = hide-hide-root-m C (at (m-mu ε)) src (at (m-mu q))
    embeds₀ .input-embed q =
      ≈-trans (hide-hide-root-m C (at (m-mu ε)) input (at (m-mu q)))
              (ccast-step eᵥ {X = graph-m D input (at q)} {Z = graph-m D input (at ε)}
                          ≈-refl ≈-refl ≈-refl)
    embeds₀ .embed-embed p q = hide-hide-root-m C (at (m-mu ε)) (at (m-mu p)) (at (m-mu q))
    embeds₀ .env-root =
      ≈-trans (hide-hide-root-m C (at (m-mu ε)) env (at ε)) (into-hidden-m D P env)
    embeds₀ .source-root =
      ≈-trans (hide-hide-root-m C (at (m-mu ε)) src (at ε)) (into-hidden-m D P src)
    embeds₀ .input-root =
      ≈-trans (hide-hide-root-m C (at (m-mu ε)) input (at ε))
      (≈-trans (+ₘ-lunit (P ∘ ccast eᵥ (graph-m D input (at ε))))
               (∘-cong₂ (ccast-cong eᵥ (≈-sym (hide-root-m D input (at ε))))))
    embeds₀ .embed-root p np =
      ≈-trans (hide-hide-root-m C (at (m-mu ε)) (at (m-mu p)) (at ε))
      (≈-trans (+ₘ-cong (edge-off-m P p np) ≈-refl) (into-hidden-m D P (at p)))

    rfin = embeds-hide-all (interior-m D) (interior-not-root-m D) embeds₀

  agree-env : collapse-m-env C ≈ rcast e' (collapse-m-env D)
  agree-env =
    ≈-trans (rfin .env-root)
    (≈-trans (rcast-∘ e' M.I (collapse-m-env D)) (rcast-cong e' id-left))

  agree-src : collapse-m-src C ≈ rcast e' (collapse-m-src D)
  agree-src =
    ≈-trans (rfin .source-root)
    (≈-trans (rcast-∘ e' M.I (collapse-m-src D)) (rcast-cong e' id-left))

  agree-in : collapse-m-in C ≈ rcast e' (ccast eᵥ (collapse-m-in D))
  agree-in =
    ≈-trans (rfin .input-root)
    (≈-trans (rcast-∘ e' M.I (ccast eᵥ (collapse-m-in D))) (rcast-cong e' id-left))

-- The pair action: the two premises' collapses are injected side by side, the input columns
-- resolved through the two halves of the input value.
module MPair {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr}
             {σ₁ σ₂ : type 1} {v : Val (σ₁ [ μ τ₀ ])} {u : Val (σ₂ [ μ τ₀ ])}
             {R : Nat.suc (width-env γ) ⇒ width (pair v u)}
             {v' : Val (σ₁ [ σr ])} {S₁ : Nat.suc (width-env γ) ⇒ width v'}
             {u' : Val (σ₂ [ σr ])} {T : Nat.suc (width-env γ) ⇒ width u'}
             {D₁ : Map γ s σ₁ v
                     (M.p₁ {width v} {width u} ∘ (M.p₂ {1} {width v Nat.+ width u} ∘ R)) v' S₁}
             {D₂ : Map γ s σ₂ u
                     (M.p₂ {width v} {width u} ∘ (M.p₂ {1} {width v Nat.+ width u} ∘ R)) u' T}
             where

  private
    C : Map γ s (σ₁ [×] σ₂) (pair v u) R (pair v' u') _
    C = m-pair {v = v} {v' = v'} {u = u} {u' = u'} {R = R} {T = S₁} {U = T} D₁ D₂

    p2 = M.p₂ {1} {width v Nat.+ width u}
    pˡ = M.p₁ {width v} {width u}
    pʳ = M.p₂ {width v} {width u}
    i₁ = M.in₁ {width v'} {width u'}
    i₂ = M.in₂ {width v'} {width u'}
    ri₁ = M.in₂ {1} {width v' Nat.+ width u'} ∘ i₁
    ri₂ = M.in₂ {1} {width v' Nat.+ width u'} ∘ i₂
    Wˡ = pˡ ∘ p2
    Wʳ = pʳ ∘ p2
    K = M.in₁ {1} {width v' Nat.+ width u'} ∘ M.p₁ {1} {width v Nat.+ width u}
    Kₛ = src-root {width v' Nat.+ width u'}

  record Phase₁ (G : GraphM C) (H : GraphM D₁) : Set ℓ where
    field
      env-left    : ∀ q → G env (at (m-pair₁ q)) ≈ H env (at q)
      src-left    : ∀ q → G src (at (m-pair₁ q)) ≈ H src (at q)
      input-left  : ∀ q → G input (at (m-pair₁ q)) ≈ (H input (at q) ∘ Wˡ)
      left-left   : ∀ p q → G (at (m-pair₁ p)) (at (m-pair₁ q)) ≈ H (at p) (at q)
      env-root    : G env (at ε) ≈ (ri₁ ∘ H env (at ε))
      source-root : G src (at ε) ≈ (Kₛ M.+ₘ (ri₁ ∘ H src (at ε)))
      input-root  : G input (at ε) ≈ (K M.+ₘ ((ri₁ ∘ H input (at ε)) ∘ Wˡ))
      left-root   : ∀ p → is-ε-m p ≡ Bool.false →
                    G (at (m-pair₁ p)) (at ε) ≈ (ri₁ ∘ H (at p) (at ε))
      env-right   : ∀ q → G env (at (m-pair₂ q)) ≈ graph-m D₂ env (at q)
      src-right   : ∀ q → G src (at (m-pair₂ q)) ≈ graph-m D₂ src (at q)
      input-right : ∀ q → G input (at (m-pair₂ q)) ≈ (graph-m D₂ input (at q) ∘ Wʳ)
      right-right : ∀ p q → G (at (m-pair₂ p)) (at (m-pair₂ q)) ≈ graph-m D₂ (at p) (at q)
      right-root  : ∀ p → G (at (m-pair₂ p)) (at ε) ≈ edge-m ri₂ p
      left-right  : ∀ p q → G (at (m-pair₁ p)) (at (m-pair₂ q)) ≈ M.εₘ
      right-left  : ∀ p q → G (at (m-pair₂ p)) (at (m-pair₁ q)) ≈ M.εₘ

  open Phase₁

  step₁ : ∀ {G H} (w : PathM D₁) → is-ε-m w ≡ Bool.false →
          Phase₁ G H → Phase₁ (hide-m G (at (m-pair₁ w))) (hide-m H (at w))
  step₁ w nw r .env-left q = +ₘ-cong (r .env-left q) (∘-cong (r .left-left w q) (r .env-left w))
  step₁ w nw r .src-left q = +ₘ-cong (r .src-left q) (∘-cong (r .left-left w q) (r .src-left w))
  step₁ {H = H} w nw r .input-left q =
    step-under {W = Wˡ} {X = H input (at q)} {Y = H (at w) (at q)} {Z = H input (at w)}
      (r .input-left q) (r .left-left w q) (r .input-left w)
  step₁ w nw r .left-left p q =
    +ₘ-cong (r .left-left p q) (∘-cong (r .left-left w q) (r .left-left p w))
  step₁ w nw r .env-root = root-step {P = ri₁} (r .env-root) (r .left-root w nw) (r .env-left w)
  step₁ {H = H} w nw r .source-root =
    offset-step {K = Kₛ} {P = ri₁} {X = H src (at ε)} {Y = H (at w) (at ε)} {Z = H src (at w)}
      (r .source-root) (r .left-root w nw) (r .src-left w)
  step₁ {H = H} w nw r .input-root =
    offset-under ri₁ {W = Wˡ} {K = K}
                 {X = H input (at ε)} {Y = H (at w) (at ε)} {Z = H input (at w)}
      (r .input-root) (r .left-root w nw) (r .input-left w)
  step₁ w nw r .left-root p np =
    root-step {P = ri₁} (r .left-root p np) (r .left-root w nw) (r .left-left p w)
  step₁ w nw r .env-right q = keep-l (r .env-right q) (r .left-right w q)
  step₁ w nw r .src-right q = keep-l (r .src-right q) (r .left-right w q)
  step₁ w nw r .input-right q = keep-l (r .input-right q) (r .left-right w q)
  step₁ w nw r .right-right p q = keep-l (r .right-right p q) (r .left-right w q)
  step₁ w nw r .right-root p = keep-r (r .right-root p) (r .right-left p w)
  step₁ w nw r .left-right p q = keep-l (r .left-right p q) (r .left-right w q)
  step₁ w nw r .right-left p q = keep-r (r .right-left p q) (r .right-left p w)

  steps₁ : ∀ {G H} (ws : List (PathM D₁)) → All (λ w → is-ε-m w ≡ Bool.false) ws →
           Phase₁ G H → Phase₁ (hide-all-m G (map at (map m-pair₁ ws))) (hide-all-m H (map at ws))
  steps₁ []       []         r = r
  steps₁ (w ∷ ws) (nw ∷ nws) r = steps₁ ws nws (step₁ w nw r)

  private
    hh : ∀ x y → hide-m (hide-m (graph-m C) (at ε)) (at (m-pair₁ ε)) x y
         ≈ (graph-m C x y M.+ₘ (graph-m C (at (m-pair₁ ε)) y ∘ graph-m C x (at (m-pair₁ ε))))
    hh = hide-hide-root-m C (at (m-pair₁ ε))

    base₁ : Phase₁ (hide-m (hide-m (graph-m C) (at ε)) (at (m-pair₁ ε)))
                   (hide-m (graph-m D₁) (at ε))
    base₁ .env-left q = hh env (at (m-pair₁ q))
    base₁ .src-left q = hh src (at (m-pair₁ q))
    base₁ .input-left q =
      ≈-trans (hh input (at (m-pair₁ q)))
              (step-under {W = Wˡ} {X = graph-m D₁ input (at q)} {Y = graph-m D₁ (at ε) (at q)}
                          {Z = graph-m D₁ input (at ε)}
                          (assoc (graph-m D₁ input (at q)) pˡ p2)
                          (≈-refl {f = graph-m D₁ (at ε) (at q)})
                          (assoc (graph-m D₁ input (at ε)) pˡ p2))
    base₁ .left-left p q = hh (at (m-pair₁ p)) (at (m-pair₁ q))
    base₁ .env-root = ≈-trans (hh env (at ε)) (into-hidden-m D₁ ri₁ env)
    base₁ .source-root =
      ≈-trans {f = hide-m (hide-m (graph-m C) (at ε)) (at (m-pair₁ ε)) src (at ε)}
              {g = Kₛ M.+ₘ (ri₁ ∘ graph-m D₁ src (at ε))}
              {h = Kₛ M.+ₘ (ri₁ ∘ hide-m (graph-m D₁) (at ε) src (at ε))}
              (hh src (at ε)) (into-hidden-off-m D₁ src Kₛ ri₁)
    base₁ .input-root =
      ≈-trans (hh input (at ε))
              (+ₘ-cong (≈-refl {f = K})
                       (≈-trans (∘-cong₂ (assoc (graph-m D₁ input (at ε)) pˡ p2))
                       (≈-trans (≈-sym (assoc ri₁ (graph-m D₁ input (at ε)) Wˡ))
                                (∘-cong₁ (∘-cong₂ (≈-sym (hide-root-m D₁ input (at ε))))))))
    base₁ .left-root p np =
      ≈-trans (hh (at (m-pair₁ p)) (at ε))
      (≈-trans (+ₘ-cong (edge-off-m ri₁ p np) ≈-refl) (into-hidden-m D₁ ri₁ (at p)))
    base₁ .env-right q =
      ≈-trans (hh env (at (m-pair₂ q)))
              (absorb (graph-m C env (at (m-pair₂ q))) (graph-m C env (at (m-pair₁ ε))))
    base₁ .src-right q =
      ≈-trans (hh src (at (m-pair₂ q)))
              (absorb (graph-m C src (at (m-pair₂ q))) (graph-m C src (at (m-pair₁ ε))))
    base₁ .input-right q =
      ≈-trans (hh input (at (m-pair₂ q)))
              (≈-trans (absorb (graph-m C input (at (m-pair₂ q)))
                               (graph-m C input (at (m-pair₁ ε))))
                       (assoc (graph-m D₂ input (at q)) pʳ p2))
    base₁ .right-right p q =
      ≈-trans (hh (at (m-pair₂ p)) (at (m-pair₂ q)))
              (absorb (graph-m C (at (m-pair₂ p)) (at (m-pair₂ q)))
                      (graph-m C (at (m-pair₂ p)) (at (m-pair₁ ε))))
    base₁ .right-root p =
      ≈-trans (hh (at (m-pair₂ p)) (at ε))
              (absorb-r (graph-m C (at (m-pair₂ p)) (at ε)) (graph-m C (at (m-pair₁ ε)) (at ε)))
    base₁ .left-right p q =
      ≈-trans (hh (at (m-pair₁ p)) (at (m-pair₂ q)))
              (absorb (graph-m C (at (m-pair₁ p)) (at (m-pair₂ q)))
                      (graph-m C (at (m-pair₁ p)) (at (m-pair₁ ε))))
    base₁ .right-left p q =
      ≈-trans (hh (at (m-pair₂ p)) (at (m-pair₁ q)))
              (absorb-r (graph-m C (at (m-pair₂ p)) (at (m-pair₁ q)))
                        (graph-m C (at (m-pair₁ ε)) (at (m-pair₁ q))))

  record Phase₂ (G : GraphM C) (H : GraphM D₂)
                (Kₑ : M.Matrix (width (pair v' u')) (width-env γ))
                (Kc : M.Matrix (width (pair v' u')) 1)
                (Kᵢ : M.Matrix (width (pair v' u')) (width (pair v u))) : Set ℓ where
    field
      env-right   : ∀ q → G env (at (m-pair₂ q)) ≈ H env (at q)
      src-right   : ∀ q → G src (at (m-pair₂ q)) ≈ H src (at q)
      input-right : ∀ q → G input (at (m-pair₂ q)) ≈ (H input (at q) ∘ Wʳ)
      right-right : ∀ p q → G (at (m-pair₂ p)) (at (m-pair₂ q)) ≈ H (at p) (at q)
      env-root    : G env (at ε) ≈ (Kₑ M.+ₘ (ri₂ ∘ H env (at ε)))
      source-root : G src (at ε) ≈ (Kc M.+ₘ (ri₂ ∘ H src (at ε)))
      input-root  : G input (at ε) ≈ (Kᵢ M.+ₘ ((ri₂ ∘ H input (at ε)) ∘ Wʳ))
      right-root  : ∀ p → is-ε-m p ≡ Bool.false →
                    G (at (m-pair₂ p)) (at ε) ≈ (ri₂ ∘ H (at p) (at ε))

  open Phase₂

  step₂ : ∀ {G H Kₑ Kc Kᵢ} (w : PathM D₂) → is-ε-m w ≡ Bool.false →
          Phase₂ G H Kₑ Kc Kᵢ → Phase₂ (hide-m G (at (m-pair₂ w))) (hide-m H (at w)) Kₑ Kc Kᵢ
  step₂ w nw r .env-right q = +ₘ-cong (r .env-right q) (∘-cong (r .right-right w q) (r .env-right w))
  step₂ w nw r .src-right q = +ₘ-cong (r .src-right q) (∘-cong (r .right-right w q) (r .src-right w))
  step₂ {H = H} w nw r .input-right q =
    step-under {W = Wʳ} {X = H input (at q)} {Y = H (at w) (at q)} {Z = H input (at w)}
      (r .input-right q) (r .right-right w q) (r .input-right w)
  step₂ w nw r .right-right p q =
    +ₘ-cong (r .right-right p q) (∘-cong (r .right-right w q) (r .right-right p w))
  step₂ {Kₑ = Kₑ} w nw r .env-root =
    offset-step {K = Kₑ} {P = ri₂} (r .env-root) (r .right-root w nw) (r .env-right w)
  step₂ {Kc = Kc} w nw r .source-root =
    offset-step {K = Kc} {P = ri₂} (r .source-root) (r .right-root w nw) (r .src-right w)
  step₂ {H = H} {Kᵢ = Kᵢ} w nw r .input-root =
    offset-under ri₂ {W = Wʳ} {K = Kᵢ}
                 {X = H input (at ε)} {Y = H (at w) (at ε)} {Z = H input (at w)}
      (r .input-root) (r .right-root w nw) (r .input-right w)
  step₂ w nw r .right-root p np =
    root-step {P = ri₂} (r .right-root p np) (r .right-root w nw) (r .right-right p w)

  steps₂ : ∀ {G H Kₑ Kc Kᵢ} (ws : List (PathM D₂)) → All (λ w → is-ε-m w ≡ Bool.false) ws →
           Phase₂ G H Kₑ Kc Kᵢ →
           Phase₂ (hide-all-m G (map at (map m-pair₂ ws))) (hide-all-m H (map at ws)) Kₑ Kc Kᵢ
  steps₂ []       []         r = r
  steps₂ (w ∷ ws) (nw ∷ nws) r = steps₂ ws nws (step₂ w nw r)

  private
    r1 : Phase₁ (hide-all-m (hide-m (hide-m (graph-m C) (at ε)) (at (m-pair₁ ε)))
                            (map at (map m-pair₁ (interior-m D₁))))
                (hide-all-m (hide-m (graph-m D₁) (at ε)) (map at (interior-m D₁)))
    r1 = steps₁ (interior-m D₁) (interior-not-root-m D₁) base₁

    base₂ : Phase₂ (hide-m (hide-all-m (hide-m (hide-m (graph-m C) (at ε)) (at (m-pair₁ ε)))
                                       (map at (map m-pair₁ (interior-m D₁))))
                           (at (m-pair₂ ε)))
                   (hide-m (graph-m D₂) (at ε))
                   (ri₁ ∘ collapse-m-env D₁)
                   (Kₛ M.+ₘ (ri₁ ∘ collapse-m-src D₁))
                   (K M.+ₘ ((ri₁ ∘ collapse-m-in D₁) ∘ Wˡ))
    base₂ .env-right q = +ₘ-cong (r1 .env-right q) (∘-cong (r1 .right-right ε q) (r1 .env-right ε))
    base₂ .src-right q = +ₘ-cong (r1 .src-right q) (∘-cong (r1 .right-right ε q) (r1 .src-right ε))
    base₂ .input-right q =
      step-under {W = Wʳ} {X = graph-m D₂ input (at q)}
                 {Y = graph-m D₂ (at ε) (at q)}
                 {Z = graph-m D₂ input (at ε)}
                 (r1 .input-right q) (r1 .right-right ε q) (r1 .input-right ε)
    base₂ .right-right p q =
      +ₘ-cong (r1 .right-right p q) (∘-cong (r1 .right-right ε q) (r1 .right-right p ε))
    base₂ .env-root =
      ≈-trans (+ₘ-cong (r1 .env-root) (∘-cong (r1 .right-root ε) (r1 .env-right ε)))
              (+ₘ-cong (≈-refl {f = ri₁ ∘ collapse-m-env D₁})
                       (∘-cong₂ {f = ri₂} (≈-sym (hide-root-m D₂ env (at ε)))))
    base₂ .source-root =
      ≈-trans (+ₘ-cong (r1 .source-root) (∘-cong (r1 .right-root ε) (r1 .src-right ε)))
              (+ₘ-cong (≈-refl {f = Kₛ M.+ₘ (ri₁ ∘ collapse-m-src D₁)})
                       (∘-cong₂ {f = ri₂} (≈-sym (hide-root-m D₂ src (at ε)))))
    base₂ .input-root =
      ≈-trans (+ₘ-cong (r1 .input-root) (∘-cong (r1 .right-root ε) (r1 .input-right ε)))
              (+ₘ-cong (≈-refl {f = K M.+ₘ ((ri₁ ∘ collapse-m-in D₁) ∘ Wˡ)})
                       (≈-trans (≈-sym (assoc ri₂ (graph-m D₂ input (at ε)) Wʳ))
                                (∘-cong₁ (∘-cong₂ (≈-sym (hide-root-m D₂ input (at ε)))))))
    base₂ .right-root p np =
      ≈-trans (+ₘ-cong (≈-trans (r1 .right-root p) (edge-off-m ri₂ p np))
                       (∘-cong (r1 .right-root ε) (r1 .right-right p ε)))
              (into-hidden-m D₂ ri₂ (at p))

    rfin = steps₂ (interior-m D₂) (interior-not-root-m D₂) base₂

    plumbG : hide-all-m (hide-m (graph-m C) (at ε))
                        (map at (map m-pair₁ (paths-m D₁) ++ map m-pair₂ (paths-m D₂)))
             ≡ hide-all-m (hide-all-m (hide-m (graph-m C) (at ε))
                                      (map at (map m-pair₁ (paths-m D₁))))
                          (map at (map m-pair₂ (paths-m D₂)))
    plumbG =
      ≡-trans (≡-cong (hide-all-m (hide-m (graph-m C) (at ε)))
                      (map-++ at (map m-pair₁ (paths-m D₁)) (map m-pair₂ (paths-m D₂))))
              (hide-all-m-++ (hide-m (graph-m C) (at ε))
                             (map at (map m-pair₁ (paths-m D₁)))
                             (map at (map m-pair₂ (paths-m D₂))))

  agree-env : collapse-m-env C ≈ ((ri₁ ∘ collapse-m-env D₁) M.+ₘ (ri₂ ∘ collapse-m-env D₂))
  agree-env = ≈-trans (≈-of-≡ (≡-cong (λ Gg → Gg env (at ε)) plumbG)) (rfin .env-root)

  agree-src : collapse-m-src C
              ≈ ((Kₛ M.+ₘ (ri₁ ∘ collapse-m-src D₁)) M.+ₘ (ri₂ ∘ collapse-m-src D₂))
  agree-src = ≈-trans (≈-of-≡ (≡-cong (λ Gg → Gg src (at ε)) plumbG)) (rfin .source-root)

  agree-in : collapse-m-in C
             ≈ ((K M.+ₘ ((ri₁ ∘ collapse-m-in D₁) ∘ Wˡ)) M.+ₘ ((ri₂ ∘ collapse-m-in D₂) ∘ Wʳ))
  agree-in = ≈-trans (≈-of-≡ (≡-cong (λ Gg → Gg input (at ε)) plumbG)) (rfin .input-root)

-- The recursive action: the subterm is mapped, then the fold body runs under the environment
-- extended by the mapped value. The body's source is the enclosing source, so the source column
-- travels alongside the environment column.
module MRec {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr}
            {w : Val (τ₀ [ μ τ₀ ])} {R : Nat.suc (width-env γ) ⇒ width w}
            {w' : Val (τ₀ [ σr ])} {R' : Nat.suc (width-env γ) ⇒ width w'}
            {u : Val σr} {S : Nat.suc (width-env (γ · w')) ⇒ width u}
            {D₁ : Map γ s τ₀ w R w' R'} {D₂ : γ · w' , s ⇓ u [ S ]} where

  private
    C = m-rec D₁ D₂

    iₗ = M.in₁ {width-env γ} {width w'}
    iᵣ = M.in₂ {width-env γ} {width w'}

    B : (q : Path D₂) → M.Matrix (width-at q) (width-env γ Nat.+ width w')
    B q = graph D₂ env (at q)

    Bₛ : (q : Path D₂) → M.Matrix (width-at q) 1
    Bₛ q = graph D₂ src (at q)

    Wₑ : M.Matrix (width-env γ Nat.+ width w') (width-env γ)
    Wₑ = iₗ M.+ₘ (iᵣ ∘ collapse-m-env D₁)

    Wₛ : M.Matrix (width-env γ Nat.+ width w') 1
    Wₛ = iᵣ ∘ collapse-m-src D₁

    Wᵢ : M.Matrix (width-env γ Nat.+ width w') (width w)
    Wᵢ = iᵣ ∘ collapse-m-in D₁

  record Phase₁ (G : GraphM C) (H : GraphM D₁) : Set ℓ where
    field
      env-map     : ∀ q → G env (at (m-rec₁ q)) ≈ H env (at q)
      src-map     : ∀ q → G src (at (m-rec₁ q)) ≈ H src (at q)
      input-map   : ∀ q → G input (at (m-rec₁ q)) ≈ H input (at q)
      map-map     : ∀ p q → G (at (m-rec₁ p)) (at (m-rec₁ q)) ≈ H (at p) (at q)
      env-body    : ∀ q → G env (at (m-rec₂ q))
                    ≈ ((B q ∘ iₗ) M.+ₘ ((B q ∘ iᵣ) ∘ H env (at ε)))
      src-body    : ∀ q → G src (at (m-rec₂ q))
                    ≈ (Bₛ q M.+ₘ ((B q ∘ iᵣ) ∘ H src (at ε)))
      input-body  : ∀ q → G input (at (m-rec₂ q)) ≈ ((B q ∘ iᵣ) ∘ H input (at ε))
      map-body    : ∀ p → is-ε-m p ≡ Bool.false → ∀ q →
                    G (at (m-rec₁ p)) (at (m-rec₂ q)) ≈ ((B q ∘ iᵣ) ∘ H (at p) (at ε))
      body-body   : ∀ p q → G (at (m-rec₂ p)) (at (m-rec₂ q)) ≈ graph D₂ (at p) (at q)
      body-map    : ∀ p q → G (at (m-rec₂ p)) (at (m-rec₁ q)) ≈ M.εₘ
      env-root    : G env (at ε) ≈ M.εₘ
      source-root : G src (at ε) ≈ M.εₘ
      input-root  : G input (at ε) ≈ M.εₘ
      map-root    : ∀ p → G (at (m-rec₁ p)) (at ε) ≈ M.εₘ
      body-root   : ∀ p → G (at (m-rec₂ p)) (at ε) ≈ edge M.I p

  open Phase₁

  step₁ : ∀ {G H} (x : PathM D₁) → is-ε-m x ≡ Bool.false →
          Phase₁ G H → Phase₁ (hide-m G (at (m-rec₁ x))) (hide-m H (at x))
  step₁ x nx r .env-map q = +ₘ-cong (r .env-map q) (∘-cong (r .map-map x q) (r .env-map x))
  step₁ x nx r .src-map q = +ₘ-cong (r .src-map q) (∘-cong (r .map-map x q) (r .src-map x))
  step₁ x nx r .input-map q = +ₘ-cong (r .input-map q) (∘-cong (r .map-map x q) (r .input-map x))
  step₁ x nx r .map-map p q = +ₘ-cong (r .map-map p q) (∘-cong (r .map-map x q) (r .map-map p x))
  step₁ x nx r .env-body q =
    offset-step {K = B q ∘ iₗ} {P = B q ∘ iᵣ} (r .env-body q) (r .map-body x nx q) (r .env-map x)
  step₁ x nx r .src-body q =
    offset-step {K = Bₛ q} {P = B q ∘ iᵣ} (r .src-body q) (r .map-body x nx q) (r .src-map x)
  step₁ x nx r .input-body q =
    root-step {P = B q ∘ iᵣ} (r .input-body q) (r .map-body x nx q) (r .input-map x)
  step₁ x nx r .map-body p np q =
    root-step {P = B q ∘ iᵣ} (r .map-body p np q) (r .map-body x nx q) (r .map-map p x)
  step₁ x nx r .body-body p q = keep-r (r .body-body p q) (r .body-map p x)
  step₁ x nx r .body-map p q = keep-r (r .body-map p q) (r .body-map p x)
  step₁ x nx r .env-root = keep-l (r .env-root) (r .map-root x)
  step₁ x nx r .source-root = keep-l (r .source-root) (r .map-root x)
  step₁ x nx r .input-root = keep-l (r .input-root) (r .map-root x)
  step₁ x nx r .map-root p = keep-l (r .map-root p) (r .map-root x)
  step₁ x nx r .body-root p = keep-l (r .body-root p) (r .map-root x)

  steps₁ : ∀ {G H} (ws : List (PathM D₁)) → All (λ x → is-ε-m x ≡ Bool.false) ws →
           Phase₁ G H → Phase₁ (hide-all-m G (map at (map m-rec₁ ws))) (hide-all-m H (map at ws))
  steps₁ []       []         r = r
  steps₁ (x ∷ ws) (nx ∷ nws) r = steps₁ ws nws (step₁ x nx r)

  private
    hh : ∀ x y → hide-m (hide-m (graph-m C) (at ε)) (at (m-rec₁ ε)) x y
         ≈ (graph-m C x y M.+ₘ (graph-m C (at (m-rec₁ ε)) y ∘ graph-m C x (at (m-rec₁ ε))))
    hh = hide-hide-root-m C (at (m-rec₁ ε))

    base₁ : Phase₁ (hide-m (hide-m (graph-m C) (at ε)) (at (m-rec₁ ε)))
                   (hide-m (graph-m D₁) (at ε))
    base₁ .env-map q = hh env (at (m-rec₁ q))
    base₁ .src-map q = hh src (at (m-rec₁ q))
    base₁ .input-map q = hh input (at (m-rec₁ q))
    base₁ .map-map p q = hh (at (m-rec₁ p)) (at (m-rec₁ q))
    base₁ .env-body q =
      ≈-trans (hh env (at (m-rec₂ q)))
              (+ₘ-cong (≈-refl {f = B q ∘ iₗ})
                       (∘-cong₂ {f = B q ∘ iᵣ} (≈-sym (hide-root-m D₁ env (at ε)))))
    base₁ .src-body q =
      ≈-trans {f = hide-m (hide-m (graph-m C) (at ε)) (at (m-rec₁ ε)) src (at (m-rec₂ q))}
              {g = Bₛ q M.+ₘ ((B q ∘ iᵣ) ∘ graph-m D₁ src (at ε))}
              {h = Bₛ q M.+ₘ ((B q ∘ iᵣ) ∘ hide-m (graph-m D₁) (at ε) src (at ε))}
              (hh src (at (m-rec₂ q))) (into-hidden-off-m D₁ src (Bₛ q) (B q ∘ iᵣ))
    base₁ .input-body q =
      ≈-trans (hh input (at (m-rec₂ q))) (into-hidden-m D₁ (B q ∘ iᵣ) input)
    base₁ .map-body p np q =
      ≈-trans (hh (at (m-rec₁ p)) (at (m-rec₂ q)))
      (≈-trans (+ₘ-cong (edge-off-m (B q ∘ iᵣ) p np) ≈-refl)
               (into-hidden-m D₁ (B q ∘ iᵣ) (at p)))
    base₁ .body-body p q =
      ≈-trans (hh (at (m-rec₂ p)) (at (m-rec₂ q)))
              (absorb-r (graph D₂ (at p) (at q)) (graph-m C (at (m-rec₁ ε)) (at (m-rec₂ q))))
    base₁ .body-map p q =
      ≈-trans (hh (at (m-rec₂ p)) (at (m-rec₁ q)))
              (absorb-r M.εₘ (graph-m C (at (m-rec₁ ε)) (at (m-rec₁ q))))
    base₁ .env-root = ≈-trans (hh env (at ε)) (absorb M.εₘ (graph-m C env (at (m-rec₁ ε))))
    base₁ .source-root = ≈-trans (hh src (at ε)) (absorb M.εₘ (graph-m C src (at (m-rec₁ ε))))
    base₁ .input-root = ≈-trans (hh input (at ε)) (absorb M.εₘ (graph-m C input (at (m-rec₁ ε))))
    base₁ .map-root p =
      ≈-trans (hh (at (m-rec₁ p)) (at ε))
              (absorb M.εₘ (graph-m C (at (m-rec₁ p)) (at (m-rec₁ ε))))
    base₁ .body-root p =
      ≈-trans (hh (at (m-rec₂ p)) (at ε))
              (absorb (edge M.I p) (graph-m C (at (m-rec₂ p)) (at (m-rec₁ ε))))

    route-env : ∀ {m} (A : M.Matrix m (width-env γ Nat.+ width w')) →
                ((A ∘ iₗ) M.+ₘ ((A ∘ iᵣ) ∘ collapse-m-env D₁)) ≈ (A ∘ Wₑ)
    route-env A =
      ≈-trans (+ₘ-cong (≈-refl {f = A ∘ iₗ}) (assoc A iᵣ (collapse-m-env D₁)))
              (≈-sym (M.comp-bilinear₂ A iₗ (iᵣ ∘ collapse-m-env D₁)))

    route-src : ∀ {m} (A : M.Matrix m (width-env γ Nat.+ width w')) (Bs : M.Matrix m 1) →
                (Bs M.+ₘ ((A ∘ iᵣ) ∘ collapse-m-src D₁)) ≈ ((A ∘ Wₛ) M.+ₘ Bs)
    route-src A Bs =
      ≈-trans (+ₘ-comm Bs ((A ∘ iᵣ) ∘ collapse-m-src D₁))
              (+ₘ-cong (assoc A iᵣ (collapse-m-src D₁)) ≈-refl)

  record Phase₂ (G : GraphM C) (H : Graph D₂) : Set ℓ where
    field
      env-body    : ∀ q → G env (at (m-rec₂ q)) ≈ (H env (at q) ∘ Wₑ)
      src-body    : ∀ q → G src (at (m-rec₂ q))
                    ≈ ((H env (at q) ∘ Wₛ) M.+ₘ H src (at q))
      input-body  : ∀ q → G input (at (m-rec₂ q)) ≈ (H env (at q) ∘ Wᵢ)
      body-body   : ∀ p q → G (at (m-rec₂ p)) (at (m-rec₂ q)) ≈ H (at p) (at q)
      env-root    : G env (at ε) ≈ (H env (at ε) ∘ Wₑ)
      source-root : G src (at ε) ≈ ((H env (at ε) ∘ Wₛ) M.+ₘ H src (at ε))
      input-root  : G input (at ε) ≈ (H env (at ε) ∘ Wᵢ)
      body-root   : ∀ p → is-ε p ≡ Bool.false → G (at (m-rec₂ p)) (at ε) ≈ H (at p) (at ε)

  open Phase₂

  step₂ : ∀ {G H} (x : Path D₂) → is-ε x ≡ Bool.false →
          Phase₂ G H → Phase₂ (hide-m G (at (m-rec₂ x))) (hide H (at x))
  step₂ x nx r .env-body q = step-under {W = Wₑ} (r .env-body q) (r .body-body x q) (r .env-body x)
  step₂ {H = H} x nx r .src-body q =
    pair-step-id {W = Wₛ} {A = H env (at q)} {B = H src (at q)} {Y = H (at x) (at q)}
                 {Aw = H env (at x)} {Bw = H src (at x)}
                 (r .src-body q) (r .body-body x q) (r .src-body x)
  step₂ x nx r .input-body q =
    step-under {W = Wᵢ} (r .input-body q) (r .body-body x q) (r .input-body x)
  step₂ x nx r .body-body p q =
    +ₘ-cong (r .body-body p q) (∘-cong (r .body-body x q) (r .body-body p x))
  step₂ x nx r .env-root = step-under {W = Wₑ} (r .env-root) (r .body-root x nx) (r .env-body x)
  step₂ {H = H} x nx r .source-root =
    pair-step-id {W = Wₛ} {A = H env (at ε)} {B = H src (at ε)} {Y = H (at x) (at ε)}
                 {Aw = H env (at x)} {Bw = H src (at x)}
                 (r .source-root) (r .body-root x nx) (r .src-body x)
  step₂ x nx r .input-root = step-under {W = Wᵢ} (r .input-root) (r .body-root x nx) (r .input-body x)
  step₂ x nx r .body-root p np =
    +ₘ-cong (r .body-root p np) (∘-cong (r .body-root x nx) (r .body-body p x))

  steps₂ : ∀ {G H} (ws : List (Path D₂)) → All (λ x → is-ε x ≡ Bool.false) ws →
           Phase₂ G H → Phase₂ (hide-all-m G (map at (map m-rec₂ ws))) (hide-all H (map at ws))
  steps₂ []       []         r = r
  steps₂ (x ∷ ws) (nx ∷ nws) r = steps₂ ws nws (step₂ x nx r)

  private
    PA : GraphM C
    PA = hide-all-m (hide-m (hide-m (graph-m C) (at ε)) (at (m-rec₁ ε)))
                    (map at (map m-rec₁ (interior-m D₁)))

    r1 : Phase₁ PA (hide-all-m (hide-m (graph-m D₁) (at ε)) (map at (interior-m D₁)))
    r1 = steps₁ (interior-m D₁) (interior-not-root-m D₁) base₁

    Zₛ : M.Matrix (width u) 1
    Zₛ = (B ε ∘ Wₛ) M.+ₘ Bₛ ε

    base₂ : Phase₂ (hide-m PA (at (m-rec₂ ε))) (hide (graph D₂) (at ε))
    base₂ .env-body q =
      step-under {W = Wₑ} {X = B q} {Y = graph D₂ (at ε) (at q)} {Z = B ε}
                 (≈-trans (r1 .env-body q) (route-env (B q)))
                 (r1 .body-body ε q)
                 (≈-trans (r1 .env-body ε) (route-env (B ε)))
    base₂ .src-body q =
      pair-step-id {W = Wₛ} {A = B q} {B = Bₛ q} {Y = graph D₂ (at ε) (at q)}
                   {Aw = B ε} {Bw = Bₛ ε}
                   (≈-trans (r1 .src-body q) (route-src (B q) (Bₛ q)))
                   (r1 .body-body ε q)
                   (≈-trans (r1 .src-body ε) (route-src (B ε) (Bₛ ε)))
    base₂ .input-body q =
      step-under {W = Wᵢ} {X = B q} {Y = graph D₂ (at ε) (at q)} {Z = B ε}
                 (≈-trans (r1 .input-body q) (assoc (B q) iᵣ (collapse-m-in D₁)))
                 (r1 .body-body ε q)
                 (≈-trans (r1 .input-body ε) (assoc (B ε) iᵣ (collapse-m-in D₁)))
    base₂ .body-body p q =
      +ₘ-cong (r1 .body-body p q) (∘-cong (r1 .body-body ε q) (r1 .body-body p ε))
    base₂ .env-root =
      ≈-trans (+ₘ-cong (r1 .env-root)
                       (∘-cong (r1 .body-root ε) (≈-trans (r1 .env-body ε) (route-env (B ε)))))
      (≈-trans (+ₘ-lunit (M.I ∘ (B ε ∘ Wₑ)))
      (≈-trans id-left (≈-sym (∘-cong₁ (hide-root D₂ env (at ε))))))
    base₂ .source-root =
      ≈-trans {g = M.εₘ M.+ₘ (M.I ∘ Zₛ)}
              (+ₘ-cong (r1 .source-root)
                       (∘-cong (r1 .body-root ε)
                               (≈-trans (r1 .src-body ε) (route-src (B ε) (Bₛ ε)))))
      (≈-trans {g = M.I ∘ Zₛ} (+ₘ-lunit (M.I ∘ Zₛ))
      (≈-trans {g = Zₛ} id-left
               (+ₘ-cong (∘-cong₁ {g = Wₛ} (≈-sym (hide-root D₂ env (at ε))))
                        (≈-sym (hide-root D₂ src (at ε))))))
    base₂ .input-root =
      ≈-trans (+ₘ-cong (r1 .input-root)
                       (∘-cong (r1 .body-root ε)
                               (≈-trans (r1 .input-body ε) (assoc (B ε) iᵣ (collapse-m-in D₁)))))
      (≈-trans (+ₘ-lunit (M.I ∘ (B ε ∘ Wᵢ)))
      (≈-trans id-left (≈-sym (∘-cong₁ (hide-root D₂ env (at ε))))))
    base₂ .body-root p np =
      ≈-trans (+ₘ-cong (≈-trans (r1 .body-root p) (edge-off M.I p np))
                       (∘-cong (r1 .body-root ε) (r1 .body-body p ε)))
      (≈-trans (into-hidden D₂ M.I (at p)) id-left)

    rfin = steps₂ (interior D₂) (interior-not-root D₂) base₂

    plumbG : hide-all-m (hide-m (graph-m C) (at ε))
                        (map at (map m-rec₁ (paths-m D₁) ++ map m-rec₂ (paths D₂)))
             ≡ hide-all-m (hide-all-m (hide-m (graph-m C) (at ε))
                                      (map at (map m-rec₁ (paths-m D₁))))
                          (map at (map m-rec₂ (paths D₂)))
    plumbG =
      ≡-trans (≡-cong (hide-all-m (hide-m (graph-m C) (at ε)))
                      (map-++ at (map m-rec₁ (paths-m D₁)) (map m-rec₂ (paths D₂))))
              (hide-all-m-++ (hide-m (graph-m C) (at ε))
                             (map at (map m-rec₁ (paths-m D₁)))
                             (map at (map m-rec₂ (paths D₂))))

  agree-env : collapse-m-env C ≈ (collapse D₂ ∘ Wₑ)
  agree-env = ≈-trans (≈-of-≡ (≡-cong (λ Gg → Gg env (at ε)) plumbG)) (rfin .env-root)

  agree-src : collapse-m-src C ≈ ((collapse D₂ ∘ Wₛ) M.+ₘ collapse-src D₂)
  agree-src = ≈-trans (≈-of-≡ (≡-cong (λ Gg → Gg src (at ε)) plumbG)) (rfin .source-root)

  agree-in : collapse-m-in C ≈ (collapse D₂ ∘ Wᵢ)
  agree-in = ≈-trans (≈-of-≡ (≡-cong (λ Gg → Gg input (at ε)) plumbG)) (rfin .input-root)
