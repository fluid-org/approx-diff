{-# OPTIONS --prop --postfix-projections --guardedness #-}

-- Values as axis labels: the glyphs of a value in printed order, each with the positions it covers.
module example.render.tokens where

open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (_×_; _,_)
open import Data.String using (String; _++_)
open import Data.Unit using (⊤)
import Data.Vec as Vec
import three
open import semiring-Q using (nonzero)
open import signature.example.interpretation (nonzero three.semiring) three.semiring
  using (Sig; interpretation)
open import language-operational.evaluation Sig three.semiring interpretation three.C using (Val; Env)
open import example.render.constants (nonzero three.semiring) three.semiring using (show-const)
open import example.render.grid using (Tok)
import example.render.annotated-value as AV
open AV Sig three.semiring interpretation three.C
  using (AVal; node; Tag; width; shape-of; shape-env-of)

private
  shw : ∀ {s} → _ → String
  shw {s} c = show-const {s} c

  appL : {A : Set} → List A → List A → List A
  appL []       ys = ys
  appL (x ∷ xs) ys = x ∷ appL xs ys

  tokens : ℕ → AVal ⊤ → List Tok
  tokens-snd : ℕ → AVal ⊤ → List Tok
  tokens-vec : ∀ {k} → ℕ → Vec.Vec (AVal ⊤) k → List Tok

  tokens off (node Tag.unit      _ n _)  = ("()" , n , off) ∷ []
  tokens off (node (Tag.const l) _ n _)  = (l , n , off) ∷ []
  tokens off (node Tag.inl       _ n cs) = ("\\mathsf{inl}\\," , n , off) ∷ tokens-vec (off + n) cs
  tokens off (node Tag.inr       _ n cs) = ("\\mathsf{inr}\\," , n , off) ∷ tokens-vec (off + n) cs
  tokens off (node (Tag.clo _)   _ n _)  = ("\\lambda" , n , off) ∷ []
  tokens off (node Tag.nil       _ n _)  = ("[\\,]" , n , off) ∷ []
  tokens off (node Tag.pair      _ n (p Vec.∷ q Vec.∷ Vec.[])) =
    ("(" , 0 , 0) ∷ appL (tokens (off + n) p)
      (("," , n , off) ∷ appL (tokens-snd (off + n + width p) q) ((")" , 0 , 0) ∷ []))
  tokens off (node Tag.cons      _ n (h Vec.∷ t Vec.∷ Vec.[])) =
    appL (tokens (off + n) h) (("\\cons" , n , off) ∷ tokens (off + n + width h) t)

  tokens-snd off (node Tag.pair _ n (p Vec.∷ q Vec.∷ Vec.[])) =
    appL (tokens (off + n) p) (("," , n , off) ∷ tokens-snd (off + n + width p) q)
  tokens-snd off t = tokens off t

  tokens-vec off Vec.[]      = []
  tokens-vec off (t Vec.∷ _) = tokens off t

  tokens-env : ℕ → List (AVal ⊤) → List Tok
  tokens-env _   []       = []
  tokens-env off (c ∷ []) = tokens off c
  tokens-env off (c ∷ cs) = appL (tokens off c) ((";" , 0 , 0) ∷ tokens-env (off + width c) cs)

val-toks : ∀ {τ} → ℕ → Val τ → List Tok
val-toks off v = tokens off (shape-of (λ {s} c → shw {s} c) v)

env-toks : ∀ {Γ} → Env Γ → List Tok
env-toks γ = tokens-env 0 (shape-env-of (λ {s} c → shw {s} c) γ)
