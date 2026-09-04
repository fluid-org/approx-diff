{-# OPTIONS --prop --postfix-projections --guardedness #-}

open import Level using (0ℓ)
open import Data.Rational using (ℚ)
open import prop-setoid using (Setoid)
open import commutative-semiring using (CommutativeSemiring)

-- Values as axis labels: the glyphs of a value in printed order, each with the positions it covers.
module example.render.value-labels {A : Setoid 0ℓ 0ℓ} (as-weight : ℚ → Setoid.Carrier A)
                                   (S : CommutativeSemiring A) (ctrl-weight : Setoid.Carrier A) where

open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (_×_; _,_)
open import Data.String using (String; _++_)
open import Data.Unit using (⊤)
import Data.Vec as Vec
open import signature.example.interpretation as-weight S using (Sig; interpretation)
open import language-operational.evaluation Sig S interpretation ctrl-weight using (Val; Env)
open import example.render.constants as-weight S using (show-const)
open import example.render.table using (Label)
import example.render.annotated-value as AV
open AV Sig S interpretation ctrl-weight
  using (AVal; node; Tag; width; shape-of; shape-env-of)

private
  shw : ∀ {s} → _ → String
  shw {s} c = show-const {s} c

  appL : {A : Set} → List A → List A → List A
  appL []       ys = ys
  appL (x ∷ xs) ys = x ∷ appL xs ys

  labels : ℕ → AVal ⊤ → List Label
  labels-snd : ℕ → AVal ⊤ → List Label
  labels-vec : ∀ {k} → ℕ → Vec.Vec (AVal ⊤) k → List Label

  labels off (node Tag.unit      _ n _)  = ("()" , n , off) ∷ []
  labels off (node (Tag.const l) _ n _)  = (l , n , off) ∷ []
  labels off (node Tag.inl       _ n cs) = ("\\mathsf{inl}\\," , n , off) ∷ labels-vec (off + n) cs
  labels off (node Tag.inr       _ n cs) = ("\\mathsf{inr}\\," , n , off) ∷ labels-vec (off + n) cs
  labels off (node (Tag.clo _)   _ n _)  = ("\\lambda" , n , off) ∷ []
  labels off (node Tag.nil       _ n _)  = ("[\\,]" , n , off) ∷ []
  labels off (node Tag.pair      _ n (p Vec.∷ q Vec.∷ Vec.[])) =
    ("(" , 0 , 0) ∷ appL (labels (off + n) p)
      (("," , n , off) ∷ appL (labels-snd (off + n + width p) q) ((")" , 0 , 0) ∷ []))
  labels off (node Tag.cons      _ n (h Vec.∷ t Vec.∷ Vec.[])) =
    appL (labels (off + n) h) (("\\cons" , n , off) ∷ labels (off + n + width h) t)

  labels-snd off (node Tag.pair _ n (p Vec.∷ q Vec.∷ Vec.[])) =
    appL (labels (off + n) p) (("," , n , off) ∷ labels-snd (off + n + width p) q)
  labels-snd off t = labels off t

  labels-vec off Vec.[]      = []
  labels-vec off (t Vec.∷ _) = labels off t

  labels-env : ℕ → List (AVal ⊤) → List Label
  labels-env _   []       = []
  labels-env off (c ∷ []) = labels off c
  labels-env off (c ∷ cs) = appL (labels off c) ((";" , 0 , 0) ∷ labels-env (off + width c) cs)

txt : AVal ⊤ → String
txt-snd : AVal ⊤ → String
txt-rest : AVal ⊤ → String

txt (node Tag.unit      _ _ _) = "()"
txt (node (Tag.const l) _ _ _) = l
txt (node Tag.inl       _ _ cs) = "inl " ++ txt-kid cs
  where
  txt-kid : ∀ {k} → Vec.Vec (AVal ⊤) k → String
  txt-kid Vec.[]      = ""
  txt-kid (t Vec.∷ _) = txt t
txt (node Tag.inr       _ _ cs) = "inr " ++ txt-kid cs
  where
  txt-kid : ∀ {k} → Vec.Vec (AVal ⊤) k → String
  txt-kid Vec.[]      = ""
  txt-kid (t Vec.∷ _) = txt t
txt (node (Tag.clo _)   _ _ _) = "<closure>"
txt (node Tag.nil       _ _ _) = "[]"
txt (node Tag.pair      _ _ (a Vec.∷ b Vec.∷ Vec.[])) = "(" ++ txt a ++ txt-snd b ++ ")"
txt (node Tag.cons      _ _ (h Vec.∷ t Vec.∷ Vec.[])) = "[" ++ txt h ++ txt-rest t ++ "]"

txt-snd (node Tag.pair _ _ (a Vec.∷ b Vec.∷ Vec.[])) = ", " ++ txt a ++ txt-snd b
txt-snd t = ", " ++ txt t

txt-rest (node Tag.nil  _ _ _) = ""
txt-rest (node Tag.cons _ _ (h Vec.∷ t Vec.∷ Vec.[])) = ", " ++ txt h ++ txt-rest t
txt-rest t = ", " ++ txt t

show-val : ∀ {τ} → Val τ → String
show-val v = txt (shape-of (λ {s} c → shw {s} c) v)

show-env : ∀ {Γ} → Env Γ → String
show-env γ = go (shape-env-of (λ {s} c → shw {s} c) γ)
  where
  go : List (AVal ⊤) → String
  go []       = ""
  go (c ∷ []) = txt c
  go (c ∷ cs) = txt c ++ "; " ++ go cs

val-labels : ∀ {τ} → ℕ → Val τ → List Label
val-labels off v = labels off (shape-of (λ {s} c → shw {s} c) v)

env-labels : ∀ {Γ} → Env Γ → List Label
env-labels γ = labels-env 0 (shape-env-of (λ {s} c → shw {s} c) γ)
