{-# OPTIONS --prop --postfix-projections --guardedness #-}

-- Writes dot renderings of the example runs; run from the paper repository root. The file name is
-- the run's definition name without its inst- prefix.
module artefact.dump-graphs where

open import IO
open import IO.Finite using (writeFile)
open import Data.Rational using (ℚ)
open import Data.String using (String; _++_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.List using (List; []; _∷_; map; applyUpTo; foldr)
open import Data.Bool.ListAction using (any)
open import Data.Bool using (Bool; if_then_else_; _∧_)
open import Data.Nat using (ℕ; _+_; _*_; _≡ᵇ_; _<ᵇ_)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Level using (0ℓ)
open import example.signature ℚ using (Sig)
open import example.runs
import example.dependency as Dep
open import language-operational.evaluation Sig Dep.primitives using (width)
import language-operational.instrument as instrument
open instrument Sig Dep.primitives using (Seq; seq-vals; dep-edges; edge-rel)
open import language-operational.render Sig Dep.primitives using (show-val; showDotPlain)

private
  nth : List ℕ → ℕ → ℕ
  nth []       _         = 0
  nth (w ∷ _)  ℕ.zero    = w
  nth (_ ∷ ws) (ℕ.suc i) = nth ws i

  -- The relation as 0/1 rows, one row per target position, one column per source position.
  rel-label : List (ℕ × ℕ) → ℕ → ℕ → String
  rel-label rel wi wj = rows (applyUpTo (λ q → q) wj)
    where
    bit : ℕ → ℕ → String
    bit p q = if any (λ e → (proj₁ e ≡ᵇ p) ∧ (proj₂ e ≡ᵇ q)) rel then "1" else "0"
    row : ℕ → String
    row q = foldr _++_ "" (applyUpTo (λ p → bit p q) wi)
    rows : List ℕ → String
    rows []           = ""
    rows (q ∷ [])     = row q
    rows (q ∷ qs)     = row q ++ "\\n" ++ rows qs

  dot-of : ∀ {g n} → String → Seq g n → String × String
  dot-of name Φ =
    ("fig/dot/" ++ name ++ ".dot") ,
    showDotPlain (map (λ p → show-val (λ {s} → show-const {s}) (proj₂ p)) (seq-vals Φ))
                 (map labelled (dep-edges Φ))
    where
    widths : List ℕ
    widths = map (λ p → width (proj₂ p)) (seq-vals Φ)

    labelled : ℕ × ℕ → ℕ × ℕ × String
    labelled (i , j) =
      i , j ,
      (if 1 <ᵇ nth widths i * nth widths j
       then rel-label (edge-rel Φ i j) (nth widths i) (nth widths j)
       else "")

  Φ-of : ∀ {a} {A : Set a} {g p t} (r : A × instrument.Out Sig Dep.primitives g p t) →
         Seq g (p + proj₁ (proj₂ r))
  Φ-of r = proj₁ (proj₂ (proj₂ r))

targets : List (String × String)
targets =
  dot-of "add-full"         (Φ-of inst-add-full)
  ∷ dot-of "mult-full"        (Φ-of inst-mult-full)
  ∷ dot-of "mavg-full"        (Φ-of inst-mavg-full)
  ∷ dot-of "query-a-full"     (Φ-of inst-query-a-full)
  ∷ dot-of "query-a-marked"   (Φ-of inst-query-a-marked)
  ∷ dot-of "query-a-coarse"   (Φ-of inst-query-a-coarse)
  ∷ []

write-all : List (String × String) → IO {0ℓ} ⊤
write-all []              = pure tt
write-all ((p , s) ∷ fs) = writeFile p s >> write-all fs

main : Main
main = run (write-all targets)
