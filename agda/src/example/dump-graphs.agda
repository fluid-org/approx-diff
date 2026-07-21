{-# OPTIONS --prop --postfix-projections --guardedness #-}

-- Writes dot and trace renderings of the harness examples; run from the paper repository root.
module example.dump-graphs where

open import IO
open import IO.Finite using (writeFile)
open import Data.Rational using (ℚ)
open import Data.String using (String; _++_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.List using (List; []; _∷_; map)
open import Data.Nat using (_+_)
open import Data.Unit using (⊤; tt)
open import Level using (0ℓ)
open import example.signature ℚ using (Sig)
open import example.trace using (show-op; show-const; D-add; D-query)
open import example.instrument
  using (dep-edges; inst-add-full; inst-mult-full; inst-query-a-full; inst-query-a-marked;
         inst-query-a-coarse)
import example.dependency as Dep
import language-operational.instrument as instrument
open instrument Sig Dep.primitives using (Seq; seq-vals)
open import language-operational.trace Sig Dep.primitives show-op
  using (show-eval; show-val; showDotPlain)

private
  dot-of : ∀ {g n} → String → Seq g n → String × String
  dot-of name Φ =
    ("fig/dot/" ++ name ++ ".dot") ,
    showDotPlain (map (λ p → show-val (λ {s} → show-const {s}) (proj₂ p)) (seq-vals Φ))
                 (dep-edges Φ)

  Φ-of : ∀ {a} {A : Set a} {g p t} (r : A × instrument.Out Sig Dep.primitives g p t) →
         Seq g (p + proj₁ (proj₂ r))
  Φ-of r = proj₁ (proj₂ (proj₂ r))

-- The file name is the definition name without its inst- prefix.
targets : List (String × String)
targets =
  dot-of "add-full"         (Φ-of inst-add-full)
  ∷ dot-of "mult-full"        (Φ-of inst-mult-full)
  ∷ dot-of "query-a-full"     (Φ-of inst-query-a-full)
  ∷ dot-of "query-a-marked"   (Φ-of inst-query-a-marked)
  ∷ dot-of "query-a-coarse"   (Φ-of inst-query-a-coarse)
  ∷ []

write-all : List (String × String) → IO {0ℓ} ⊤
write-all []              = pure tt
write-all ((p , s) ∷ fs) = writeFile p s >> write-all fs

main : Main
main = run do
  write-all targets
  writeFile "fig/trace/add.trace" (show-eval D-add)
  writeFile "fig/trace/query-a.trace" (show-eval D-query)
