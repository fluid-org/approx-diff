{-# OPTIONS --prop --postfix-projections --safe #-}

------------------------------------------------------------------------------
-- Fibre action in an ambient context over an index-only reindex. `abase`
-- supplies a fibre map under the context fibre G for each variable, together
-- with its naturality in the tree; `abind` extends across a binder. The
-- morphisms are first-order data so the recursion stays structural. Taking G
-- to be the terminal object recovers a context-free fibre action.
------------------------------------------------------------------------------

open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Data.Nat using (ℕ; suc)
import Data.Fin as Fin
open Fin using (Fin)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import prop using (_,_)
open import categories using (Category; HasTerminal; HasProducts)
import fam-mu-types.reindex

module fam-mu-types.action {o m e} (os es : Level) {𝒞 : Category o m e}
    (T : HasTerminal 𝒞) (P : HasProducts 𝒞) where

open fam-mu-types.reindex os es T P public

-- The action lives over a fixed pair of parameter contexts and a fixed
-- ambient context fibre G.
module Action {nA nB} {δA : Fin nA → Obj} {δB : Fin nB → Obj} (G : obj) where
  private
    module TA = Tree δA
    module TB = Tree δB
  open Reindex δA δB using (IMorD; ibase; ibind; ireindex; ireindex-shape; iapply;
                            ireindex-resp; ireindex-shape-resp; iapply-resp)

  data Act : ∀ {k} {ρA : Fin k → Fin nA ⊎ Sort nA} {ρB : Fin k → Fin nB ⊎ Sort nB} →
             IMorD ρA ρB → (∀ v → TA.DecoAssign (ρA v)) → (∀ v → TB.DecoAssign (ρB v)) →
             Set (o ⊔ m ⊔ e ⊔ lsuc os ⊔ lsuc es) where
    abase : ∀ {k} {ρA ρB} {cmb : IMorD {k} ρA ρB} {dA dB}
            (afib : ∀ v (a : TA.El (ρA v)) →
                    prod G (TA.fib-el (ρA v) (dA v) a) ⇒ TB.fib-el (ρB v) (dB v) (iapply cmb v a))
            (afib-natural : ∀ v {a a'} (p : TA.elEq (ρA v) a a') →
                    (afib v a' ∘ prod-m (id G) (TA.fib-el-subst (ρA v) (dA v) p))
                      ≈ (TB.fib-el-subst (ρB v) (dB v) (iapply-resp cmb v p) ∘ afib v a)) →
            Act cmb dA dB
    abind : ∀ {k} {ρA ρB} (Q : Poly (suc k)) (cmb : IMorD ρA ρB) {dA dB} → Act cmb dA dB →
            Act (ibind ∣ Q ∣ cmb) (TA.deco-ext Q dA) (TB.deco-ext Q dB)

  mutual
    act-fam : ∀ {k} {Q : Poly (suc k)} {ρA ρB} {cmb : IMorD ρA ρB} {dA dB} (act : Act cmb dA dB)
              {t : TA.W ∣ Q ∣ ρA} → prod G (TA.fib Q dA t) ⇒ TB.fib Q dB (ireindex cmb t)
    act-fam {Q = Q} {cmb = cmb} act {TA.sup x} = act-shape-fam Q (abind Q cmb act) {x}

    act-shape-fam : ∀ {j} (R : Poly j) {ηA ηB} {cmb : IMorD ηA ηB} {dA dB} (act : Act cmb dA dB)
                    {a : TA.⟦ ∣ R ∣ ⟧shape ηA} →
                    prod G (TA.fib-shape R dA a) ⇒ TB.fib-shape R dB (ireindex-shape ∣ R ∣ cmb a)
    act-shape-fam (const A') act = p₂
    act-shape-fam (var v)    act {a} = act-apply act v a
    act-shape-fam (P + Q) act {inj₁ a} = act-shape-fam P act {a}
    act-shape-fam (P + Q) act {inj₂ b} = act-shape-fam Q act {b}
    act-shape-fam (P × Q) act {a , b} =
      strong-prod-m (act-shape-fam P act {a}) (act-shape-fam Q act {b})
    act-shape-fam (μ Q') act {t} = act-fam act {t}

    act-apply : ∀ {k} {ρA ρB} {cmb : IMorD {k} ρA ρB} {dA dB} (act : Act cmb dA dB) (v : Fin k)
                (a : TA.El (ρA v)) →
                prod G (TA.fib-el (ρA v) (dA v) a) ⇒ TB.fib-el (ρB v) (dB v) (iapply cmb v a)
    act-apply (abase afib _)     v           a = afib v a
    act-apply (abind Q cmb act) Fin.zero    a = act-fam act {a}
    act-apply (abind Q cmb act) (Fin.suc v) a = act-apply act v a

  -- The action commutes with subst in the tree.
  mutual
    act-fam-natural : ∀ {k} {Q : Poly (suc k)} {ρA ρB} {cmb : IMorD ρA ρB} {dA dB}
                      (act : Act cmb dA dB) {t t' : TA.W ∣ Q ∣ ρA} (p : TA.W-≈ t t') →
                      (act-fam act {t'} ∘ prod-m (id G) (TA.fib-subst Q dA {x = t} {y = t'} p))
                        ≈ (TB.fib-subst Q dB {x = ireindex cmb t} {y = ireindex cmb t'}
                                        (ireindex-resp cmb {t} {t'} p) ∘ act-fam act {t})
    act-fam-natural {Q = Q} {cmb = cmb} act {TA.sup x} {TA.sup y} p =
      act-shape-fam-natural Q (abind Q cmb act) {x} {y} p

    act-shape-fam-natural : ∀ {j} (R : Poly j) {ηA ηB} {cmb : IMorD ηA ηB} {dA dB}
                            (act : Act cmb dA dB) {a a' : TA.⟦ ∣ R ∣ ⟧shape ηA}
                            (p : TA.shape≈ ∣ R ∣ ηA a a') →
                            (act-shape-fam R act {a'} ∘ prod-m (id G) (TA.fib-shape-subst R dA p))
                              ≈ (TB.fib-shape-subst R dB (ireindex-shape-resp ∣ R ∣ cmb p)
                                   ∘ act-shape-fam R act {a})
    act-shape-fam-natural (const A') act p = pair-p₂ _ _
    act-shape-fam-natural (var v)    act {a} {a'} p = act-apply-natural act v {a} {a'} p
    act-shape-fam-natural (P + Q) act {inj₁ _} {inj₁ _} p = act-shape-fam-natural P act p
    act-shape-fam-natural (P + Q) act {inj₂ _} {inj₂ _} p = act-shape-fam-natural Q act p
    act-shape-fam-natural (P × Q) act {_ , _} {_ , _} (p₁p , p₂p) =
      strong-prod-m-natural (act-shape-fam-natural P act p₁p) (act-shape-fam-natural Q act p₂p)
    act-shape-fam-natural (μ Q') act {t} {t'} p = act-fam-natural act {t} {t'} p

    act-apply-natural : ∀ {k} {ρA ρB} {cmb : IMorD {k} ρA ρB} {dA dB} (act : Act cmb dA dB)
                        (v : Fin k) {a a'} (p : TA.elEq (ρA v) a a') →
                        (act-apply act v a' ∘ prod-m (id G) (TA.fib-el-subst (ρA v) (dA v) p))
                          ≈ (TB.fib-el-subst (ρB v) (dB v) (iapply-resp cmb v p) ∘ act-apply act v a)
    act-apply-natural (abase _ afib-natural) v p = afib-natural v p
    act-apply-natural (abind Q cmb act) Fin.zero    {a} {a'} p = act-fam-natural act {a} {a'} p
    act-apply-natural (abind Q cmb act) (Fin.suc v) p = act-apply-natural act v p
