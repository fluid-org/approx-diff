{-# OPTIONS --prop --postfix-projections --safe #-}

-- CBN backward slice, label.a (split out so each heavy slice compiles on its own).
module example-bool-cbn-1 where

open import example-bool-cbn

input : ⟦ Tag (list (Tag (Tag (base label) [×] Tag (base number)))) ⟧ty .idx .Carrier
input = _ , 2 , (_ , (_ , a) , (_ , 0)) , (_ , (_ , b) , (_ , 1)) , _

input-ty : first-order-data (Tag (list (Tag (Tag (base label) [×] Tag (base number)))))
input-ty = Tag-ty (list (Tag-ty (Tag-ty (base label) [×] Tag-ty (base number))))

bwd-slice : _ → _
bwd-slice l =
  to-gal (ty (unit [×] input-ty) (_ , input)) (ty (Tag-ty (base number)) (_ , 0))
         (mor (cbn-query l) (_ , input)) .right .fun (⊥ , lift ·)

test : bwd-slice a ≡
  (lift · , ⊥ ,
    (⊥ , (⊥ , lift ·) , ⊥ , lift ·) ,
    (⊥ , (⊥ , lift ·) , ⊤ , lift ·) , _)
test = refl
