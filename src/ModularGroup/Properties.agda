module ModularGroup.Properties where

open import MLTT.Spartan
open import UF.Sets
open import Groups.Type

open import ModularGroup.Type
open import ModularGroup.Composition
open import ModularGroup.Inversion

𝓜-is-set : is-set 𝓜
𝓜-is-set refl refl = refl

𝓜-has-monoid-structure : monoid-structure 𝓜
𝓜-has-monoid-structure = _·_ , E

𝓜-is-monoid : monoid-axioms 𝓜 𝓜-has-monoid-structure
𝓜-is-monoid = 𝓜-is-set , (λ x → refl)
            , composition-right-neutral
            , composition-associative

𝓜-has-group-structure : group-structure 𝓜
𝓜-has-group-structure = _·_

𝓜-is-associative : associative _·_
𝓜-is-associative x y z = composition-associative x y z

𝓜-is-group : group-axioms 𝓜 (_·_)
𝓜-is-group = 𝓜-is-set
           , composition-associative
           , E
           , (λ x → refl)
           , composition-right-neutral
           , 𝓜-invertible

⟨S,R⟩ : Group 𝓤₀
⟨S,R⟩ = 𝓜 , _·_ , 𝓜-is-group
