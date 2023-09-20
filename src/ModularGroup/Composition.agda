{-# OPTIONS --without-K --exact-split --safe #-}

module ModularGroup.Composition where

open import MLTT.Spartan
open import ModularGroup.Type

_·_ : 𝓜 → 𝓜 → 𝓜
η 𝐸 · y = y
η 𝑆 · y = s y
η (𝑠 x) · y = s (θ x · y)
θ (𝑟 x) · y = r (η x · y)
θ (𝑟² x) · y = r² (η x · y)

infixr 10 _·_

s-left : (a b : 𝓜) → s a · b ＝ s (a · b)
s-left (η 𝐸) b = refl
s-left (η 𝑆) b = s-quotiented b
s-left (η (𝑠 x)) b = s-quotiented (θ x · b)
s-left (θ x) b = refl

r-left : (a b : 𝓜) → r a · b ＝ r (a · b)
r-left (η x) b = refl
r-left (θ (𝑟 x)) b = refl
r-left (θ (𝑟² x)) b = r-quotiented (η x · b)

r²-left : (a b : 𝓜) → r² a · b ＝ r² (a · b)
r²-left a b = r-left (r a) b ∙ ap r (r-left a b)

composition-associative : associative _·_
composition-associative (η 𝐸) b c = refl
composition-associative (η 𝑆) b c = s-left b c
composition-associative (η (𝑠 x)) b c = s-left (θ x · b) c
                                      ∙ ap s (composition-associative (θ x) b c)
composition-associative (θ (𝑟 x)) b c = r-left (η x · b) c
                                      ∙ ap r (composition-associative (η x) b c)
composition-associative (θ (𝑟² x)) b c = r²-left (η x · b) c
                                       ∙ ap r² (composition-associative (η x) b c)

composition-left-neutral : left-neutral E _·_
composition-left-neutral x = refl

composition-right-neutral : right-neutral E _·_
composition-right-neutral (η 𝐸) = refl
composition-right-neutral (η 𝑆) = refl
composition-right-neutral (η (𝑠 x)) = ap s (composition-right-neutral (θ x))
composition-right-neutral (θ (𝑟 x)) = ap r (composition-right-neutral (η x))
composition-right-neutral (θ (𝑟² x)) = ap r² (composition-right-neutral (η x))

