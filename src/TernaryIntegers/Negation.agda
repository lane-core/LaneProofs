{-# OPTIONS --without-K --exact-split --safe --no-sized-types --no-guardedness --auto-inline #-}

open import UF.FunExt

module TernaryIntegers.Negation where

open import MLTT.Spartan
open import TernaryIntegers.Type public

-_ : ℤ → ℤ
- zero = zero
- η one = η negone
- η negone = η one
- η (L x) = rr (- (η x))
- η (T x) = tt (- (η x))
- η (R x) = ll (- (η x))
