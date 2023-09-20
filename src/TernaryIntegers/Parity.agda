{-# OPTIONS --without-K --exact-split --safe --no-sized-types --no-guardedness --auto-inline #-}

open import UF.FunExt

module TernaryIntegers.Parity where

open import MLTT.Spartan
open import TernaryIntegers.Type public


ℤeven ℤodd : ℤ → 𝓤₀ ̇
ℤeven-succ : (x : ℤ) → ℤeven x → ℤodd (succℤ x)
ℤodd-succ : (x : ℤ) → ℤodd x → ℤeven (succℤ x)
ℤeven-succ zero e = {!!}
ℤeven-succ (η (L x)) e = {!!}
ℤeven-succ (η (T x)) e = {!!}
ℤeven-succ (η (R x)) e = {!!}
ℤodd-succ x o = {!!}

ℤeven zero = 𝟙
ℤeven (η one) = 𝟘
ℤeven (η negone) = 𝟘
ℤeven (η (L x)) = ℤodd (η x)
ℤeven (η (T x)) = ℤeven (η x)
ℤeven (η (R x)) = ℤodd (η x)
ℤodd zero = 𝟘
ℤodd (η one) = 𝟙
ℤodd (η negone) = 𝟙
ℤodd (η (L x)) = ℤeven (η x)
ℤodd (η (T x)) = ℤodd (η x)
ℤodd (η (R x)) = ℤeven (η x)
