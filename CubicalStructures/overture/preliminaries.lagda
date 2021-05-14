---
layout: default
title : overture.preliminaries module (of the cubical-algebras library)
date : 2021-05-08
author: William DeMeo
---

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --cubical #-}

-- Imports from the Agda (Builtin) and the Agda Standard Library
open import Agda.Primitive using (_⊔_; lsuc)

-- Imports from Cubical Agda
open import Cubical.Core.Primitives using (_≡_; Type; Level; Σ-syntax; fst; snd; _,_)
open import Cubical.Foundations.Prelude using (refl; sym; _∙_; Lift; lift; lower)
open import Cubical.Foundations.Function using (_∘_)

module overture.preliminaries where

variable
 α β : Level

{-Pi types. The dependent function type is traditionally denoted with a Pi symbol
  typically arranged as Π(x : A) B x, or something similar.  In Agda syntax, one writes
  `(x : A) → B x` for the dependent function type, but may use syntax that is closer
  to the standard Π notation and made available in Agda as follows.-}
Π : {A : Type α } (B : A → Type β ) → Type (α ⊔ β)   -- `\lub` ↝ ⊔
Π {A = A} B = (x : A) → B x
Π-syntax : (A : Type α)(B : A → Type β) → Type (α ⊔ β)
Π-syntax A B = Π B
syntax Π-syntax A (λ x → B) = Π[ x ∈ A ] B
infix 6 Π-syntax


module _ {A : Type α }{B : A → Type β} where

 ∣_∣ : Σ[ x ∈ A ] B x → A
 ∣ x , y ∣ = x

 ∥_∥ : (z : Σ[ a ∈ A ] B a) → B ∣ z ∣
 ∥ x , y ∥ = y

 infix  40 ∣_∣ ∥_∥

_⁻¹ : {A : Type α} {x y : A} → x ≡ y → y ≡ x
p ⁻¹ = sym p
infix  40 _⁻¹

id : {A : Type α} → A → A
id x = x

𝑖𝑑 : (A : Type α ) → A → A
𝑖𝑑 A = λ x → x

lift∼lower : {A : Type α} → lift ∘ lower ≡ 𝑖𝑑 (Lift {j = β} A)
lift∼lower = refl

lower∼lift : {A : Type α} → lower {α}{β}(lift {α}{β}(λ x → x)) ≡ 𝑖𝑑 A
lower∼lift = refl

_≈_ : {A : Type α } {B : A → Type β } → Π B → Π B → Type (α ⊔ β)
f ≈ g = ∀ x → f x ≡ g x

infix 8 _≈_

\end{code}

-------------------------------------------------------------------
--                        THE END                                --
-------------------------------------------------------------------






























<!-- no longer used or needed ---------------------------------------------

-- id : {A : Type 𝓤} → A → A
-- id x = x

-- infixl 30 _∙_
-- infixr  0 _≡⟨_⟩_
-- infix   1 _∎



-- Type : (𝓤 : Level) → Set (ℓ-suc 𝓤)
-- Type 𝓤 = Set 𝓤

-- Type₀ : Type (ℓ-suc lzero)
-- Type₀ = Set

-- -Σ : {𝓤 𝓥 : Level} (A : Type 𝓤 ) (B : A → Type 𝓥 ) → Type(ℓ-max 𝓤 𝓥)
-- -Σ = Σ

-- syntax -Σ A (λ x → B) = Σ[ x ꞉ A ] B    -- type \:4 to get ꞉

-- infixr 3 -Σ

-- module _ {A : Type 𝓤 }{B : A → Type 𝓥} where

--  ∣_∣ : Σ[ x ∈ A ] B x → A
--  ∣ x , y ∣ = x
--  -- fst (x , y) = x

--  ∥_∥ : (z : Σ[ a ∈ A ] B a) → B ∣ z ∣
--  ∥ x , y ∥ = y
--  -- snd (x , y) = y

--  infix  40 ∣_∣ ∥_∥
-- _∙_ : {A : Type 𝓤}{x y z : A} → x ≡ y → y ≡ z → x ≡ z
-- p ∙ q = trans p q

-- _≡⟨_⟩_ : {A : Type 𝓤} (x : A) {y z : A} → x ≡ y → y ≡ z → x ≡ z
-- x ≡⟨ p ⟩ q = p ∙ q

-- _∎ : {X : Type 𝓤} (x : X) → x ≡ x
-- x ∎ = refl


-- open import Cubical.Foundations.Equiv
-- open import Cubical.Foundations.Equiv.HalfAdjoint
-- open import Cubical.Foundations.HLevels
-- open import Cubical.Foundations.Isomorphism
-- open import Cubical.Foundations.SIP
-- open import Cubical.Displayed.Base
-- open import Cubical.Displayed.Auto
-- open import Cubical.Displayed.Record
-- open import Cubical.Displayed.Universe

-- open import Cubical.Reflection.RecordEquiv
-- -- Imports from the Agda (Builtin) and the Agda Standard Library
-- -- open import Agda.Builtin.Equality using (_≡_; refl)
-- open import Cubical.Foundations.Prelude using (i0; i1; _≡_; refl)
-- open import Data.Product using (_,_; Σ; Σ-syntax; _×_)
-- open import Function using (_∘_)
-- open import Level renaming (suc to lsuc; zero to lzero)
-- -- open import Relation.Binary.PropositionalEquality.Core using (sym; trans)
-- import Agda.Builtin.Cubical.HCompU as HCompU

-- module Helpers = HCompU.Helpers

-- open Helpers


--------------------------------------------------------------- -->
