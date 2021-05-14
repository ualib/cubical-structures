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
open import Cubical.Core.Primitives using (_≡_; Type; Level;Σ-syntax; fst; snd; _,_)
-- open import Cubical.Core.Primitives using (_≡_; Type; Level; i0; i1
open import Cubical.Foundations.Prelude using (refl; sym; _∙_; Lift; lift; lower)
open import Cubical.Foundations.Function using (_∘_)

module overture.preliminaries where

variable
 α β γ δ ι 𝓘 𝓞 𝓠 𝓡 𝓢 𝓣 𝓤 𝓥 𝓦 𝓧 𝓨 𝓩 : Level

Π : {A : Type 𝓤 } (B : A → Type 𝓦 ) → Type (𝓤 ⊔ 𝓦)
Π {A = A} B = (x : A) → B x

-Π : (A : Type 𝓤 )(B : A → Type 𝓦 ) → Type(𝓤 ⊔ 𝓦)
-Π A B = Π B

infixr 6 -Π
syntax -Π A (λ x → B) = Π[ x ꞉ A ] B  -- type \,3 to get ⸲


module _ {A : Type 𝓤 }{B : A → Type 𝓥} where

 ∣_∣ : Σ[ x ∈ A ] B x → A
 ∣ x , y ∣ = x

 ∥_∥ : (z : Σ[ a ∈ A ] B a) → B ∣ z ∣
 ∥ x , y ∥ = y

 infix  40 ∣_∣ ∥_∥

_⁻¹ : {A : Type 𝓤} {x y : A} → x ≡ y → y ≡ x
p ⁻¹ = sym p
infix  40 _⁻¹

id : {A : Type 𝓤} → A → A
id x = x

𝑖𝑑 : (A : Type 𝓤 ) → A → A
𝑖𝑑 A = λ x → x

lift∼lower : ∀ {𝓤 𝓦}{A : Type 𝓤} → lift ∘ lower ≡ 𝑖𝑑 (Lift {j = 𝓦} A)
lift∼lower = refl

lower∼lift : {𝓤 𝓦 : Level}{A : Type 𝓤} → lower {𝓤}{𝓦}(lift {𝓤}{𝓦}(λ x → x)) ≡ 𝑖𝑑 A
lower∼lift = refl

_≈_ : {X : Type 𝓤 } {A : X → Type 𝓥 } → Π A → Π A → Type (𝓤 ⊔ 𝓥)
f ≈ g = ∀ x → f x ≡ g x

infix 8 _≈_

\end{code}

-------------------------

{% include cubical-algebras.links.md %}

[agda-algebras]: https://github.com/ualib/agda-algebras

















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
