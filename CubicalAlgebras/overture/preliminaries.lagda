---
layout: default
title : overture.preliminaries module (of the cubical-algebras library)
date : 2021-05-08
author: William DeMeo
---

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --cubical #-}

-- Imports from the Agda (Builtin) and the Agda Standard Library
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_,_; Σ; Σ-syntax; _×_)
open import Function using (_∘_)
open import Level renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality.Core using (sym; trans)

module overture.preliminaries where


Type : (𝓤 : Level) → Set (lsuc 𝓤)
Type 𝓤 = Set 𝓤

Type₀ : Type (lsuc lzero)
Type₀ = Set

variable
 𝓘 𝓞 𝓠 𝓡 𝓢 𝓣 𝓤 𝓥 𝓦 𝓧 𝓨 𝓩 : Level


-Σ : {𝓤 𝓥 : Level} (A : Type 𝓤 ) (B : A → Type 𝓥 ) → Type(𝓤 ⊔ 𝓥)
-Σ = Σ

syntax -Σ A (λ x → B) = Σ[ x ꞉ A ] B    -- type \:4 to get ꞉

infixr 3 -Σ

Π : {A : Type 𝓤 } (B : A → Type 𝓦 ) → Type (𝓤 ⊔ 𝓦)
Π {A = A} B = (x : A) → B x

-Π : (A : Type 𝓤 )(B : A → Type 𝓦 ) → Type(𝓤 ⊔ 𝓦)
-Π A B = Π B

infixr 3 -Π
syntax -Π A (λ x → B) = Π[ x ꞉ A ] B  -- type \,3 to get ⸲

module _ {A : Type 𝓤 }{B : A → Type 𝓥} where

 ∣_∣ fst : Σ[ x ∈ A ] B x → A
 ∣ x , y ∣ = x
 fst (x , y) = x

 ∥_∥ snd : (z : Σ[ a ∈ A ] B a) → B ∣ z ∣
 ∥ x , y ∥ = y
 snd (x , y) = y

 infix  40 ∣_∣

_⁻¹ : {A : Type 𝓤} {x y : A} → x ≡ y → y ≡ x
p ⁻¹ = sym p

infix  40 _⁻¹

_∙_ : {A : Type 𝓤}{x y z : A} → x ≡ y → y ≡ z → x ≡ z
p ∙ q = trans p q

_≡⟨_⟩_ : {A : Type 𝓤} (x : A) {y z : A} → x ≡ y → y ≡ z → x ≡ z
x ≡⟨ p ⟩ q = p ∙ q

_∎ : {X : Type 𝓤} (x : X) → x ≡ x
x ∎ = refl


𝑖𝑑 : (A : Type 𝓤 ) → A → A
𝑖𝑑 A = λ x → x

id : {A : Type 𝓤} → A → A
id x = x

infixl 30 _∙_
infixr  0 _≡⟨_⟩_
infix   1 _∎


lift∼lower : ∀ {𝓤 𝓦}{A : Type 𝓤} → lift ∘ lower ≡ 𝑖𝑑 (Lift 𝓦 A)
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

