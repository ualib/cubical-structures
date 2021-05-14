---
layout: default
title : relations.continuous
date : 2021-05-08
author: William DeMeo
---

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --cubical #-}


-- Imports from the Agda (Builtin) and the Agda Standard Library
open import Agda.Primitive using (_⊔_; lsuc)

-- Imports from Cubical Agda
open import Cubical.Core.Primitives using (Type; Level)
open import Cubical.Foundations.Prelude using (_≡_; refl)

open import relations.discrete using (Op)


module relations.continuous where

variable
 𝓤 𝓥 𝓦 : Level

ContRel : Type 𝓥 → Type 𝓤 → (𝓦 : Level) → Type(𝓤 ⊔ 𝓥 ⊔ lsuc 𝓦)
ContRel I A 𝓦 = (I → A) → Type 𝓦

DepRel : (I : Type 𝓥) → (I → Type 𝓤) → (𝓦 : Level) → Type(𝓤 ⊔ 𝓥 ⊔ lsuc 𝓦)
DepRel I 𝒜 𝓦 = ((i : I) → 𝒜 i) → Type 𝓦

module _ {I J : Type 𝓥} {A : Type 𝓤} where

 eval-cont-rel : ContRel I A 𝓦 → (I → J → A) → Type(𝓥 ⊔ 𝓦)
 eval-cont-rel R 𝒶 = ∀ (j : J) → R λ i → 𝒶 i j

 cont-compatible-op : Op J A → ContRel I A 𝓦 → Type(𝓥 ⊔ 𝓤 ⊔ 𝓦)
 cont-compatible-op 𝑓 R  = ∀ (𝒶 : (I → J → A)) → (eval-cont-rel R 𝒶 → R λ i → (𝑓 (𝒶 i)))

module _ {I J : Type 𝓥} {𝒜 : I → Type 𝓤} where

 eval-dep-rel : DepRel I 𝒜 𝓦 → (∀ i → (J → 𝒜 i)) → Type(𝓥 ⊔ 𝓦)
 eval-dep-rel R 𝒶 = ∀ j → R (λ i → (𝒶 i) j)

 dep-compatible-op : (∀ i → Op J (𝒜 i)) → DepRel I 𝒜 𝓦 → Type(𝓥 ⊔ 𝓤 ⊔ 𝓦)
 dep-compatible-op 𝑓 R  = ∀ 𝒶 → (eval-dep-rel R) 𝒶 → R λ i → (𝑓 i)(𝒶 i)

\end{code}

-------------------------------------------------------------------
--                        THE END                                --
-------------------------------------------------------------------

