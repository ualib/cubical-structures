---
layout: default
title : Relations.Quotients module (The Agda Universal Algebra Library)
date : 2021-01-13
author: William DeMeo
---

### <a id="equivalence-relations-and-quotients">Equivalence Relations and Quotients</a>

This section presents the [Relations.Quotients][] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --cubical #-}

-- Imports from the Agda (Builtin) and the Agda Standard Library
open import Agda.Primitive using (_⊔_; lsuc)
open import Relation.Unary using (Pred; _∈_; _⊆_)
open import Function.Base using (_on_)

-- Imports from Cubical Agda
open import Cubical.Core.Primitives using (_≡_; Type; Level; _,_; Σ-syntax; Typeω)
open import Cubical.Foundations.Prelude using (refl; sym; _∙_; cong)
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Relation.Binary.Base as CBinary renaming (Rel to REL) using (EquivRel)
open CBinary.BinaryRelation renaming (isEquivRel to IsEquivalence)

open import Cubical.Data.Sigma using (_×_)

open import overture.preliminaries using (𝓤; 𝓥; 𝓦; 𝓧; 𝓨; 𝓩)
open import relations.discrete using (ker; Rel)


module relations.quotients where


Refl : {A : Type 𝓤} → Rel A 𝓦 → Type(𝓤 ⊔ 𝓦)
Refl _≈_ = ∀{x} → x ≈ x

Symm : {A : Type 𝓤} → Rel A 𝓦 → Type(𝓤 ⊔ 𝓦)
Symm _≈_ = ∀{x}{y} → x ≈ y → y ≈ x

Antisymm : {A : Type 𝓤} → Rel A 𝓦 → Type(𝓤 ⊔ 𝓦)
Antisymm _≈_ = ∀{x}{y} → x ≈ y → y ≈ x → x ≡ y

Trans : {A : Type 𝓤} → Rel A 𝓦 → Type(𝓤 ⊔ 𝓦)
Trans _≈_ = ∀{x}{y}{z} → x ≈ y → y ≈ z → x ≈ z

Equivalence : {𝓤 : Level} → Type 𝓤 → Type (lsuc 𝓤)
Equivalence {𝓤} A = Σ[ r ∈ Rel A 𝓤 ] IsEquivalence r

\end{code}


\begin{code}

module _ {I : Type 𝓥} {A : Type 𝓤 } where

 𝟎 : Rel (I → A) (𝓥 ⊔ 𝓤)
 𝟎 x y = ∀ i → x i ≡ y i


 𝟎-IsEquivalence : IsEquivalence 𝟎
 𝟎-IsEquivalence = equivRel
                   (λ a i _ → a i)                        -- reflexive
                   (λ a b p i i₁ → sym (p i) i₁)          -- symmetric
                   (λ a b c p q i i₁ → ((p i)∙(q i)) i₁)  -- transitive

 𝟎-IsEquivalence' : IsEquivalence 𝟎
 𝟎-IsEquivalence' = record {reflexive = λ a i → refl; symmetric = λ a b x i → sym (x i) ; transitive = λ a b c x y i → (x i ∙ y i) }


𝟎-is-smallest : Typeω
𝟎-is-smallest = ∀{𝓥}{𝓤}{𝓦}{I : Type 𝓥}{A : Type 𝓤}(ρ : Rel (I → A) 𝓦) → IsEquivalence ρ → (x y : I → A) → 𝟎 x y → ρ x y


ker-IsEquivalence : {A : Type 𝓤}{B : Type 𝓦}(f : A → B) → IsEquivalence (ker f)
ker-IsEquivalence f = record { reflexive = λ a i → f a ; symmetric = λ a b → sym ; transitive = λ a b c → _∙_ }


kernel-lemma : {𝓥 𝓤 : Level} → 𝟎-is-smallest → {I : Type 𝓥}{A : Type 𝓤}(f : (I → A) → A)(x y : I → A)
 →             (∀ i → x i ≡ y i) → (ker f) x y
kernel-lemma {𝓥}{𝓤} 0min {I = I}{A = A} f x y hyp = 0min (ker f) (ker-IsEquivalence{𝓤 = (𝓥 ⊔ 𝓤)}{A = (I → A)} f) x y hyp


[_] : {A : Type 𝓤} → A → {R : Rel A 𝓦} → Pred A 𝓦
[ u ]{R} = R u

infix 60 [_]


IsBlock : {A : Type 𝓤}(C : Pred A 𝓦){R : Rel A 𝓦} → Type(𝓤 ⊔ lsuc 𝓦)
IsBlock {A = A} C {R} = Σ[ u ∈ A ] C ≡ [ u ]{R}



module _ {𝓤 𝓦 : Level} where

 _/_ : (A : Type 𝓤 ) → Rel A 𝓦 → Type(𝓤 ⊔ lsuc 𝓦)
 A / R = Σ[ C ∈ Pred A 𝓦 ] IsBlock C {R}

 infix -1 _/_


⟪_⟫ : {A : Type 𝓤} → A → {R : Rel A 𝓦} → A / R
⟪ a ⟫{R} = [ a ]{R} , (a  , refl)

⌞_⌟ : {A : Type 𝓤}{R : Rel A 𝓦} → A / R  → A
⌞ C , a , p ⌟ = a

open IsEquivalence

/-subset : {𝓤 : Level}{A : Type 𝓤}{x y : A}{R : Rel A 𝓦}
 →         IsEquivalence R → R x y →  [ x ]{R} ⊆ [ y ]{R}
/-subset {x = x}{y = y}  Req  Rxy {z}  Rxz  =
 transitive Req y x z (symmetric Req x y Rxy) Rxz -- C-c C-a automatic proof

/-supset : {𝓤 : Level}{A : Type 𝓤}{x y : A}{R : Rel A 𝓦}
 →         IsEquivalence R → R x y →  [ y ]{R} ⊆ [ x ]{R}
/-supset {x = x}{y = y} Req Rxy {z} Ryz =
 transitive Req x y z Rxy Ryz  -- C-c C-a proves this automatically

\end{code}


An example application of these is the `block-ext` type in the [Relations.Extensionality] module.

--------------------------------------


<sup>1</sup><span class="footnote" id="fn1">**Unicode Hints** ([agda2-mode][]). `\cl ↝ ⌞`; `\clr ↝ ⌟`.</span>


<br>
<br>

{% include UALib.Links.md %}











<!-- NO LONGER NEEDED ------------------------------------------------------------


open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Primitive using (_⊔_; lzero; lsuc; Level; Setω)
open import Data.Product  using (_,_; Σ; Σ-syntax; _×_)
open import Relation.Binary using (Rel; IsEquivalence)
open import Relation.Binary.PropositionalEquality using (sym; trans)
open import Relation.Unary using (Pred; _⊆_)

---------------------------------------------------------------------------- -->
