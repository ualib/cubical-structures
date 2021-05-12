---
layout: default
title : sturctures.products module (cubical-structures library)
date : 2021-05-11
author: William DeMeo
---

### Product structures

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --cubical #-}

open import Agda.Primitive using (_⊔_; lsuc)
open import Relation.Unary using (Pred; _∈_)

open import Cubical.Core.Primitives using (_≡_; Type; Level; Σ-syntax;  i0; i1; fst; snd; _,_)
open import Cubical.Foundations.Prelude using (refl; sym; _∙_; funExt; cong; _∎; _≡⟨_⟩_)
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Data.Sigma.Base using (_×_)

-- Imports from the Agda Universal Algebra Library
open import overture.preliminaries using (𝓘; 𝓞; 𝓤; 𝓥; 𝓦; 𝓧; 𝓨; 𝓩; Π; -Π; _⁻¹; id; ∣_∣)
open import structures.basic
open import overture.inverses using (IsInjective; IsSurjective)
open import relations.discrete using (ker)


module structures.products  where

module _ {𝑅 𝐹 : Signature}{ρ β ι : Level} where

 ⨅ : (ℑ : Type ι)(ℬ : ℑ → Structure {ρ} β 𝑅 𝐹) → Structure (β ⊔ ι) 𝑅 𝐹

 ⨅ ℑ ℬ =
  Π[ 𝔦 ꞉ ℑ ] ∣ ℬ 𝔦 ∣ ,                     -- domain of the product structure
  ( λ r 𝑎 → ∀ 𝔦 → (r ʳ ℬ 𝔦) λ x → 𝑎 x 𝔦 ) , -- interpretations of relations
  ( λ 𝑓 𝑎 𝔦 → (𝑓 ᵒ ℬ 𝔦) λ x → 𝑎 x 𝔦 )        -- interpretations of  operations

 -- Alternative notation for the domain of the product is `∀ 𝔦 → ∣ ℬ 𝔦 ∣`.


module _ {𝑅 𝐹 : Signature}{ρ β : Level}{𝒦 : Pred (Structure {ρ} β 𝑅 𝐹) (lsuc β)} where

 ℑ : Type (lsuc (ρ ⊔ β))
 ℑ = Σ[ 𝑨 ∈ Structure β 𝑅 𝐹 ] 𝑨 ∈ 𝒦

 𝔄 : ℑ → Structure β 𝑅 𝐹
 𝔄 𝔦 = ∣ 𝔦 ∣

 class-prod : Structure  (lsuc (ρ ⊔ β)) 𝑅 𝐹
 class-prod = ⨅ ℑ 𝔄

\end{code}

If `p : 𝑨 ∈ 𝒦`, we view the pair `(𝑨 , p) ∈ ℑ` as an *index* over the class, so we can think of `𝔄 (𝑨 , p)` (which is simply `𝑨`) as the projection of the product `⨅ 𝔄` onto the `(𝑨 , p)`-th component.


#### Representing structures with record types

\begin{code}

module _ {𝑅 𝐹 : signature}{ρ β ι : Level} where
 open structure

 ⨅' : (ℑ : Type ι)(ℬ : ℑ → structure {ρ} β 𝑅 𝐹) → structure (β ⊔ ι) 𝑅 𝐹
 ⨅' ℑ ℬ = record
           { univ       = Π[ 𝔦 ꞉ ℑ ] univ (ℬ 𝔦)                       -- domain of the product structure
           ; relation   = λ r 𝑎 → ∀ 𝔦 → relation (ℬ 𝔦) r (λ x → 𝑎 x 𝔦) -- interpretations of relations
           ; operation  = λ f 𝑎 𝔦 → operation (ℬ 𝔦) f (λ x → 𝑎 x 𝔦)    -- interpretations of operations
           }

module _ {𝑅 𝐹 : signature}{ρ β ι : Level} {𝒦 : Pred (structure β 𝑅 𝐹) (lsuc β)} where

  ℑ' : Type (lsuc (ρ ⊔ β))
  ℑ' = Σ[ 𝑨 ∈ structure {ρ} β 𝑅 𝐹 ] 𝑨 ∈ 𝒦

  𝔄' : ℑ' → structure β 𝑅 𝐹
  𝔄' 𝔦 = ∣ 𝔦 ∣

  class-prod' : structure (lsuc (ρ ⊔  β)) 𝑅 𝐹
  class-prod' = ⨅' ℑ' 𝔄'

\end{code}

-----------------------

<sup>1</sup><span class="footnote" id="fn1"> If you haven't seen this before, give it some thought and see if the correct type comes to you organically.</span>

<sup>2</sup><span class="footnote" id="fn2"> **Unicode Hints**. Some of our types are denoted with with Gothic ("mathfrak") symbols. To produce them in [agda2-mode][], type `\Mf` followed by a letter. For example, `\MfI` ↝ `ℑ`.</span>

[← Algebras.Basic](Algebras.Basic.html)
<span style="float:right;">[Algebras.Congruences →](Algebras.Congruences.html)</span>

{% include UALib.Links.md %}























-- Imports from the Agda (Builtin) and the Agda Standard Library
-- open import Level renaming (suc to lsuc; zero to lzero)
-- open import Data.Product using (_,_; Σ; _×_)
-- open import Relation.Unary using (Pred; _∈_)

-- Imports from the Agda Universal Algebra Library
-- open import Overture.Preliminaries using (Type; 𝓘; 𝓞; 𝓤; 𝓥; 𝓦; Π; -Π; -Σ; _≡⟨_⟩_; _∎; _⁻¹; 𝑖𝑑; ∣_∣; ∥_∥)
-- open import Algebras.Basic


-- open import Relation.Binary using (Rel; IsEquivalence)
-- open import Relation.Binary.PropositionalEquality.Core using (trans)

