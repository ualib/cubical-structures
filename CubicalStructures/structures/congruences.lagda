---
layout: default
title : structures.congruences module (cubical-structures library)
date : 2021-05-12
author: William DeMeo
---

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --cubical #-}

open import Agda.Primitive using (_⊔_; lsuc)
open import Relation.Unary using (Pred; _∈_)

open import Cubical.Core.Primitives using (_≡_; Type; Level; Σ-syntax;  i0; i1; fst; snd; _,_)
open import Cubical.Data.Sigma.Base using (_×_)
open import Cubical.Foundations.Prelude using (refl; sym; _∙_; funExt; cong; _∎; _≡⟨_⟩_)
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Relation.Binary.Base as CBinary renaming (Rel to REL) using (EquivRel)
open CBinary.BinaryRelation renaming (isEquivRel to IsEquivalence)

-- Imports from the Agda Universal Algebra Library
open import overture.preliminaries using (𝓘; 𝓞; 𝓤; 𝓥; 𝓦; 𝓧; 𝓨; 𝓩; Π; -Π; _⁻¹; id; ∣_∣)
open import structures.basic
open import overture.inverses using (IsInjective; IsSurjective)
open import relations.discrete renaming (Rel to BinRel) using (𝟎;_|:_; ker)
-- open import Relations.Quotients using (_/_; ⟪_⟫)
-- open import structures.products



module structures.congruences {𝑅 𝐹 : Signature} where

record IsCongruence {α : Level}(𝑨 : Structure 𝑅 𝐹 {α})(θ : BinRel ∣ 𝑨 ∣ α) : Type (lsuc α)  where
 constructor mkcon
 field       is-equivalence : IsEquivalence θ
             is-compatible  : compatible 𝑨 θ

open IsCongruence

Con : {α : Level}(𝑨 : Structure 𝑅 𝐹 {α}) → Type (lsuc α)
Con {α} 𝑨 = Σ[ θ ∈ (BinRel ∣ 𝑨 ∣ α) ] IsCongruence 𝑨 θ

\end{code}

Each of these types captures what it means to be a congruence and they are equivalent in the sense that each implies the other. One implication is the "uncurry" operation and the other is the second projection.

\begin{code}

module _ {α : Level} {𝑨 : Structure 𝑅 𝐹 {α}} where

 IsCongruence→Con : (θ : BinRel ∣ 𝑨 ∣ α) → IsCongruence 𝑨 θ → Con 𝑨
 IsCongruence→Con θ p = θ , p

 Con→IsCongruence : ((θ , _) : Con 𝑨) → IsCongruence 𝑨 θ
 Con→IsCongruence θ = snd θ

open IsEquivalence

𝟎-IsEquivalence : {A : Type 𝓤} →  IsEquivalence {A = A} 𝟎
𝟎-IsEquivalence = record { reflexive = λ a _ → a
                         ; symmetric = λ _ _ x i → sym x i
                         ; transitive = λ _ _ _ 0ab 0bc i → (0ab ∙ 0bc) i
                         }


module _ {α : Level} {𝑨 : Structure 𝑅 𝐹 {α}} where
 𝟎-compatible-op : (𝑓 : ∣ 𝐹 ∣) → (𝑓 ᵒ 𝑨) |: 𝟎
 𝟎-compatible-op 𝑓 {i}{j} ptws0  = cong (𝑓 ᵒ 𝑨) (funExt ptws0)

 𝟎-compatible :  compatible 𝑨 𝟎
 𝟎-compatible = λ 𝑓 x → 𝟎-compatible-op 𝑓 x

 Δ : IsCongruence 𝑨 𝟎
 Δ = mkcon 𝟎-IsEquivalence 𝟎-compatible

 -- 𝟘 : IsCongruence 𝑨 𝟎 → Con 𝑨
 -- 𝟘 = IsCongruence→Con 𝟎 Δ

\end{code}


A concrete example is `⟪𝟎⟫[ 𝑨 ╱ θ ]`, presented in the next subsection.

#### <a id="quotient-algebras">Quotient algebras</a>
In many areas of abstract mathematics the *quotient* of an algebra `𝑨` with respect to a congruence relation `θ` of `𝑨` plays an important role. This quotient is typically denoted by `𝑨 / θ` and Agda allows us to define and express quotients using this standard notation.<sup>[1](Algebras.Congruences.html#fn1)</sup>


_╱_ : (𝑨 : Algebra 𝓤 𝑆) → Con{𝓤}{𝓦} 𝑨 → Algebra (𝓤 ⊔ lsuc 𝓦) 𝑆

𝑨 ╱ θ = (∣ 𝑨 ∣ / ∣ θ ∣)  ,                               -- the domain of the quotient algebra
        λ 𝑓 𝑎 → ⟪ (𝑓 ̂ 𝑨)(λ i →  fst ∥ 𝑎 i ∥) ⟫           -- the basic operations of the quotient algebra

\end{code}

**Example**. If we adopt the notation `𝟎[ 𝑨 ╱ θ ]` for the zero (or identity) relation on the quotient algebra `𝑨 ╱ θ`, then we define the zero relation as follows.



𝟘[_╱_] : (𝑨 : Algebra 𝓤 𝑆)(θ : Con{𝓤}{𝓦} 𝑨) → Rel (∣ 𝑨 ∣ / ∣ θ ∣)(𝓤 ⊔ lsuc 𝓦)
𝟘[ 𝑨 ╱ θ ] = λ u v → u ≡ v

\end{code}

From this we easily obtain the zero congruence of `𝑨 ╱ θ` by applying the `Δ` function defined above.


𝟎[_╱_] : (𝑨 : Algebra 𝓤 𝑆)(θ : Con{𝓤}{𝓦} 𝑨){fe : funext 𝓥 (𝓤 ⊔ lsuc 𝓦)} → Con (𝑨 ╱ θ)
𝟎[ 𝑨 ╱ θ ] {fe} = 𝟘[ 𝑨 ╱ θ ] , Δ (𝑨 ╱ θ) {fe}

\end{code}


Finally, the following elimination rule is sometimes


open IsCongruence

/-≡ : {𝑨 : Algebra 𝓤 𝑆}(θ : Con{𝓤}{𝓦} 𝑨){u v : ∣ 𝑨 ∣} → ⟪ u ⟫ {∣ θ ∣} ≡ ⟪ v ⟫ → ∣ θ ∣ u v
/-≡ θ refl = IsEquivalence.refl (is-equivalence ∥ θ ∥)

\end{code}

--------------------------------------

<sup>1</sup><span class="footnote" id="fn1"> **Unicode Hints**. Produce the `╱` symbol in [agda2-mode][] by typing `\---` and then `C-f` a number of times.</span>


<br>
<br>

[← Algebras.Products](Algebras.Products.html)
<span style="float:right;">[Homomorphisms →](Homomorphisms.html)</span>

{% include UALib.Links.md %}
























<!-- NO LONGER NEEDED ----------------------------------------------------------

-- Imports from the Agda (Builtin) and the Agda Standard Library
-- open import Agda.Builtin.Equality using (_≡_; refl)
-- open import Axiom.Extensionality.Propositional renaming (Extensionality to funext)
-- open import Level renaming (suc to lsuc; zero to lzero)
-- open import Data.Product using (_,_; Σ; _×_)
-- open import Relation.Binary using (Rel; IsEquivalence)
-- open import Relation.Unary using (Pred; _∈_)
-- open import Relation.Binary.PropositionalEquality.Core using (sym; trans; cong)

-- -- Imports from the Agda Universal Algebra Library
-- open import Algebras.Basic
-- open import Overture.Preliminaries using (Type; 𝓘; 𝓞; 𝓤; 𝓥; 𝓦; Π; -Π; -Σ; ∣_∣; ∥_∥; fst)
-- open import Relations.Discrete using (𝟎; _|:_)
-- open import Relations.Quotients using (_/_; ⟪_⟫)

--------------------------------------------------------------------------------- -->
