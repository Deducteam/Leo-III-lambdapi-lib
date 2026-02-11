/* 
---------------------------------------------------------------------------
Library on Meta-Theorems for Disjunctions and Conjunctions
---------------------------------------------------------------------------

This file contains additions to the standard library file Disj.lp.
In particular, it encodes a theorem for removing ⊥ from clauses and an
n-ary version of the transformation theorem.
---------------------------------------------------------------------------
*/

require open Stdlib.Disj;

/******************************************************************************
*  Deletion of ⊥ 
******************************************************************************/

// Prelim 

symbol insertBot : 𝕃 o → ℕ → 𝕃 o;
rule insertBot □ 0 ↪ (⊥ ⸬ □)
with insertBot □ (_ +1) ↪ □
with insertBot ($l0 ⸬ $l) 0 ↪ (⊥ ⸬ ($l0 ⸬ $l))
with insertBot ($l0 ⸬ $l) ($n +1) ↪ $l0 ⸬ (insertBot $l $n);

symbol insertBots : 𝕃 o → 𝕃 nat → 𝕃 o;
rule insertBots $l □ ↪ $l
with insertBots $l ($n ⸬ $nl) ↪ insertBots (insertBot $l $n) $nl;

// Theorems

opaque symbol deleteBot (n : ℕ) (c: 𝕃 o) :
π (disj (insertBot c n) = disj c)≔
begin
    induction
        {induction
            {reflexivity}
            {assume x xlist h0; 
            simplify; 
            rewrite disj_correct; 
            rewrite ⊥∨; 
            reflexivity}} 
        {assume n h0; 
        induction
            {reflexivity}
            {assume x c;
            simplify;
            assume h1;
            rewrite disj_correct;
            rewrite disj_correct;
            rewrite (h0 c);
            reflexivity}}
end;

opaque symbol deleteBots (n : 𝕃 nat) (c: 𝕃 o):
π (disj (insertBots c n) = disj c)≔
begin
    induction
        {induction
            {reflexivity}
            {assume x xlist h0; 
            reflexivity}}
        {induction
            {assume n h0 c; 
            simplify; 
            rewrite left deleteBot 0 c; 
            rewrite left h0 (insertBot c 0); 
            reflexivity}
            {assume n h0 nlist h1 c; 
            rewrite left (deleteBot (n +1) c); 
            rewrite left h1 (insertBot c (n +1)); 
            reflexivity;}}
end;

// Application Example

assert a b c ⊢ deleteBots (0 ⸬ 3 ⸬ □) (a ⸬ b ⸬ c ⸬ □) : 
    π ((⊥ ∨ a ∨ b ∨ ⊥ ∨ c) = (a ∨ b ∨ c));

/******************************************************************************
*  N-ary Transform Theorem
******************************************************************************/

// Theorem

opaque symbol transform_n [l : τ o] (c0 c1 c2: 𝕃 o): 
π (l ⇒ disj c1) → π (disj (c0 ++ (l ⸬ c2))) → π (disj (c0 ++ c1 ++ c2)) ≔
begin
    assume l c0 c1 c2 h2 h3;
    rewrite disj_++_correct;
    have H0: π ((disj c0) ∨ disj (l ⸬ c2))
        {rewrite left disj_++_correct; refine h3};
    refine ∨ₑ H0 _ _
        {assume h4; refine ∨ᵢ₁ h4}
        {assume h4;
         have H1: π (l ∨ disj c2)
            {rewrite left disj_correct; refine h4};
        rewrite disj_++_correct;
        refine ∨ₑ H1 _ _
            {assume h5;
            refine ∨ᵢ₂ (∨ᵢ₁ (h2 h5))}
            {assume h5;
            refine ∨ᵢ₂ (∨ᵢ₂ h5)}}
end;

// Application Example

assert l0 l1 l2 l3 l1' l1'' ⊢ transform_n [l1] (l0 ⸬ □) (l1' ⸬ l1'' ⸬ □) (l2 ⸬ l3 ⸬ □): 
    (π (l1 ⇒ (l1' ∨ l1''))) →  π (l0 ∨ l1 ∨ l2 ∨ l3) → π (l0 ∨ l1' ∨ l1'' ∨ l2 ∨ l3);