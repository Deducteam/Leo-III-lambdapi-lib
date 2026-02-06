/* Library on Meta-Theorems for Disjunctions and conjunctions
*/

require open Stdlib.List Stdlib.PropExt Stdlib.Disj;
  

////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////// lemmas ////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////


symbol insertBot : 𝕃 o → ℕ → 𝕃 o;
rule insertBot □ 0 ↪ (⊥ ⸬ □)
with insertBot □ (_ +1) ↪ □
with insertBot ($l0 ⸬ $l) 0 ↪ (⊥ ⸬ ($l0 ⸬ $l))
with insertBot ($l0 ⸬ $l) ($n +1) ↪ $l0 ⸬ (insertBot $l $n);

symbol insertBots : 𝕃 o → 𝕃 nat → 𝕃 o;
rule insertBots $l □ ↪ $l
with insertBots $l ($n ⸬ $nl) ↪ insertBots (insertBot $l $n) $nl;

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

// transformation theorem //////////////////////////////////////////////////////
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






// new battlefield starting here

// first is acc
// symbol undup_acc : Π [a : Set], (τ a → τ a → 𝔹) → 𝕃 a → 𝕃 a → 𝕃 a;

// rule undup_acc _ $acc □ ↪ rev $acc
// with undup_acc $beq $acc ($x ⸬ $l) ↪
//   if (∈ $beq $x $acc) (undup_acc $beq $acc $l) (undup_acc $beq ($x ⸬ $acc) $l);

// opaque symbol mem_acc [a: Set] (beq : τ a → τ a → 𝔹) l acc x: 
//     π (∈ beq x acc) → π (∈ beq x (undup_acc beq acc l))≔
// begin
//     assume a beq;
//     induction
//         {simplify; admit
//         }
//         {assume x0 l0 h0 acc0 x1 h1; 
//         simplify undup_acc; 
//         refine ∨ₑ (case_𝔹 (∈ beq x0 acc0)) _ _ 
//             {assume h2; rewrite h2; simplify if; 
//             refine h0 acc0 x1 h1;
//             }
//             {assume h2; rewrite h2; simplify if; 
//             refine h0 (x0 ⸬ acc0) x1 _;
//             refine mem_tail beq x1 x0 acc0 h1}}
// end;


// opaque symbol fdsfds [a: Set] (beq : τ a → τ a → 𝔹) (beq_rfl : Π x:τ a, π(beq x x)) l x: 
//     π (∈ beq x (undup_acc beq □ (x ⸬ l))) ≔
// begin
//     assume a beq beq_rfl;
//     induction
//         {assume x; simplify; refine beq_rfl x}
//         {assume x0 l0 h0 x1; 
//         simplify undup_acc; simplify;
//         refine ∨ₑ (case_𝔹 (beq x0 x1)) _ _ 
//             {assume h1; rewrite h1; simplify if; 
//             refine mem_acc beq l0 (x1 ⸬ □) x1 _;
//             simplify; refine beq_rfl x1
//             }
//             {assume h1; rewrite h1; simplify if; 
//             refine mem_acc beq l0 (x0 ⸬ (x1 ⸬ □)) x1 _;
//             simplify; refine orᵢ₂ (beq x1 x0) (beq_rfl x1)}}
// end;


