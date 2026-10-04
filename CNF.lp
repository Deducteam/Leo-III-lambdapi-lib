/* 
---------------------------------------------------------------------------
Library on proving the normalisazion to CNF by reflection
---------------------------------------------------------------------------

Overview
--------
This file contains a (partial) encoding of the Leo-III clausification
procedure. The encoding relies on proof by reflection:

  1. Formulas from the standard library are reified into a 
     dedicated representation.
  2. Normalization rules are executed computationally using rewrite rules.
  3. The normalized formulas are interpreted back into Prop.
  4. Correctness theorems connect computation with logical equivalence.


Clausification Phases
---------------------

The clausification pipeline is decomposed into independent transformations:

** 1. Negation Normal Form (NNF)
     - Push negations inward (De Morgan, double negation elimination)
     - Eliminate implications
     - Transform quantifiers under negation

** 2. Quantifier Generalization (Work in Progress)
     - Lift universal quantifiers to outer scope

** 3. Distributivity
     - Rewrite disjunctions over conjunctions
     - Construct conjunctions of disjunctions

** 4. Associativity / Structural Normalization (Work in Progress)
     - Canonical restructuring of boolean connectives

Each phase is verified independently via reflection lemmas.


Contents
--------

  • NNF syntax, reification, denotation, normalization
  • Proof of semantic correctness for NNF
  • Distributivity encoding using list-based constructions
  • Proof of semantic correctness for distributivity
  • Small application examples


Notes
-----

This encoding is currently experimental and not yet integrated into the
full proof translation pipeline. Future work will extend the missing
clausification phases and connect them to the Leo-III backend.

---------------------------------------------------------------------------
*/

require open Stdlib.Conj Leo-III-lambdapi-lib.CNFeq;


symbol a : Prop;
symbol b : Prop;
symbol c : Prop;
symbol d : Prop;
symbol e : Prop;
symbol p: τ ι → Prop;


/******************************************************************************
*  Negation Normal Form       
******************************************************************************/

// Setup

inductive nnf_prop: TYPE ≔
| nnf_Other: Prop → nnf_prop
| nnf_Neg: nnf_prop → nnf_prop
| nnf_And: nnf_prop → nnf_prop → nnf_prop
| nnf_OR: nnf_prop → nnf_prop → nnf_prop
| nnf_Impl: nnf_prop → nnf_prop → nnf_prop
| nnf_Forall [a : Set] : (τ a → nnf_prop) → nnf_prop
| nnf_Exists [a : Set] : (τ a → nnf_prop) → nnf_prop;

symbol nnf_propS: Set;
rule τ nnf_propS ↪ nnf_prop;

sequential symbol nnf_reify: Prop → nnf_prop;
rule nnf_reify ($x ∧ $y) ↪ (nnf_And (nnf_reify $x) (nnf_reify $y))
with nnf_reify ($x ∨ $y) ↪ (nnf_OR (nnf_reify $x) (nnf_reify $y))
with nnf_reify ($x ⇒ ⊥) ↪  (nnf_Neg (nnf_reify $x)) 
with nnf_reify ($x ⇒ $y) ↪ (nnf_Impl (nnf_reify $x) (nnf_reify $y))
with nnf_reify (∀ $p) ↪ (nnf_Forall (λ x, (nnf_reify ($p x)))) 
with nnf_reify (∃ $p) ↪ (nnf_Exists (λ x, (nnf_reify ($p x)))) 
with nnf_reify $x ↪ (nnf_Other $x);

symbol nnf_denote (p: nnf_prop): Prop;
rule nnf_denote (nnf_And $x $y) ↪  (nnf_denote $x) ∧ (nnf_denote $y)
with nnf_denote (nnf_Neg $x) ↪  ¬ (nnf_denote $x)
with nnf_denote (nnf_OR $x $y) ↪  (nnf_denote $x) ∨ (nnf_denote $y)
with nnf_denote (nnf_Impl $x $y) ↪  (nnf_denote $x) ⇒ (nnf_denote $y)
with nnf_denote (nnf_Forall $p) ↪  ∀(λ x, nnf_denote ($p x))
with nnf_denote (nnf_Exists $p) ↪  ∃(λ x, nnf_denote ($p x))
with nnf_denote (nnf_Other $i) ↪ $i;

symbol nnf: nnf_prop → nnf_prop;
rule nnf (nnf_Neg (nnf_Neg $x)) ↪ nnf $x //Dne
with nnf (nnf_Neg (nnf_Impl $x $y)) ↪ nnf_And (nnf $x) (nnf (nnf_Neg $y)) // Imp_neg
with nnf (nnf_Neg (nnf_And $x $y)) ↪ nnf_OR (nnf (nnf_Neg $x)) (nnf (nnf_Neg $y)) // Demorgan_∧ 
with nnf (nnf_Neg (nnf_OR $x $y)) ↪ nnf_And (nnf (nnf_Neg $x)) (nnf (nnf_Neg $y)) // Demorgan_∨
with nnf (nnf_Neg (nnf_Forall (λ x, $F.[x]))) ↪ (nnf_Exists ((λ x, nnf (nnf_Neg $F.[x])))) // Neg_All
with nnf (nnf_Neg (nnf_Forall (λ x, $F.[]))) ↪ nnf (nnf_Neg $F.[]) // Eliminate quantifier
with nnf (nnf_Neg (nnf_Exists (λ x, $F.[x]))) ↪ (nnf_Forall (λ x,nnf (nnf_Neg $F.[x]))) // Neg_Ex
with nnf (nnf_Neg (nnf_Exists (λ x, $F.[]))) ↪ nnf (nnf_Neg $F.[]) // Eliminate quantifier
with nnf (nnf_Neg (nnf_Other $x)) ↪ (nnf_Neg (nnf_Other $x))
with nnf (nnf_Impl $x $y) ↪ nnf_OR (nnf (nnf_Neg $x)) (nnf $y) // Imp
with nnf (nnf_OR $x $y) ↪ nnf_OR (nnf $x) (nnf $y)
with nnf (nnf_And $x $y) ↪ nnf_And (nnf $x) (nnf $y)
with nnf (nnf_Forall (λ x, $F.[x])) ↪ (nnf_Forall (λ x, nnf $F.[x]))
with nnf (nnf_Forall (λ x, $F.[])) ↪ (nnf $F.[])
with nnf (nnf_Exists (λ x, $F.[x])) ↪ (nnf_Exists (λ x, nnf $F.[x]))
with nnf (nnf_Exists (λ x, $F.[])) ↪ (nnf $F.[])
with nnf (nnf_Other $x) ↪ nnf_Other $x;


// Lemma

symbol nnf_denote_correct_Neg x : 
    π ((¬ (nnf_denote (nnf x))) = (nnf_denote (nnf (nnf_Neg x))))≔
begin
    have ¬_exp: Π x , π ((x ⇒ ⊥) = ¬ x) {reflexivity};
    induction
        {reflexivity}
        {assume x0 h0; rewrite left h0; repeat rewrite ¬_exp;
        rewrite ¬¬ₑ_eq (nnf_denote (nnf x0)); 
        reflexivity}
        {simplify; assume x0 h0 x1 h1;
        rewrite left h0; rewrite left h1;
        repeat rewrite  ¬_exp; rewrite deMorgan_∧; 
        reflexivity}
        {simplify; assume x0 h0 x1 h1;
        rewrite left h0; rewrite left h1;
        repeat rewrite  ¬_exp; rewrite deMorgan_∨; 
        reflexivity}
        {simplify; assume x0 h0 x1 h1;
        rewrite left h0; rewrite left h1;
        repeat rewrite  ¬_exp; rewrite deMorgan_∨; rewrite ¬¬ₑ_eq; reflexivity}  
        {assume a h0 h1; rewrite eta_exp h0; simplify; 
        rewrite  ¬_exp; rewrite ¬∀=∃¬; simplify rule off;
        refine propExt (`∃ x, ¬ (nnf_denote (nnf (h0 x)))) (`∃ x, nnf_denote (nnf (nnf_Neg (h0 x)))) _ _
            {assume h2; refine ∃ₑ h2 _; assume y h3;
            have H0 : π (nnf_denote (nnf (nnf_Neg (h0 y))))
                {rewrite left h1 y; refine h3};
            refine ∃ᵢ y H0}
            {assume h2; refine ∃ₑ h2 _; assume y h3;
            have H0 : π ( ¬ (nnf_denote (nnf (h0 y)))) 
                {rewrite h1 y; refine h3};
            refine ∃ᵢ y H0}}
        {assume a f h0; rewrite eta_exp f; simplify; rewrite  ¬_exp; rewrite ¬∃=∀¬; simplify rule off;
        refine propExt (`∀ x, ¬ (nnf_denote (nnf (f x)))) (`∀ x, nnf_denote (nnf (nnf_Neg (f x)))) _ _
            {assume h1 y; rewrite left h0 y; refine h1 y}
            {assume h1 y; rewrite h0 y; refine h1 y}}      
end;


// Correctness Theorem 

symbol nnf_correct x : π (nnf_denote x = nnf_denote (nnf x))≔
begin
    induction
        {simplify; reflexivity}
        {assume x h0; rewrite left nnf_denote_correct_Neg; rewrite left h0; simplify; 
        reflexivity}
        {assume x h0 y h1; simplify; rewrite left h0; rewrite left h1; 
        reflexivity}
        {assume x h0 y h1; simplify; rewrite left h0; rewrite left h1; 
        reflexivity}
        {assume x h0 y h1; simplify; rewrite left nnf_denote_correct_Neg; rewrite left h0; 
        rewrite left h1; rewrite ⇒=∨; reflexivity}
        {assume a f h0; simplify; rewrite eta_exp f; simplify; 
        refine propExt (`∀ x, nnf_denote ((λ y, f y) x)) (nnf_denote (nnf (nnf_Forall (λ y, f y)))) _ _ 
            {assume h1 z; rewrite left (h0 z) ; refine h1 z}
            {assume h1 z; rewrite (h0 z) ; refine h1 z}}
        {assume a f h0; rewrite eta_exp f; simplify;
        refine propExt (`∃ x, nnf_denote (f x)) (`∃ x, nnf_denote (nnf (f x))) _ _ 
            {assume h1; refine ∃ₑ h1 _; assume y h2;
            have H0 : π (nnf_denote (nnf (f y)))
                {rewrite left h0 y; refine h2};
            refine ∃ᵢ y H0}
            {assume h1; refine ∃ₑ h1 _; assume y h2;
            have H0 : π (nnf_denote (f y))
                {rewrite h0 y; refine h2};
            refine ∃ᵢ y H0}}
end;


// Application Example:

symbol nnf_example_0 : π ((¬ (a ∨ b ∧ (a ⇒ a))) = ((¬ a) ∧ ((¬ b) ∨ (a ∧ (¬ a))))) ≔
begin

    have H0: π ((¬ (a ∨ b ∧ (a ⇒ a))) = (nnf_denote (nnf_reify (¬ (a ∨ b ∧ (a ⇒ a))))))
        {reflexivity};
    rewrite H0;
    rewrite .[x in x = _] nnf_correct;
    reflexivity; 
end;

symbol nnf_example_1 : π ((∀(λ x , ¬ (p x ∨ a ∧ (∃(λ y, ¬ (y ⇒ a)))))) = (`∀ x, (¬ p x) ∧ ((¬ a) ∨ (`∀ x0, (¬ x0) ∨ a)))) ≔
begin

    have H0: π ((∀(λ x , ¬ (p x ∨ a ∧ (∃(λ y, ¬ (y ⇒ a)))))) = (nnf_denote (nnf_reify (∀(λ x , ¬ (p x ∨ a ∧ (∃(λ y, ¬ (y ⇒ a)))))))))
        {reflexivity};
    rewrite H0;
    rewrite .[x in x = _] nnf_correct;
    reflexivity; 
end;


/******************************************************************************
*  Distributivit     
******************************************************************************/

// Setup

inductive dist_prop : TYPE ≔
| dist_Other: Prop → dist_prop
| dist_And: dist_prop → dist_prop → dist_prop
| dist_Or: dist_prop → dist_prop → dist_prop;

symbol dist_prop_S: Set;
rule τ dist_prop_S ↪ dist_prop;

sequential symbol dist_reify: Prop → dist_prop;
rule dist_reify ($x ∧ $y) ↪ (dist_And (dist_reify $x) (dist_reify $y))
with dist_reify ($x ∨ $y) ↪ (dist_Or (dist_reify $x) (dist_reify $y))
with dist_reify $x ↪ (dist_Other $x);

symbol dist_denote: dist_prop → Prop;
rule dist_denote (dist_And $x $y) ↪ (dist_denote $x) ∧ (dist_denote $y)
with dist_denote (dist_Or $x $y) ↪ (dist_denote $x) ∨ (dist_denote $y)
with dist_denote (dist_Other $x) ↪ $x;

symbol prepend_each [a] : 𝕃 a → 𝕃 (list a) → 𝕃 (list a);
rule prepend_each _ □ ↪ □
with prepend_each $x ($l0 ⸬ $l) ↪ ($x ++ $l0) ⸬ (prepend_each $x $l);
symbol cartesian_prepend [a] : 𝕃 (list a) → 𝕃 (list a) → 𝕃 (list a);
rule cartesian_prepend ($l0 ⸬ $l) $n ↪ (prepend_each $l0 $n) ++ (cartesian_prepend $l $n)
with cartesian_prepend □ _ ↪ □;

symbol dist_disj : 𝕃 dist_prop_S → dist_prop;
rule dist_disj ($l0 ⸬ ($l1 ⸬ $l)) ↪ dist_Or $l0 (dist_disj ($l1 ⸬ $l))
with dist_disj ($l0 ⸬ □) ↪ $l0
with dist_disj □ ↪ dist_Other ⊥;

symbol dist_conj : 𝕃 (list dist_prop_S) → dist_prop;
rule dist_conj ($l0 ⸬ ($l1 ⸬ $l)) ↪ dist_And (dist_disj $l0) (dist_conj ($l1 ⸬ $l))
with dist_conj ($l0 ⸬ □) ↪ (dist_disj $l0)
with dist_conj □ ↪ dist_Other ⊤;

symbol dist : dist_prop → 𝕃 (list dist_prop_S);
rule dist (dist_And $x $y) ↪ (dist $x) ++ (dist $y)
with dist (dist_Other $x) ↪ (((dist_Other $x) ⸬ □) ⸬ □)
with dist (dist_Or $x $y) ↪ cartesian_prepend (dist $x) (dist $y);

// Lemmas

symbol dist_denote_correct_∧ x y : 
    π (((dist_denote x) ∧ (dist_denote y)) = (dist_denote (dist_And x y)))≔
begin
    simplify; reflexivity;
end;

symbol dist_denote_correct_∨ x y : 
    π (((dist_denote x) ∨ (dist_denote y)) = (dist_denote (dist_Or x y)))≔
begin
    simplify; reflexivity;
end;

symbol dist_denote_correct_++ x y : 
    π ((dist_denote (dist_And (dist_conj x) (dist_conj y))) = (dist_denote (dist_conj (x ++ y))))≔
begin
    induction
        {simplify; assume x; rewrite ⊤∧; reflexivity}
        {assume x; induction
                {assume h0; induction
                    {simplify; rewrite ∧⊤; reflexivity}
                    {assume y l h1; simplify; reflexivity}}
                {simplify; assume y l h0 h1 n; rewrite left h1 n; rewrite ∧_assoc; 
                reflexivity}}
end;

symbol dist_denote_correct_⸬ x y : 
    π (dist_denote (dist_conj (x ⸬ y)) = dist_denote (dist_And (dist_disj x) (dist_conj y)))≔
begin
    induction
        {induction
            {simplify; rewrite ⊥∧; reflexivity}
            {assume x0 x1 h0; reflexivity}}
        {assume x l h0; induction
                {simplify; rewrite ∧⊤; reflexivity}
                {simplify; assume y n h1 ; reflexivity}}
end;

symbol prepend_each_add n0 n l: 
    π ((dist_denote (dist_conj (cartesian_prepend (n0 ⸬ n) l))) = (dist_denote (dist_conj (cartesian_prepend n l)) ∧ dist_denote (dist_conj (cartesian_prepend (n0 ⸬ n) l))))≔
begin
    assume n0 n l;
    refine propExt (dist_denote (dist_conj (cartesian_prepend (n0 ⸬ n) l))) (dist_denote (dist_conj (cartesian_prepend n l)) ∧ dist_denote (dist_conj (cartesian_prepend (n0 ⸬ n) l)))_ _ 
        {assume h0; refine ∧ᵢ _ h0; 
        have H0 : π ((dist_denote (dist_conj (cartesian_prepend (n0 ⸬ n) l))) ⇒ (dist_denote (dist_conj (cartesian_prepend n l))))
            {simplify cartesian_prepend; rewrite left dist_denote_correct_++; simplify; assume h1; refine ∧ₑ₂ h1};
        refine H0 h0}
        {assume h0; refine ∧ₑ₂ h0}
end;    

symbol dist_disj_corr_⸬ x y : 
    π ((dist_denote (dist_disj (x ⸬ y))) = (dist_denote x ∨ dist_denote (dist_disj y)))≔
begin
    assume x;
    induction
        {simplify; rewrite ∨⊥; reflexivity}
        {assume y0 y h0;
        simplify; reflexivity}
end;

symbol dist_disj_corr_++  x y : 
    π ((dist_denote (dist_disj (x ++ y))) = (dist_denote (dist_disj x) ∨ dist_denote (dist_disj y)))≔
begin
    induction
        {simplify; assume x; rewrite ⊥∨; reflexivity}
        {assume x0 x h0 y;
        simplify; rewrite dist_disj_corr_⸬; rewrite dist_disj_corr_⸬; rewrite h0;
        rewrite ∨_assoc;reflexivity}
end;

symbol cartesian_prepend_⸬_++ [a] (l0 : 𝕃 a) l n : 
    π ((cartesian_prepend (l0 ⸬ l) n) = (prepend_each l0 n) ++ (cartesian_prepend l n))≔
begin
    assume l0 l n; simplify;
    reflexivity
end;

symbol cartesian_prepend_empty [a] (x : 𝕃 (list a)) : 
    π ((cartesian_prepend x □) = □)≔
begin
    assume a;
    induction
        {simplify; reflexivity}
        {simplify; assume x y h; refine h}
end;

symbol cartesian_prepend_sym n l :
     π ((dist_denote (dist_conj (cartesian_prepend l n))) = dist_denote (dist_conj (cartesian_prepend n l))) ≔
begin
    induction
        {simplify; assume l; rewrite cartesian_prepend_empty; simplify; reflexivity}
        {assume l0 l h0; induction
            {rewrite cartesian_prepend_empty; simplify; 
            reflexivity}
            {assume n0 n h1; 
            rewrite cartesian_prepend_⸬_++; rewrite left dist_denote_correct_++; simplify dist_denote; rewrite h1; rewrite cartesian_prepend_⸬_++; 
            simplify prepend_each; rewrite dist_denote_correct_⸬; simplify dist_denote; rewrite left dist_denote_correct_++; simplify dist_denote;
            rewrite cartesian_prepend_⸬_++; rewrite left dist_denote_correct_++; simplify dist_denote; rewrite left h0 (n0 ⸬ n); rewrite cartesian_prepend_⸬_++; 
            simplify prepend_each; rewrite dist_denote_correct_⸬; simplify dist_denote; rewrite left dist_denote_correct_++; simplify dist_denote;
            rewrite h0 n; rewrite dist_disj_corr_++; rewrite dist_disj_corr_++; rewrite ∨_sym;
            have ∧_sym_3 : Π x, Π y, Π z, π ((x ∧ y ∧ z) = (y ∧ x ∧ z))
                {assume x y z; rewrite ∧_sym; rewrite ∧_assoc; rewrite .[x in (_ ∧ x) = _] ∧_sym; 
                reflexivity};
            rewrite ∧_assoc; rewrite ∧_assoc; rewrite .[x in (_ ∧ x) = _] ∧_sym_3; 
            reflexivity}} 
end;

symbol ∧_idem_l a b :
    π ((a ∧ (a ∧ b)) = (a ∧ b)) ≔
begin
    assume a b;
    refine propExt (a ∧ (a ∧ b)) (a ∧ b) _ _
        {assume h0; refine ∧ₑ₂ h0}
        {assume h0; refine ∧ᵢ (∧ₑ₁ h0) h0}
end;

symbol cartesian_prepend_double l0 n0 l n : 
    π (dist_denote ( dist_conj (cartesian_prepend (l0 ⸬ l) (n0 ⸬ n))) = dist_denote (dist_conj ((l0 ++ n0) ⸬ (cartesian_prepend (l0 ⸬ l) (n)) ++ (cartesian_prepend (l) (n0 ⸬ n)))))≔
begin
    assume l0 n0; assume l n; simplify; rewrite dist_denote_correct_⸬; rewrite dist_denote_correct_⸬; simplify dist_denote; simplify dist_denote;
    rewrite left dist_denote_correct_++; rewrite left dist_denote_correct_++; simplify dist_denote; simplify dist_denote; rewrite cartesian_prepend_sym; 
    rewrite left dist_denote_correct_++; simplify dist_denote; rewrite prepend_each_add; rewrite ∧_assoc;
    rewrite right cartesian_prepend_sym; rewrite right cartesian_prepend_sym; rewrite ∧_idem_l;
    reflexivity
end;

symbol ∧_asso a b : 
    π ((a ∧ (b ∧ a)) = (b ∧ a)) ≔
begin
    assume a b;
    refine propExt (a ∧ (b ∧ a)) (b ∧ a) _ _
        {assume h0; refine ∧ₑ₂ h0}
        {assume h0; refine ∧ᵢ (∧ₑ₂ h0) h0}
end;

symbol cartesian_prepend_correct x y : 
    π (dist_denote (dist_Or (dist_conj x) (dist_conj y)) = dist_denote (dist_conj (cartesian_prepend x y)))≔
begin
    induction
        {simplify; assume x; rewrite ⊤∨; reflexivity}
        {assume x; assume l h0;
            induction
                {simplify; rewrite ∨⊤; rewrite left (h0 □); simplify; rewrite ∨⊤; 
                reflexivity}
                {assume y z h1; simplify dist_denote; rewrite dist_denote_correct_⸬; rewrite dist_denote_correct_⸬; simplify dist_denote; 
                rewrite cartesian_prepend_double; rewrite dist_denote_correct_⸬; simplify dist_denote; rewrite left dist_denote_correct_++; 
                simplify dist_denote; rewrite left h1; rewrite left h0 (y ⸬ z); simplify dist_denote; rewrite dist_denote_correct_⸬; 
                rewrite dist_denote_correct_⸬; rewrite dist_disj_corr_++; simplify; rewrite ∧∨_dist_l; rewrite ∧∨_dist_l; 
                rewrite ∧∨_dist_r; rewrite ∧∨_dist_r; rewrite ∧_assoc; rewrite ∧_assoc; rewrite ∧_asso; 
                reflexivity}}
end;


// Correctness Theorem 

symbol dist_correct l : 
    π (dist_denote l = dist_denote (dist_conj (dist l)))≔
begin
    induction
        {simplify; reflexivity}
        {simplify; assume x0 h0 x1 h1; rewrite h0; rewrite h1; 
        rewrite dist_denote_correct_∧; rewrite dist_denote_correct_++;
        reflexivity}
        {simplify; assume x0 h0 x1 h1; rewrite h0; rewrite h1;
        rewrite dist_denote_correct_∨; rewrite cartesian_prepend_correct;
        reflexivity}
end;


// Application Example

symbol dist_example_0 : π ((a ∨ b ∨ c ∨ (d ∧ e)) = ((a ∨ (b ∨ (c ∨ d))) ∧ (a ∨ (b ∨ (c ∨ e))))) ≔
begin

    have H0: π ((a ∨ b ∨ c ∨ (d ∧ e)) = (dist_denote (dist_reify (a ∨ b ∨ c ∨ (d ∧ e)))))
        {reflexivity};
    rewrite H0;
    rewrite .[x in x = _] dist_correct;
    reflexivity; 
end;
