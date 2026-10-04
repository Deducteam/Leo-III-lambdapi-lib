/*
---------------------------------------------------------------------------
Library on TPTP arithmetic symbols used by Leo-III
---------------------------------------------------------------------------

Library introducing Lambdapi names for the TPTP arithmetic
constants used in Leo-III. The simplification rules encoded below mirror the 
cases from Leo-III's Simplification.apply0 matching. 
---------------------------------------------------------------------------
*/

require open Stdlib.HOL Stdlib.Impred Stdlib.PropExt;


/******************************************************************************
*  TPTP arithmetic types
******************************************************************************/

symbol tptp_int : Set;
symbol tptp_rat : Set;
symbol tptp_real : Set;


/******************************************************************************
*  Active Leo-III TPTP arithmetic constants
******************************************************************************/

symbol tptp_less : Π (TA : Set), τ (TA ⤳ (TA ⤳ o));
symbol tptp_lesseq : Π (TA : Set), τ (TA ⤳ (TA ⤳ o));
symbol tptp_greater : Π (TA : Set), τ (TA ⤳ (TA ⤳ o));
symbol tptp_greatereq : Π (TA : Set), τ (TA ⤳ (TA ⤳ o));

symbol tptp_uminus : Π (TA : Set), τ (TA ⤳ TA);
symbol tptp_sum : Π (TA : Set), τ (TA ⤳ (TA ⤳ TA));
symbol tptp_difference : Π (TA : Set), τ (TA ⤳ (TA ⤳ TA));
symbol tptp_product : Π (TA : Set), τ (TA ⤳ (TA ⤳ TA));
symbol tptp_quotient : Π (TA : Set), τ (TA ⤳ (TA ⤳ TA));


/******************************************************************************
*  Leo-III Simplification.apply0 arithmetic facts
******************************************************************************/

symbol tptp_difference_simp [TA : Set] (x y : τ TA) :
  π (tptp_difference TA x y = tptp_sum TA x (tptp_uminus TA y));

symbol tptp_lesseq_simp [TA : Set] (x y : τ TA) :
  π (tptp_lesseq TA x y = (tptp_less TA x y ∨ x = y));

symbol tptp_greater_simp [TA : Set] (x y : τ TA) :
  π (tptp_greater TA x y = tptp_less TA y x);

symbol tptp_greatereq_simp [TA : Set] (x y : τ TA) :
  π (tptp_greatereq TA x y = (tptp_less TA y x ∨ x = y));
