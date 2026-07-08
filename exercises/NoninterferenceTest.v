Set Warnings "-notation-overridden,-parsing".
From Stdlib Require Export String.
From LF Require Import Noninterference.

Parameter MISSING: Type.

Module Check.

Ltac check_type A B :=
    match type of A with
    | context[MISSING] => idtac "Missing:" A
    | ?T => first [unify T B; idtac "Type: ok" | idtac "Type: wrong - should be (" B ")"]
    end.

Tactic Notation "print_manual_grade" constr(A) :=
    match eval compute in A with
    | Some (_ ?S ?C) =>
        idtac "Score:"  S;
        match eval compute in C with
          | ""%string => idtac "Comment: None"
          | _ => idtac "Comment:" C
        end
    | None =>
        idtac "Score: Ungraded";
        idtac "Comment: None"
    end.

End Check.

From LF Require Import Noninterference.
Import Check.

Goal True.

idtac "-------------------  noninterferent_tincX  --------------------".
idtac " ".

idtac "#> noninterferent_tincX".
idtac "Possible points: 2".
check_type @noninterferent_tincX ((noninterferent_state LXP tincX)).
idtac "Assumptions:".
Abort.
Print Assumptions noninterferent_tincX.
Goal True.
idtac " ".

idtac "-------------------  noninterferent_tincY  --------------------".
idtac " ".

idtac "#> noninterferent_tincY".
idtac "Possible points: 2".
check_type @noninterferent_tincY ((noninterferent_state LXP tincY)).
idtac "Assumptions:".
Abort.
Print Assumptions noninterferent_tincY.
Goal True.
idtac " ".

idtac "-------------------  noninterferent_tincY  --------------------".
idtac " ".

idtac "#> noninterferent_tincY".
idtac "Possible points: 3".
check_type @noninterferent_tincY ((noninterferent_state LXP tincY)).
idtac "Assumptions:".
Abort.
Print Assumptions noninterferent_tincY.
Goal True.
idtac " ".

idtac "-------------------  sme_state_tXplusYtoX  --------------------".
idtac " ".

idtac "#> sme_state_tXplusYtoX".
idtac "Possible points: 3".
check_type @sme_state_tXplusYtoX (
(@eq (forall _ : Imp.state, Imp.state) (sme_state tXplusYtoX LXP) tid)).
idtac "Assumptions:".
Abort.
Print Assumptions sme_state_tXplusYtoX.
Goal True.
idtac " ".

idtac "-------------------  noninterferent_secure_ex1  --------------------".
idtac " ".

idtac "#> noninterferent_secure_ex1".
idtac "Possible points: 2".
check_type @noninterferent_secure_ex1 ((noninterferent_no_while LXP secure_ex1)).
idtac "Assumptions:".
Abort.
Print Assumptions noninterferent_secure_ex1.
Goal True.
idtac " ".

idtac "-------------------  interferent_insecure_com_explicit  --------------------".
idtac " ".

idtac "#> interferent_insecure_com_explicit".
idtac "Possible points: 2".
check_type @interferent_insecure_com_explicit (
(not (noninterferent_no_while LXP insecure_com_explicit))).
idtac "Assumptions:".
Abort.
Print Assumptions interferent_insecure_com_explicit.
Goal True.
idtac " ".

idtac "-------------------  interferent_insecure_com_implicit  --------------------".
idtac " ".

idtac "#> interferent_insecure_com_implicit".
idtac "Possible points: 3".
check_type @interferent_insecure_com_implicit (
(not (noninterferent_no_while LXP insecure_com_implicit))).
idtac "Assumptions:".
Abort.
Print Assumptions interferent_insecure_com_implicit.
Goal True.
idtac " ".

idtac "-------------------  noninterferent_incX  --------------------".
idtac " ".

idtac "#> noninterferent_incX".
idtac "Possible points: 2".
check_type @noninterferent_incX (
(noninterferent_com LXP
   (Imp.CAsgn Imp.X (Imp.APlus (Imp.AId Imp.X) (Imp.ANum 1))))).
idtac "Assumptions:".
Abort.
Print Assumptions noninterferent_incX.
Goal True.
idtac " ".

idtac "-------------------  interferent_YtoX_com  --------------------".
idtac " ".

idtac "#> interferent_YtoX_com".
idtac "Possible points: 2".
check_type @interferent_YtoX_com (
(not (noninterferent_com LXP (Imp.CAsgn Imp.X (Imp.AId Imp.Y))))).
idtac "Assumptions:".
Abort.
Print Assumptions interferent_YtoX_com.
Goal True.
idtac " ".

idtac "-------------------  sme_com_YtoX  --------------------".
idtac " ".

idtac "#> sme_com_YtoX".
idtac "Possible points: 2".
check_type @sme_com_YtoX (
(sme_com LXP (Imp.CAsgn Imp.X (Imp.AId Imp.Y))
   (@Maps.t_update nat Imp.empty_st Imp.Y 5)
   (@Maps.t_update nat (@Maps.t_update nat Imp.empty_st Imp.Y 5) Imp.X 0))).
idtac "Assumptions:".
Abort.
Print Assumptions sme_com_YtoX.
Goal True.
idtac " ".

idtac "-------------------  tsni_incX  --------------------".
idtac " ".

idtac "#> tsni_incX".
idtac "Possible points: 2".
check_type @tsni_incX (
(tsni_com_R Imp.ceval LXP
   (Imp.CAsgn Imp.X (Imp.APlus (Imp.AId Imp.X) (Imp.ANum 1))))).
idtac "Assumptions:".
Abort.
Print Assumptions tsni_incX.
Goal True.
idtac " ".

idtac " ".

idtac "Max points - standard: 25".
idtac "Max points - advanced: 25".
idtac "".
idtac "Allowed Axioms:".
idtac "functional_extensionality".
idtac "FunctionalExtensionality.functional_extensionality_dep".
idtac "".
idtac "".
idtac "********** Summary **********".
idtac "".
idtac "Below is a summary of the automatically graded exercises that are incomplete.".
idtac "".
idtac "The output for each exercise can be any of the following:".
idtac "  - 'Closed under the global context', if it is complete".
idtac "  - 'MANUAL', if it is manually graded".
idtac "  - A list of pending axioms, containing unproven assumptions. In this case".
idtac "    the exercise is considered complete, if the axioms are all allowed.".
idtac "".
idtac "********** Standard **********".
idtac "---------- noninterferent_tincX ---------".
Print Assumptions noninterferent_tincX.
idtac "---------- noninterferent_tincY ---------".
Print Assumptions noninterferent_tincY.
idtac "---------- noninterferent_tincY ---------".
Print Assumptions noninterferent_tincY.
idtac "---------- sme_state_tXplusYtoX ---------".
Print Assumptions sme_state_tXplusYtoX.
idtac "---------- noninterferent_secure_ex1 ---------".
Print Assumptions noninterferent_secure_ex1.
idtac "---------- interferent_insecure_com_explicit ---------".
Print Assumptions interferent_insecure_com_explicit.
idtac "---------- interferent_insecure_com_implicit ---------".
Print Assumptions interferent_insecure_com_implicit.
idtac "---------- noninterferent_incX ---------".
Print Assumptions noninterferent_incX.
idtac "---------- interferent_YtoX_com ---------".
Print Assumptions interferent_YtoX_com.
idtac "---------- sme_com_YtoX ---------".
Print Assumptions sme_com_YtoX.
idtac "---------- tsni_incX ---------".
Print Assumptions tsni_incX.
idtac "".
idtac "********** Advanced **********".
Abort.

(* 2026-07-08 20:19 *)
