Set Warnings "-notation-overridden,-parsing".
From Stdlib Require Export String.
From LF Require Import Noninterference1.

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

From LF Require Import Noninterference1.
Import Check.

Goal True.

idtac "-------------------  prove_or_disprove_obvious_f1  --------------------".
idtac " ".

idtac "#> prove_or_disprove_obvious_f1".
idtac "Possible points: 1".
check_type @prove_or_disprove_obvious_f1 (
(or (@noninterferent nat nat nat nat obvious_f1)
   (not (@noninterferent nat nat nat nat obvious_f1)))).
idtac "Assumptions:".
Abort.
Print Assumptions prove_or_disprove_obvious_f1.
Goal True.
idtac " ".

idtac "-------------------  prove_or_disprove_obvious_f2  --------------------".
idtac " ".

idtac "#> prove_or_disprove_obvious_f2".
idtac "Possible points: 1".
check_type @prove_or_disprove_obvious_f2 (
(or (@noninterferent nat nat nat nat obvious_f2)
   (not (@noninterferent nat nat nat nat obvious_f2)))).
idtac "Assumptions:".
Abort.
Print Assumptions prove_or_disprove_obvious_f2.
Goal True.
idtac " ".

idtac "-------------------  prove_or_disprove_less_obvious_f4  --------------------".
idtac " ".

idtac "#> prove_or_disprove_less_obvious_f4".
idtac "Possible points: 2".
check_type @prove_or_disprove_less_obvious_f4 (
(or (@noninterferent nat nat nat nat less_obvious_f4)
   (not (@noninterferent nat nat nat nat less_obvious_f4)))).
idtac "Assumptions:".
Abort.
Print Assumptions prove_or_disprove_less_obvious_f4.
Goal True.
idtac " ".

idtac "-------------------  prove_or_disprove_less_obvious_f5  --------------------".
idtac " ".

idtac "#> prove_or_disprove_less_obvious_f5".
idtac "Possible points: 2".
check_type @prove_or_disprove_less_obvious_f5 (
(or (@noninterferent nat nat nat nat less_obvious_f5)
   (not (@noninterferent nat nat nat nat less_obvious_f5)))).
idtac "Assumptions:".
Abort.
Print Assumptions prove_or_disprove_less_obvious_f5.
Goal True.
idtac " ".

idtac "-------------------  prove_or_disprove_less_obvious_f6  --------------------".
idtac " ".

idtac "#> prove_or_disprove_less_obvious_f6".
idtac "Possible points: 2".
check_type @prove_or_disprove_less_obvious_f6 (
(or (@noninterferent nat nat nat nat less_obvious_f6)
   (not (@noninterferent nat nat nat nat less_obvious_f6)))).
idtac "Assumptions:".
Abort.
Print Assumptions prove_or_disprove_less_obvious_f6.
Goal True.
idtac " ".

idtac "-------------------  noninterferent_diff_si_same  --------------------".
idtac " ".

idtac "#> noninterferent_diff_si_same".
idtac "Possible points: 2".
check_type @noninterferent_diff_si_same (
(forall f : forall (_ : nat) (_ : nat), prod nat nat,
 iff (@noninterferent_diff_si nat nat nat nat f)
   (@noninterferent nat nat nat nat f))).
idtac "Assumptions:".
Abort.
Print Assumptions noninterferent_diff_si_same.
Goal True.
idtac " ".

idtac "-------------------  sme_another_insecure_f2  --------------------".
idtac " ".

idtac "#> sme_another_insecure_f2".
idtac "Possible points: 1".
check_type @sme_another_insecure_f2 (
(forall pi si : nat,
 @eq (prod nat nat) (@sme nat nat nat nat 0 another_insecure_f2 pi si)
   (@pair nat nat (PeanoNat.Nat.mul 2 pi) (PeanoNat.Nat.add pi si)))).
idtac "Assumptions:".
Abort.
Print Assumptions sme_another_insecure_f2.
Goal True.
idtac " ".

idtac "-------------------  sme_another_insecure_f3  --------------------".
idtac " ".

idtac "#> sme_another_insecure_f3".
idtac "Possible points: 2".
check_type @sme_another_insecure_f3 (
(forall pi si : nat,
 @eq (prod nat nat) (@sme nat nat nat nat 0 another_insecure_f3 pi si)
   (@pair nat nat pi (PeanoNat.Nat.add pi si)))).
idtac "Assumptions:".
Abort.
Print Assumptions sme_another_insecure_f3.
Goal True.
idtac " ".

idtac "-------------------  sme_correct_so  --------------------".
idtac " ".

idtac "#> sme_correct_so".
idtac "Possible points: 1".
check_type @sme_correct_so (
(forall (PI SI PO SO : Type) (some_si : SI)
   (f : forall (_ : PI) (_ : SI), prod PO SO) (pi : PI) 
   (si : SI),
 @eq SO (@snd PO SO (f pi si))
   (@snd PO SO (@sme PI SI PO SO some_si f pi si)))).
idtac "Assumptions:".
Abort.
Print Assumptions sme_correct_so.
Goal True.
idtac " ".

idtac " ".

idtac "Max points - standard: 14".
idtac "Max points - advanced: 14".
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
idtac "---------- prove_or_disprove_obvious_f1 ---------".
Print Assumptions prove_or_disprove_obvious_f1.
idtac "---------- prove_or_disprove_obvious_f2 ---------".
Print Assumptions prove_or_disprove_obvious_f2.
idtac "---------- prove_or_disprove_less_obvious_f4 ---------".
Print Assumptions prove_or_disprove_less_obvious_f4.
idtac "---------- prove_or_disprove_less_obvious_f5 ---------".
Print Assumptions prove_or_disprove_less_obvious_f5.
idtac "---------- prove_or_disprove_less_obvious_f6 ---------".
Print Assumptions prove_or_disprove_less_obvious_f6.
idtac "---------- noninterferent_diff_si_same ---------".
Print Assumptions noninterferent_diff_si_same.
idtac "---------- sme_another_insecure_f2 ---------".
Print Assumptions sme_another_insecure_f2.
idtac "---------- sme_another_insecure_f3 ---------".
Print Assumptions sme_another_insecure_f3.
idtac "---------- sme_correct_so ---------".
Print Assumptions sme_correct_so.
idtac "".
idtac "********** Advanced **********".
Abort.

(* 2026-06-24 17:07 *)
