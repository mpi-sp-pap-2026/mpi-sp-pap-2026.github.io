Set Warnings "-notation-overridden,-parsing".
From Stdlib Require Export String.
From LF Require Import Logic1.

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

From LF Require Import Logic1.
Import Check.

Goal True.

idtac "-------------------  plus_is_O  --------------------".
idtac " ".

idtac "#> plus_is_O".
idtac "Possible points: 2".
check_type @plus_is_O (
(forall (n m : nat) (_ : @eq nat (Nat.add n m) 0),
 and (@eq nat n 0) (@eq nat m 0))).
idtac "Assumptions:".
Abort.
Print Assumptions plus_is_O.
Goal True.
idtac " ".

idtac "-------------------  and_assoc  --------------------".
idtac " ".

idtac "#> and_assoc".
idtac "Possible points: 1".
check_type @and_assoc ((forall (P Q R : Prop) (_ : and P (and Q R)), and (and P Q) R)).
idtac "Assumptions:".
Abort.
Print Assumptions and_assoc.
Goal True.
idtac " ".

idtac "-------------------  mult_is_O  --------------------".
idtac " ".

idtac "#> mult_is_O".
idtac "Possible points: 2".
check_type @mult_is_O (
(forall (n m : nat) (_ : @eq nat (Nat.mul n m) 0),
 or (@eq nat n 0) (@eq nat m 0))).
idtac "Assumptions:".
Abort.
Print Assumptions mult_is_O.
Goal True.
idtac " ".

idtac "-------------------  or_commut  --------------------".
idtac " ".

idtac "#> or_commut".
idtac "Possible points: 1".
check_type @or_commut ((forall (P Q : Prop) (_ : or P Q), or Q P)).
idtac "Assumptions:".
Abort.
Print Assumptions or_commut.
Goal True.
idtac " ".

idtac "-------------------  contrapositive  --------------------".
idtac " ".

idtac "#> contrapositive".
idtac "Possible points: 1".
check_type @contrapositive (
(forall (P Q : Prop) (_ : forall _ : P, Q) (_ : not Q), not P)).
idtac "Assumptions:".
Abort.
Print Assumptions contrapositive.
Goal True.
idtac " ".

idtac "-------------------  not_both_true_and_false  --------------------".
idtac " ".

idtac "#> not_both_true_and_false".
idtac "Possible points: 1".
check_type @not_both_true_and_false ((forall P : Prop, not (and P (not P)))).
idtac "Assumptions:".
Abort.
Print Assumptions not_both_true_and_false.
Goal True.
idtac " ".

idtac "-------------------  not_PNP_informal  --------------------".
idtac " ".

idtac "#> Manually graded: not_PNP_informal".
idtac "Advanced".
idtac "Possible points: 1".
print_manual_grade manual_grade_for_not_PNP_informal.
idtac " ".

idtac "-------------------  de_morgan_not_or  --------------------".
idtac " ".

idtac "#> de_morgan_not_or".
idtac "Possible points: 2".
check_type @de_morgan_not_or (
(forall (P Q : Prop) (_ : not (or P Q)), and (not P) (not Q))).
idtac "Assumptions:".
Abort.
Print Assumptions de_morgan_not_or.
Goal True.
idtac " ".

idtac "-------------------  not_S_pred_n  --------------------".
idtac " ".

idtac "#> not_S_pred_n".
idtac "Possible points: 1".
check_type @not_S_pred_n ((not (forall n : nat, @eq nat (S (Nat.pred n)) n))).
idtac "Assumptions:".
Abort.
Print Assumptions not_S_pred_n.
Goal True.
idtac " ".

idtac "-------------------  S_pred_not_zero  --------------------".
idtac " ".

idtac "#> S_pred_not_zero".
idtac "Possible points: 2".
check_type @S_pred_not_zero (
(forall (n : nat) (_ : not (@eq nat n 0)), @eq nat (S (Nat.pred n)) n)).
idtac "Assumptions:".
Abort.
Print Assumptions S_pred_not_zero.
Goal True.
idtac " ".

idtac "-------------------  or_distributes_over_and  --------------------".
idtac " ".

idtac "#> or_distributes_over_and".
idtac "Possible points: 3".
check_type @or_distributes_over_and (
(forall P Q R : Prop, iff (or P (and Q R)) (and (or P Q) (or P R)))).
idtac "Assumptions:".
Abort.
Print Assumptions or_distributes_over_and.
Goal True.
idtac " ".

idtac "-------------------  dist_not_exists  --------------------".
idtac " ".

idtac "#> dist_not_exists".
idtac "Possible points: 1".
check_type @dist_not_exists (
(forall (X : Type) (P : forall _ : X, Prop) (_ : forall x : X, P x),
 not (@ex X (fun x : X => not (P x))))).
idtac "Assumptions:".
Abort.
Print Assumptions dist_not_exists.
Goal True.
idtac " ".

idtac "-------------------  dist_exists_or  --------------------".
idtac " ".

idtac "#> dist_exists_or".
idtac "Possible points: 2".
check_type @dist_exists_or (
(forall (X : Type) (P Q : forall _ : X, Prop),
 iff (@ex X (fun x : X => or (P x) (Q x)))
   (or (@ex X (fun x : X => P x)) (@ex X (fun x : X => Q x))))).
idtac "Assumptions:".
Abort.
Print Assumptions dist_exists_or.
Goal True.
idtac " ".

idtac " ".

idtac "Max points - standard: 19".
idtac "Max points - advanced: 20".
idtac "".
idtac "Allowed Axioms:".
idtac "functional_extensionality".
idtac "FunctionalExtensionality.functional_extensionality_dep".
idtac "plus_le".
idtac "le_trans".
idtac "le_plus_l".
idtac "add_le_cases".
idtac "Sn_le_Sm__n_le_m".
idtac "O_le_n".
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
idtac "---------- plus_is_O ---------".
Print Assumptions plus_is_O.
idtac "---------- and_assoc ---------".
Print Assumptions and_assoc.
idtac "---------- mult_is_O ---------".
Print Assumptions mult_is_O.
idtac "---------- or_commut ---------".
Print Assumptions or_commut.
idtac "---------- contrapositive ---------".
Print Assumptions contrapositive.
idtac "---------- not_both_true_and_false ---------".
Print Assumptions not_both_true_and_false.
idtac "---------- de_morgan_not_or ---------".
Print Assumptions de_morgan_not_or.
idtac "---------- not_S_pred_n ---------".
Print Assumptions not_S_pred_n.
idtac "---------- S_pred_not_zero ---------".
Print Assumptions S_pred_not_zero.
idtac "---------- or_distributes_over_and ---------".
Print Assumptions or_distributes_over_and.
idtac "---------- dist_not_exists ---------".
Print Assumptions dist_not_exists.
idtac "---------- dist_exists_or ---------".
Print Assumptions dist_exists_or.
idtac "".
idtac "********** Advanced **********".
idtac "---------- not_PNP_informal ---------".
idtac "MANUAL".
Abort.

(* 2026-06-03 17:04 *)
