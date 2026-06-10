Set Warnings "-notation-overridden,-parsing".
From Stdlib Require Export String.
From LF Require Import Logic.

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

From LF Require Import Logic.
Import Check.

Goal True.

idtac "-------------------  In_map_iff  --------------------".
idtac " ".

idtac "#> In_map_iff".
idtac "Possible points: 2".
check_type @In_map_iff (
(forall (A B : Type) (f : forall _ : A, B) (l : list A) (y : B),
 iff (@In B y (@map A B f l))
   (@ex A (fun x : A => and (@eq B (f x) y) (@In A x l))))).
idtac "Assumptions:".
Abort.
Print Assumptions In_map_iff.
Goal True.
idtac " ".

idtac "-------------------  In_app_iff  --------------------".
idtac " ".

idtac "#> In_app_iff".
idtac "Possible points: 2".
check_type @In_app_iff (
(forall (A : Type) (l l' : list A) (a : A),
 iff (@In A a (@app A l l')) (or (@In A a l) (@In A a l')))).
idtac "Assumptions:".
Abort.
Print Assumptions In_app_iff.
Goal True.
idtac " ".

idtac "-------------------  All  --------------------".
idtac " ".

idtac "#> All_In".
idtac "Possible points: 3".
check_type @All_In (
(forall (T : Type) (P : forall _ : T, Prop) (l : list T),
 iff (forall (x : T) (_ : @In T x l), P x) (@All T P l))).
idtac "Assumptions:".
Abort.
Print Assumptions All_In.
Goal True.
idtac " ".

idtac "-------------------  even_double_conv  --------------------".
idtac " ".

idtac "#> even_double_conv".
idtac "Possible points: 3".
check_type @even_double_conv (
(forall n : nat,
 @ex nat
   (fun k : nat => @eq nat n (if even n then double k else S (double k))))).
idtac "Assumptions:".
Abort.
Print Assumptions even_double_conv.
Goal True.
idtac " ".

idtac "-------------------  logical_connectives  --------------------".
idtac " ".

idtac "#> andb_true_iff".
idtac "Possible points: 1".
check_type @andb_true_iff (
(forall b1 b2 : bool,
 iff (@eq bool (andb b1 b2) true) (and (@eq bool b1 true) (@eq bool b2 true)))).
idtac "Assumptions:".
Abort.
Print Assumptions andb_true_iff.
Goal True.
idtac " ".

idtac "#> orb_true_iff".
idtac "Possible points: 1".
check_type @orb_true_iff (
(forall b1 b2 : bool,
 iff (@eq bool (orb b1 b2) true) (or (@eq bool b1 true) (@eq bool b2 true)))).
idtac "Assumptions:".
Abort.
Print Assumptions orb_true_iff.
Goal True.
idtac " ".

idtac "-------------------  eqb_neq  --------------------".
idtac " ".

idtac "#> eqb_neq".
idtac "Possible points: 1".
check_type @eqb_neq (
(forall x y : nat, iff (@eq bool (eqb x y) false) (not (@eq nat x y)))).
idtac "Assumptions:".
Abort.
Print Assumptions eqb_neq.
Goal True.
idtac " ".

idtac "-------------------  eqb_list  --------------------".
idtac " ".

idtac "#> eqb_list_true_iff".
idtac "Possible points: 3".
check_type @eqb_list_true_iff (
(forall (A : Type) (eqb : forall (_ : A) (_ : A), bool)
   (_ : forall a1 a2 : A, iff (@eq bool (eqb a1 a2) true) (@eq A a1 a2))
   (l1 l2 : list A),
 iff (@eq bool (@eqb_list A eqb l1 l2) true) (@eq (list A) l1 l2))).
idtac "Assumptions:".
Abort.
Print Assumptions eqb_list_true_iff.
Goal True.
idtac " ".

idtac "-------------------  All_forallb  --------------------".
idtac " ".

idtac "#> forallb_true_iff".
idtac "Possible points: 2".
check_type @forallb_true_iff (
(forall (X : Type) (test : forall _ : X, bool) (l : list X),
 iff (@eq bool (@forallb X test l) true)
   (@All X (fun x : X => @eq bool (test x) true) l))).
idtac "Assumptions:".
Abort.
Print Assumptions forallb_true_iff.
Goal True.
idtac " ".

idtac "-------------------  tr_rev_correct  --------------------".
idtac " ".

idtac "#> tr_rev_correct".
idtac "Possible points: 6".
check_type @tr_rev_correct (
(forall X : Type, @eq (forall _ : list X, list X) (@tr_rev X) (@rev X))).
idtac "Assumptions:".
Abort.
Print Assumptions tr_rev_correct.
Goal True.
idtac " ".

idtac "-------------------  excluded_middle_irrefutable  --------------------".
idtac " ".

idtac "#> excluded_middle_irrefutable".
idtac "Possible points: 3".
check_type @excluded_middle_irrefutable ((forall P : Prop, not (not (or P (not P))))).
idtac "Assumptions:".
Abort.
Print Assumptions excluded_middle_irrefutable.
Goal True.
idtac " ".

idtac "-------------------  not_exists_dist  --------------------".
idtac " ".

idtac "#> not_exists_dist".
idtac "Advanced".
idtac "Possible points: 3".
check_type @not_exists_dist (
(forall (_ : excluded_middle) (X : Type) (P : forall _ : X, Prop)
   (_ : not (@ex X (fun x : X => not (P x)))) (x : X),
 P x)).
idtac "Assumptions:".
Abort.
Print Assumptions not_exists_dist.
Goal True.
idtac " ".

idtac " ".

idtac "Max points - standard: 27".
idtac "Max points - advanced: 30".
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
idtac "---------- In_map_iff ---------".
Print Assumptions In_map_iff.
idtac "---------- In_app_iff ---------".
Print Assumptions In_app_iff.
idtac "---------- All_In ---------".
Print Assumptions All_In.
idtac "---------- even_double_conv ---------".
Print Assumptions even_double_conv.
idtac "---------- andb_true_iff ---------".
Print Assumptions andb_true_iff.
idtac "---------- orb_true_iff ---------".
Print Assumptions orb_true_iff.
idtac "---------- eqb_neq ---------".
Print Assumptions eqb_neq.
idtac "---------- eqb_list_true_iff ---------".
Print Assumptions eqb_list_true_iff.
idtac "---------- forallb_true_iff ---------".
Print Assumptions forallb_true_iff.
idtac "---------- tr_rev_correct ---------".
Print Assumptions tr_rev_correct.
idtac "---------- excluded_middle_irrefutable ---------".
Print Assumptions excluded_middle_irrefutable.
idtac "".
idtac "********** Advanced **********".
idtac "---------- not_exists_dist ---------".
Print Assumptions not_exists_dist.
Abort.

(* 2026-06-10 15:49 *)
