Set Warnings "-notation-overridden,-parsing".
From Stdlib Require Export String.
From LF Require Import IndProp.

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

From LF Require Import IndProp.
Import Check.

Goal True.

idtac "-------------------  re_not_empty  --------------------".
idtac " ".

idtac "#> re_not_empty".
idtac "Possible points: 3".
check_type @re_not_empty ((forall (T : Type) (_ : reg_exp T), bool)).
idtac "Assumptions:".
Abort.
Print Assumptions re_not_empty.
Goal True.
idtac " ".

idtac "#> re_not_empty_correct".
idtac "Possible points: 3".
check_type @re_not_empty_correct (
(forall (T : Type) (re : reg_exp T),
 iff (@ex (list T) (fun s : list T => @exp_match T s re))
   (@eq bool (@re_not_empty T re) true))).
idtac "Assumptions:".
Abort.
Print Assumptions re_not_empty_correct.
Goal True.
idtac " ".

idtac "-------------------  weak_pumping_char  --------------------".
idtac " ".

idtac "#> Pumping.weak_pumping_char".
idtac "Possible points: 2".
check_type @Pumping.weak_pumping_char (
(forall (T : Type) (x : T)
   (_ : le (@Pumping.pumping_constant T (@Char T x))
          (@length T (@cons T x (@nil T)))),
 @ex (list T)
   (fun s1 : list T =>
    @ex (list T)
      (fun s2 : list T =>
       @ex (list T)
         (fun s3 : list T =>
          and (@eq (list T) (@cons T x (@nil T)) (@app T s1 (@app T s2 s3)))
            (and (not (@eq (list T) s2 (@nil T)))
               (forall m : nat,
                @exp_match T (@app T s1 (@app T (@Pumping.napp T m s2) s3))
                  (@Char T x)))))))).
idtac "Assumptions:".
Abort.
Print Assumptions Pumping.weak_pumping_char.
Goal True.
idtac " ".

idtac "-------------------  weak_pumping_app  --------------------".
idtac " ".

idtac "#> Pumping.weak_pumping_app".
idtac "Possible points: 3".
check_type @Pumping.weak_pumping_app (
(forall (T : Type) (s1 s2 : list T) (re1 re2 : reg_exp T)
   (_ : @exp_match T s1 re1) (_ : @exp_match T s2 re2)
   (_ : forall _ : le (@Pumping.pumping_constant T re1) (@length T s1),
        @ex (list T)
          (fun s3 : list T =>
           @ex (list T)
             (fun s4 : list T =>
              @ex (list T)
                (fun s5 : list T =>
                 and (@eq (list T) s1 (@app T s3 (@app T s4 s5)))
                   (and (not (@eq (list T) s4 (@nil T)))
                      (forall m : nat,
                       @exp_match T
                         (@app T s3 (@app T (@Pumping.napp T m s4) s5)) re1))))))
   (_ : forall _ : le (@Pumping.pumping_constant T re2) (@length T s2),
        @ex (list T)
          (fun s3 : list T =>
           @ex (list T)
             (fun s4 : list T =>
              @ex (list T)
                (fun s5 : list T =>
                 and (@eq (list T) s2 (@app T s3 (@app T s4 s5)))
                   (and (not (@eq (list T) s4 (@nil T)))
                      (forall m : nat,
                       @exp_match T
                         (@app T s3 (@app T (@Pumping.napp T m s4) s5)) re2))))))
   (_ : le (@Pumping.pumping_constant T (@App T re1 re2))
          (@length T (@app T s1 s2))),
 @ex (list T)
   (fun s0 : list T =>
    @ex (list T)
      (fun s3 : list T =>
       @ex (list T)
         (fun s4 : list T =>
          and (@eq (list T) (@app T s1 s2) (@app T s0 (@app T s3 s4)))
            (and (not (@eq (list T) s3 (@nil T)))
               (forall m : nat,
                @exp_match T (@app T s0 (@app T (@Pumping.napp T m s3) s4))
                  (@App T re1 re2)))))))).
idtac "Assumptions:".
Abort.
Print Assumptions Pumping.weak_pumping_app.
Goal True.
idtac " ".

idtac "-------------------  weak_pumping_union_l  --------------------".
idtac " ".

idtac "#> Pumping.weak_pumping_union_l".
idtac "Possible points: 3".
check_type @Pumping.weak_pumping_union_l (
(forall (T : Type) (s1 : list T) (re1 re2 : reg_exp T)
   (_ : @exp_match T s1 re1)
   (_ : forall _ : le (@Pumping.pumping_constant T re1) (@length T s1),
        @ex (list T)
          (fun s2 : list T =>
           @ex (list T)
             (fun s3 : list T =>
              @ex (list T)
                (fun s4 : list T =>
                 and (@eq (list T) s1 (@app T s2 (@app T s3 s4)))
                   (and (not (@eq (list T) s3 (@nil T)))
                      (forall m : nat,
                       @exp_match T
                         (@app T s2 (@app T (@Pumping.napp T m s3) s4)) re1))))))
   (_ : le (@Pumping.pumping_constant T (@Union T re1 re2)) (@length T s1)),
 @ex (list T)
   (fun s0 : list T =>
    @ex (list T)
      (fun s2 : list T =>
       @ex (list T)
         (fun s3 : list T =>
          and (@eq (list T) s1 (@app T s0 (@app T s2 s3)))
            (and (not (@eq (list T) s2 (@nil T)))
               (forall m : nat,
                @exp_match T (@app T s0 (@app T (@Pumping.napp T m s2) s3))
                  (@Union T re1 re2)))))))).
idtac "Assumptions:".
Abort.
Print Assumptions Pumping.weak_pumping_union_l.
Goal True.
idtac " ".

idtac "-------------------  reflect_iff  --------------------".
idtac " ".

idtac "#> reflect_iff".
idtac "Possible points: 2".
check_type @reflect_iff (
(forall (P : Prop) (b : bool) (_ : reflect P b), iff P (@eq bool b true))).
idtac "Assumptions:".
Abort.
Print Assumptions reflect_iff.
Goal True.
idtac " ".

idtac "-------------------  eqb_spec_practice  --------------------".
idtac " ".

idtac "#> eqb_spec_practice".
idtac "Possible points: 3".
check_type @eqb_spec_practice (
(forall (n : nat) (l : list nat) (_ : @eq nat (count n l) 0),
 not (@In nat n l))).
idtac "Assumptions:".
Abort.
Print Assumptions eqb_spec_practice.
Goal True.
idtac " ".

idtac "-------------------  nostutter_defn  --------------------".
idtac " ".

idtac "#> Manually graded: nostutter".
idtac "Possible points: 3".
print_manual_grade manual_grade_for_nostutter.
idtac " ".

idtac "-------------------  filter_challenge  --------------------".
idtac " ".

idtac "#> merge_filter".
idtac "Advanced".
idtac "Possible points: 6".
check_type @merge_filter (
(forall (X : Set) (test : forall _ : X, bool) (l l1 l2 : list X)
   (_ : @merge X l1 l2 l)
   (_ : @All X (fun n : X => @eq bool (test n) true) l1)
   (_ : @All X (fun n : X => @eq bool (test n) false) l2),
 @eq (list X) (@filter X test l) l1)).
idtac "Assumptions:".
Abort.
Print Assumptions merge_filter.
Goal True.
idtac " ".

idtac " ".

idtac "Max points - standard: 22".
idtac "Max points - advanced: 28".
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
idtac "---------- re_not_empty ---------".
Print Assumptions re_not_empty.
idtac "---------- re_not_empty_correct ---------".
Print Assumptions re_not_empty_correct.
idtac "---------- Pumping.weak_pumping_char ---------".
Print Assumptions Pumping.weak_pumping_char.
idtac "---------- Pumping.weak_pumping_app ---------".
Print Assumptions Pumping.weak_pumping_app.
idtac "---------- Pumping.weak_pumping_union_l ---------".
Print Assumptions Pumping.weak_pumping_union_l.
idtac "---------- reflect_iff ---------".
Print Assumptions reflect_iff.
idtac "---------- eqb_spec_practice ---------".
Print Assumptions eqb_spec_practice.
idtac "---------- nostutter ---------".
idtac "MANUAL".
idtac "".
idtac "********** Advanced **********".
idtac "---------- merge_filter ---------".
Print Assumptions merge_filter.
Abort.

(* 2026-06-24 16:58 *)
