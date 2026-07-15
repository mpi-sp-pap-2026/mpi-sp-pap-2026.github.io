(** * StaticIFC: Information-Flow-Control Type Systems *)

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Stdlib Require Import Strings.String.
From LF Require Import Maps.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Arith.EqNat.
From Stdlib Require Import Arith.PeanoNat. Import Nat.
From Stdlib Require Import Lia.
From LF Require Import Imp.
From LF Require Import Noninterference.
From Stdlib Require Import List. Import ListNotations.
Set Default Goal Selector "!".

(* ################################################################# *)
(** * Noninterference recap and more *)

(** As explained in the [Noninterference] chapter, data
    confidentiality is most often expressed formally as a property
    called _noninterference_. *)

(** To formalize noninterference for Imp programs, we partitioned the
    variables as either [public] or [secret] using a total map
    [L : label_map] assigning each variable a Boolean label: *)

Print label. (* = bool *)
Print public. (* = true *)
Print secret. (* = false *)
Print label_map. (* = total_map label = string -> label *)

(** For simplicity, we assume that the label of each variable is
    assigned once and for all, and cannot change during execution. *)

(** We assume a noninterference attacker that can observe the
    final values of public variables, but not of secret ones.
    This may not sound particularly realistic, but:
    - as is, Imp doesn't have any other notion of outputs, so we use
      this model to keep things simple in the beginning, before we
      add more realistic outputs (e.g. an output command or side-channels);
    - in an imperative language like Imp, being able to reason about
      how secrets influence the state will remain technically
      necessary even once we add more realistic forms of output. *)

(** We formalized this as a notion of _publicly equivalent states_
    that agree on the values of all public variables: *)

Print pub_equiv.
(* fun L s1 s2 => forall x : string, L x = public -> s1 x = s2 x *)

(** For any label map [L], [pub_equiv L] is an equivalence relation
    on states, so reflexive, symmetric, and transitive. *)

(** These three lemmas ([pub_equiv_refl], [pub_equiv_sym], and
    [pub_equiv_trans]) are proved in the [Noninterference] chapter. *)

(** Program [c] is (termination-insensitive) _noninterferent_ if
    for any two terminating program runs from two publicly equivalent
    initial states [s1] and [s2], the obtained final states [s1'] and
    [s2'] are also publicly equivalent. *)

Print noninterferent_com.
(* fun L c => forall s1 s2 s1' s2', *)
(*   pub_equiv L s1 s2 -> *)
(*   s1 =[ c ]=> s1' -> *)
(*   s2 =[ c ]=> s2' -> *)
(*   pub_equiv L s1' s2'. *)

(** Intuitively, changing the value of the secret variables in the
    initial state (as allowed by [pub_equiv L s1 s2]) should lead to
    no change in the final value of the public variables (as required
    by [pub_equiv L s1' s2']). *)

(** For instance, consider the following command
    (taken from [Noninterference]): *)

Print secure_com. (* = <{ X := X+1; Y := (X-1)+Y*2 }> *)

(** Assuming that variable [X] is public and variable [Y] is secret,
    we have stated noninterference for [secure_com] as follows: *)

Print LXP. (* = (X !-> public; __ !-> secret) *)

Check noninterferent_secure_com_a_bit_harder :
  noninterferent_com LXP secure_com.

(** We have already proved that [secure_com] is indeed noninterferent
    directly using the semantics (in [Noninterference]).
    This proof was manual though, while in this chapter we will show
    how this proof can be done syntactically and automatically
    using several _information-flow-control_ (IFC) type systems that
    enforce noninterference for all well-typed programs
    [Sabelfeld and Myers 2003] (in Bib.v). *)

(** To understand what kinds of information leaks an IFC type system
    has to prevent, let us look at programs that are _not_ noninterferent.
    For instance, a program that reads the contents of a secret
    variable and uses that to change the value of a public variable is
    unlikely to be noninterferent. We call this an _explicit flow_ and
    all our type systems will prevent _all_ explicit flows.

    Here is a program that has an explicit flow, which in this case
    breaks noninterference (as we also proved in
    [Noninterference]): *)

Print insecure_com1.
(* = <{ X := Y+1; (* <- bad explicit flow! *)
        Y := (X-1)+Y*2 }> *)

Lemma interferent_com_insecure_com1 :
  ~noninterferent_com LXP insecure_com1.
Proof.
  unfold noninterferent_com, insecure_com1. intros Hni.
  assert (H1 : (Y !-> 0) =[ X := Y+1; Y := (X-1)+Y*2 ]=>
               (Y !-> 0; X !-> 1; Y !-> 0)).
  { eapply E_Seq; apply E_Asgn; reflexivity. }
  assert (H2 : (Y !-> 1) =[ X := Y+1; Y := (X-1)+Y*2 ]=>
               (Y !-> 3; X !-> 2; Y !-> 1)).
  { eapply E_Seq; apply E_Asgn; reflexivity. }
  assert (Heq : pub_equiv LXP (Y !-> 0) (Y !-> 1)).
  { intros x Hx. apply LXP_public in Hx. subst. reflexivity. }
  specialize (Hni _ _ _ _ Heq H1 H2 X LXPX).
  (* Computing the final values of [X] yields contradiction [1 = 2] *)
  unfold t_update in Hni. simpl in Hni. discriminate Hni.
Qed.

(** Explicit flows are not the only way to leak secrets though: one
    can also leak secrets using the control flow of the program, by
    branching on secrets and then assigning to public variables. We
    call these leaks _implicit flows_. *)

Print insecure_com2.
(* = <{ if Y = 0
        then Y := 42
        else X := X+1 (* <- bad implicit flow! *)
        end }> *)

(** Here the expression [X+1] we are assigning to [X] is public
    information, but we are doing this assignment after we branched on
    a secret condition [Y = 0], so we are indirectly leaking
    information about the value of [Y]. In this case we can infer that
    if [X] gets incremented the value of [Y] is not [0]. This program
    is insecure, so it will be rejected by our type systems, which
    enforce noninterference by also preventing _all_ implicit flows. *)

Lemma interferent_insecure_com2_a_bit_harder :
  ~noninterferent_com LXP insecure_com2.
Proof.
  unfold noninterferent_com, insecure_com2. intros Hni.
  assert (H1 : (Y !-> 0) =[ if Y = 0 then Y := 42 else X := X+1 end ]=>
               (Y !-> 42; Y !-> 0)).
  { apply E_IfTrue; [reflexivity | apply E_Asgn; reflexivity]. }
  assert (H2 : (Y !-> 1) =[ if Y = 0 then Y := 42 else X := X+1 end ]=>
               (X !-> 1; Y !-> 1)).
  { apply E_IfFalse; [reflexivity | apply E_Asgn; reflexivity]. }
  assert (Heq : pub_equiv LXP (Y !-> 0) (Y !-> 1)).
  { intros x Hx. apply LXP_public in Hx. subst. reflexivity. }
  specialize (Hni _ _ _ _ Heq H1 H2 X LXPX).
  (* Computing the final values of [X] yields contradiction [0 = 1] *)
  unfold t_update in Hni. simpl in Hni. discriminate Hni.
Qed.

(** Our noninterference theorems will show that preventing all explicit
    and implicit flows is _sufficient_ for enforcing noninterference. *)

(** Not all explicit/implicit flows break noninterference though.
    Here is a program that is noninterferent, even though it contains
    both an explicit and an implicit flow: *)

Definition secure_com2 :=
  <{ if Y = 0
     then X := Y (* <- harmless explicit flow *)
     else X := 0 (* <- harmless implicit flow *)
     end }>.

(** Despite the explicit and the implicit flow, this program always
    assigns [0] to [X], so no secret is leaked. We first prove
    semantically that this program always leaves [X] set to [0]: *)

Lemma secure_com2_leaves_X_eq_0 : forall s s',
  s =[ secure_com2 ]=> s' -> s' X = 0.
Proof.
  unfold secure_com2. intros s s' H.
  invert H.
  - (* then branch: [X := Y], but the guard says [Y = 0] *)
    invert H6. simpl. rewrite t_update_eq.
    simpl in H5. rewrite Nat.eqb_eq in H5. apply H5.
  - (* else branch: [X := 0] *)
    invert H6. simpl. rewrite t_update_eq. reflexivity.
Qed.

(** From this it follows that [secure_com2] is noninterferent: *)

Lemma noninterference_secure_com2 :
  noninterferent_com LXP secure_com2.
Proof.
  unfold noninterferent_com, pub_equiv.
  intros s1 s2 s1' s2' H H1 H2 x Hx.
  (* [LXP_public] is proved in the [Noninterference] chapter *)
  apply LXP_public in Hx. subst.
  apply secure_com2_leaves_X_eq_0 in H1. rewrite H1.
  apply secure_com2_leaves_X_eq_0 in H2. rewrite H2.
  reflexivity.
Qed.

(** Still, our type systems will reject programs containing any
    explicit or implicit flows, this one included. C'est la vie!
    Statically ensuring any non-trivial semantic property of programs
    is undecidable (Rice's theorem), and noninterference is definitely
    not trivial, so we need to statically overapproximate. *)

(** **** Exercise: 2 stars, standard (noninterferent_secure_com1') *)

(** As shown above, not all explicit flows break noninterference. As
    another example, the following variant of [insecure_com1] is
    noninterferent even though it has an explicit flow. The reason for
    this is that the variable [X] is overwritten with public
    information in a subsequent assignment and our noninterference
    attacker only observes the _final_ values of public variables. *)

Definition secure_com1' : com :=
  <{ X := Y+1; (* <- harmless explicit flow *)
     Y := X+Y*2;
     X := 42 (* <- X is overwritten afterwards *) }>.

(** Prove that the final value of [X] is the constant [42] in any
    execution: *)

Lemma secure_com1'_leaves_X_eq_42 : forall s s',
  s =[ secure_com1' ]=> s' -> s' X = 42.
Proof.
  (* FILL IN HERE *) Admitted.

(** Using this prove that [secure_com1'] is noninterferent: *)

Lemma noninterferent_secure_com1' :
  noninterferent_com LXP secure_com1'.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ################################################################# *)
(** * Type system for labeling expressions *)

(** We will build IFC type systems that prevent all explicit and
    implicit flows in order to statically enforce noninterference.

    Let's start with a simple component of such type systems, an IFC
    type system for arithmetic expressions: our typing judgement
    [L |-a- a \in l] specifies the label [l] of an arithmetic
    expression [a] in terms of the labels of the variables it reads.

    In particular, [L |-a- a \in public] says that expression [a] only
    reads public variables, so it computes a public value.  [L |-a- a
    \in secret] says that expression [a] reads some secret variable,
    so it computes a value that may depend on secrets. *)

(** Here are some examples:
    - For a constant [n] the label is [public], so
      [L |-a- n \in public].
    - For a variable [X] we just look up its label in L, so
      [L |-a- X \in (L X)].
    - Given variable [X1] with label [l1] and variable [X2] with
      label [l2], what should be the label of [X1 + X2] though? *)

(* ================================================================= *)
(** ** Combining labels *)

(** We need a way to combine the labels of two sub-expressions, which
    we call the _join_ (or least upper bound) of the two labels: *)

Definition join (l1 l2 : label) : label := l1 && l2.

(** Intuitively, if we add up two expressions [e1] labeled [l1] and
    [e2] labeled [l2], the result of the addition will be labeled
    [join l1 l2], which is public iff [l1] is public _and_ [l2] is public. *)

Lemma join_commutative : forall l1 l2,
  join l1 l2 = join l2 l1.
Proof. intros l1 l2. destruct l1; destruct l2; reflexivity. Qed.

Lemma join_public : forall {l1 l2},
  join l1 l2 = public -> l1 = public /\ l2 = public.
Proof. apply andb_prop. Qed.

Lemma join_public_l : forall l,
  join public l = l.
Proof. reflexivity. Qed.

Lemma join_public_r : forall l,
  join l public = l.
Proof. intros l. rewrite join_commutative. reflexivity. Qed.

Lemma join_secret_l : forall l,
  join secret l = secret.
Proof. reflexivity. Qed.

Lemma join_secret_r : forall l,
  join l secret = secret.
Proof. intros l. rewrite join_commutative.  reflexivity. Qed.

(* ================================================================= *)
(** ** Typing of arithmetic expressions *)

(** We now define a set of rules for the IFC typing relation for
    arithmetic expressions [L |-a- a \in l], which we read as follows:
    "given the label map [L] expression [a] has label [l]:" *)

(**
                          -------------------                  (T_Num)
                          L |-a- n \in public

                           -----------------                    (T_Id)
                           L |-a- X \in L X

                  L |-a- a1 \in l1    L |-a- a2 \in l2
                  ------------------------------------        (T_Plus)
                      L |-a- a1+a2 \in join l1 l2

                  L |-a- a1 \in l1    L |-a- a2 \in l2
                  ------------------------------------       (T_Minus)
                      L |-a- a1-a2 \in join l1 l2

                  L |-a- a1 \in l1    L |-a- a2 \in l2
                  ------------------------------------        (T_Mult)
                      L |-a- a1*a2 \in join l1 l2
*)

Reserved Notation "L '|-a-' a \in l" (at level 40).

Inductive aexp_has_label (L:label_map) : aexp -> label -> Prop :=
  | T_Num : forall n,
       L |-a- (ANum n) \in public
  | T_Id : forall X,
       L |-a- (AId X) \in (L X)
  | T_Plus : forall a1 l1 a2 l2,
       L |-a- a1 \in l1 ->
       L |-a- a2 \in l2 ->
       L |-a- <{ a1 + a2 }> \in (join l1 l2)
  | T_Minus : forall a1 l1 a2 l2,
       L |-a- a1 \in l1 ->
       L |-a- a2 \in l2 ->
       L |-a- <{ a1 - a2 }> \in (join l1 l2)
  | T_Mult : forall a1 l1 a2 l2,
       L |-a- a1 \in l1 ->
       L |-a- a2 \in l2 ->
       L |-a- <{ a1 * a2 }> \in (join l1 l2)

where "L '|-a-' a '\in' l" := (aexp_has_label L a l).

(* ================================================================= *)
(** ** Computing labels of arithmetic expressions *)

(** Beyond _specifying_ when an expression has a certain label as an
    inductive relation, we can also easily _compute_ the label of an
    expression: *)

Fixpoint label_of_aexp (L:label_map) (a:aexp) : label :=
  match a with
  | ANum n => public
  | AId X => L X
  | <{ a1 + a2 }>
  | <{ a1 - a2 }>
  | <{ a1 * a2 }> => join (label_of_aexp L a1) (label_of_aexp L a2)
  end.

Lemma label_of_aexp_sound : forall L a,
    L |-a- a \in label_of_aexp L a.
Proof. intros L a. induction a; constructor; eauto. Qed.

Lemma label_of_aexp_unique : forall L a l,
  L |-a- a \in l ->
  l = label_of_aexp L a.
Proof.
  intros L a l H. induction H; simpl in *; subst; auto.
Qed.

(* ================================================================= *)
(** ** Noninterference by typing for arithmetic expressions *)

Theorem noninterferent_aexp : forall {L s1 s2 a},
  pub_equiv L s1 s2 ->
  L |-a- a \in public ->
  aeval s1 a = aeval s2 a.
Proof.
  intros L s1 s2 a Heq Ht. remember public as l.
  induction Ht; simpl.
  - reflexivity.
  - apply Heq. apply Heql.
  - destruct (join_public Heql) as [H1 H2].
    rewrite (IHHt1 H1). rewrite (IHHt2 H2). reflexivity.
  - destruct (join_public Heql) as [H1 H2].
    rewrite (IHHt1 H1). rewrite (IHHt2 H2). reflexivity.
  - destruct (join_public Heql) as [H1 H2].
    rewrite (IHHt1 H1). rewrite (IHHt2 H2). reflexivity.
Qed.

(* ================================================================= *)
(** ** Typing of Boolean expressions *)

(**
                         ----------------------               (T_True)
                         L |-b- true \in public

                         -----------------------             (T_False)
                         L |-b- false \in public

                  L |-a- a1 \in l1    L |-a- a2 \in l2
                  ------------------------------------          (T_Eq)
                      L |-b- a1=a2 \in join l1 l2

...

                             L |-b- b \in l
                            ---------------                    (T_Not)
                            L |-b- ~b \in l

                  L |-b- b1 \in l1    L |-b- b2 \in l2
                  ------------------------------------         (T_And)
                      L |-b- b1&&b2 \in join l1 l2
*)

Reserved Notation "L '|-b-' b \in l" (at level 40).

Inductive bexp_has_label (L:label_map) : bexp -> label -> Prop :=
  | T_True :
       L |-b- <{ true }> \in public
  | T_False :
       L |-b- <{ false }> \in public
  | T_Eq : forall a1 l1 a2 l2,
       L |-a- a1 \in l1 ->
       L |-a- a2 \in l2 ->
       L |-b- <{ a1 = a2 }> \in (join l1 l2)
  | T_Neq : forall a1 l1 a2 l2,
       L |-a- a1 \in l1 ->
       L |-a- a2 \in l2 ->
       L |-b- <{ a1 <> a2 }> \in (join l1 l2)
  | T_Le : forall a1 l1 a2 l2,
       L |-a- a1 \in l1 ->
       L |-a- a2 \in l2 ->
       L |-b- <{ a1 <= a2 }> \in (join l1 l2)
  | T_Gt : forall a1 l1 a2 l2,
       L |-a- a1 \in l1 ->
       L |-a- a2 \in l2 ->
       L |-b- <{ a1 > a2 }> \in (join l1 l2)
  | T_Not : forall b l,
       L |-b- b \in l ->
       L |-b- <{ ~b }> \in l
  | T_And : forall b1 l1 b2 l2,
       L |-b- b1 \in l1 ->
       L |-b- b2 \in l2 ->
       L |-b- <{ b1 && b2 }> \in (join l1 l2)

where "L '|-b-' b '\in' l" := (bexp_has_label L b l).

(* ================================================================= *)
(** ** Computing labels of boolean expressions *)

Fixpoint label_of_bexp (L:label_map) (a:bexp) : label :=
  match a with
  | <{ true }> | <{ false }> => public
  | <{ a1 = a2 }>
  | <{ a1 <> a2 }>
  | <{ a1 <= a2 }>
  | <{ a1 > a2 }> => join (label_of_aexp L a1) (label_of_aexp L a2)
  | <{ ~b }> => label_of_bexp L b
  | <{ b1 && b2 }> => join (label_of_bexp L b1) (label_of_bexp L b2)
  end.

Lemma label_of_bexp_sound : forall L b,
    L |-b- b \in label_of_bexp L b.
Proof.
  intros L b. induction b; constructor;
    eauto using label_of_aexp_sound. Qed.

Lemma label_of_bexp_unique : forall L b l,
  L |-b- b \in l ->
  l = label_of_bexp L b.
Proof.
  intros L a l H.
  induction H as [ | | a1 l1 a2 l2 H1 H2
                     | a1 l1 a2 l2 H1 H2
                     | a1 l1 a2 l2 H1 H2
                     | a1 l1 a2 l2 H1 H2
                     | b l H1
                     | b1 l1 b2 l2 H1 H2];
  try apply label_of_aexp_unique in H1;
  try apply label_of_aexp_unique in H2; subst; reflexivity.
Qed.

(* ================================================================= *)
(** ** Noninterference by typing for Boolean expressions *)

Theorem noninterferent_bexp : forall {L s1 s2 b},
  pub_equiv L s1 s2 ->
  L |-b- b \in public ->
  beval s1 b = beval s2 b.
Proof.
  intros L s1 s2 b Heq Ht. remember public as l.
  induction Ht; simpl; try reflexivity;
    try (destruct (join_public Heql) as [H1 H2];
         rewrite H1 in *; rewrite H2 in *).
  - rewrite (noninterferent_aexp Heq H).
    rewrite (noninterferent_aexp Heq H0).
    reflexivity.
  - rewrite (noninterferent_aexp Heq H).
    rewrite (noninterferent_aexp Heq H0).
    reflexivity.
  - rewrite (noninterferent_aexp Heq H).
    rewrite (noninterferent_aexp Heq H0).
    reflexivity.
  - rewrite (noninterferent_aexp Heq H).
    rewrite (noninterferent_aexp Heq H0).
    reflexivity.
  - rewrite (IHHt Heql). reflexivity.
  - rewrite (IHHt1 Logic.eq_refl).
    rewrite (IHHt2 Logic.eq_refl). reflexivity.
Qed.

(* ################################################################# *)
(** * Restrictive type system preventing branching on secrets *)

(** For commands, we start with a simple type system that doesn't
    allow any branching on secrets, which is so strong that on its own
    it prevents all implicit flows. *)

(** For preventing explicit flows for assignments, we need to define
    when it is okay for information to flow from an expression with
    label [l1] to a variable with label [l2]. *)

Definition can_flow (la lx : label) : bool := la || negb lx.

(** This disjunction is only false when [la = secret] and [lx = public],
    which disallows that the value of secret expressions be assigned
    to public variables: *)

Lemma cannot_flow_secret_public : can_flow secret public = false.
Proof. reflexivity. Qed.

(** This allows public information to flow everywhere, and secret
    information to flow to secret variables: *)

Lemma can_flow_public : forall l, can_flow public l = true.
Proof. reflexivity. Qed.
Lemma can_flow_secret : can_flow secret secret = true.
Proof. reflexivity. Qed.

Lemma can_flow_refl : forall l,
  can_flow l l = true.
Proof. intros [|]; reflexivity. Qed.

Lemma can_flow_trans : forall l1 l2 l3,
  can_flow l1 l2 = true ->
  can_flow l2 l3 = true ->
  can_flow l1 l3 = true.
Proof. intros l1 l2 l3 H12 H23.
  destruct l1; destruct l2; simpl in *; auto. discriminate H12. Qed.

Lemma can_flow_join_1 : forall l1 l2 l,
  can_flow (join l1 l2) l = true ->
  can_flow l1 l = true.
Proof. intros l1 l2 l. destruct l1; [reflexivity | auto ]. Qed.

Lemma can_flow_join_2 : forall l1 l2 l,
  can_flow (join l1 l2) l = true ->
  can_flow l2 l = true.
Proof. intros l1 l2 l. destruct l1; auto. destruct l2; auto. Qed.

Lemma can_flow_join_l : forall l1 l2 l,
  can_flow l1 l = true ->
  can_flow l2 l = true ->
  can_flow (join l1 l2) l = true.
Proof. intros l1 l2 l H1 H2. destruct l1; simpl in *; auto. Qed.

Lemma can_flow_join_r1 : forall l l1 l2,
  can_flow l l1 = true ->
  can_flow l (join l1 l2) = true.
Proof. intros l l1 l2 H. destruct l; destruct l1; simpl in *; auto.
       discriminate H. Qed.

Lemma can_flow_join_r2 : forall l l1 l2,
  can_flow l l2 = true ->
  can_flow l (join l1 l2) = true.
Proof. intros l l1 l2 H. destruct l; destruct l1; simpl in *; auto. Qed.

(** For commands we use the previous relations to define a
    [cf_well_typed] relation inductively using the following rules: *)

(**
                            ------------                    (CFWT_Skip)
                            L |-cf- skip

             L |-a- a \in la   can_flow la (L X) = true
             ------------------------------------------     (CFWT_Asgn)
                           L |-cf- X := a

                      L |-cf- c1    L |-cf- c2
                      ------------------------               (CFWT_Seq)
                            L |-cf- c1;c2

           L |-b- b \in public    L |-cf- c1    L |-cf- c2
           -----------------------------------------------    (CFWT_If)
                      L |-cf- if b then c1 else c2

                  L |-b- b \in public    L |-cf- c
                  --------------------------------         (CFWT_While)
                    L |-cf- while b then c end
*)

(** Intuitively, explicit flows are prevented by the [can_flow]
    requirement in the assignment rule and implicit flows are
    prevented by the requirement that the boolean condition of [if]
    and [while] has to be a public expression. *)

Reserved Notation "L '|-cf-' c" (at level 40).

Inductive cf_well_typed (L:label_map) : com -> Prop :=
  | CFWT_Com :
      L |-cf- <{ skip }>
  | CFWT_Asgn : forall X a la,
      L |-a- a \in la ->
      can_flow la (L X) = true ->
      L |-cf- <{ X := a }>
  | CFWT_Seq : forall c1 c2,
      L |-cf- c1 ->
      L |-cf- c2 ->
      L |-cf- <{ c1 ; c2 }>
  | CFWT_If : forall b c1 c2,
      L |-b- b \in public ->
      L |-cf- c1 ->
      L |-cf- c2 ->
      L |-cf- <{ if b then c1 else c2 end }>
  | CFWT_While : forall b c1,
      L |-b- b \in public ->
      L |-cf- c1 ->
      L |-cf- <{ while b do c1 end }>

where "L '|-cf-' c" := (cf_well_typed L c).

(* ================================================================= *)
(** ** Type-Checker for [cf_well_typed] *)

Fixpoint cf_type_checker (L:label_map) (c:com) : bool :=
  match c with
  | <{ skip }> => true
  | <{ X := a }> => can_flow (label_of_aexp L a) (L X)
  | <{ c1 ; c2 }> => cf_type_checker L c1 && cf_type_checker L c2
  | <{ if b then c1 else c2 end }> =>
      Bool.eqb (label_of_bexp L b) public &&
      cf_type_checker L c1 && cf_type_checker L c2
  | <{ while b do c1 end }> =>
      Bool.eqb (label_of_bexp L b) public && cf_type_checker L c1
  end.

(** This type-checker is sound and complete with respect to the
    [cf_well_typed] relation (but as explained above,
    it can't be complete with respect to noninterference). *)

Lemma cf_type_checker_sound : forall L c,
  cf_type_checker L c = true ->
  L |-cf- c.
Proof.
  intros L c. induction c; simpl in *; econstructor;
    try rewrite andb_true_iff in *; try tauto;
    eauto using label_of_aexp_sound, label_of_bexp_sound.
  - destruct H as [H1 H2]. rewrite andb_true_iff in H1; try tauto.
    destruct H1 as [H11 H12]. apply Bool.eqb_prop in H11.
    rewrite <- H11. apply label_of_bexp_sound.
  - destruct H as [H1 H2]. rewrite andb_true_iff in H1; tauto.
  - destruct H as [H1 H2]. apply Bool.eqb_prop in H1.
    rewrite <- H1. apply label_of_bexp_sound.
Qed.

(** The proof above makes use of the [econstructor] tactic,
    which can be seen as a mix between [constructor] and
    [eapply]. Like [constructor], it applies the first constructor
    that successfully applies to the goal. Like [eapply], not all
    universally quantified variables of the applied constructor have
    to be instantiated right away, but can instead be left as
    existential variables to be instantiated later (e.g. by
    [eassumption] or [eauto]). We use this tactic extensively in this
    chapter, together with [eexists], which delays providing a witness
    to an existential quantifier by introducing an existential variable. *)

Lemma cf_type_checker_complete : forall L c,
  cf_type_checker L c = false ->
  ~(L |-cf- c).
Proof.
  intros L c H Hc. induction Hc; simpl in *;
    try rewrite andb_false_iff in *;
    try tauto; try congruence.
  - apply label_of_aexp_unique in H0.
    rewrite H0 in *. congruence.
  - destruct H; eauto. rewrite andb_false_iff in H.
    destruct H; eauto. rewrite eqb_false_iff in H.
    apply label_of_bexp_unique in H0. congruence.
  - destruct H; eauto. rewrite eqb_false_iff in H.
    apply label_of_bexp_unique in H0. congruence.
Qed.

(** It is worth noting that, while our type-checker is sound and
    complete wrt the [cf_well_typed] relation, this relation is only a
    sound overapproximation of noninterference (proved below), but not
    complete. So the type-checker is also not complete wrt
    noninterference, but it still provides an efficient way of proving
    it. For a start, let's use the type-checker to prove or disprove the
    [cf_well_typed] relation for concrete programs by computation: *)

(* ================================================================= *)
(** ** Secure program that is [cf_well_typed]: *)

Example cf_wt_secure_com :
  LXP |-cf- <{ X := X+1;  (* check: can_flow public public (OK!)  *)
               Y := X+Y*2 (* check: can_flow secret secret (OK!)  *)
             }>.
Proof. apply cf_type_checker_sound. reflexivity. Qed.

(* ================================================================= *)
(** ** Explicit flow prevented by [cf_well_typed]: *)

Example not_cf_wt_insecure_com1 :
  ~(LXP |-cf- <{ X := Y+1;  (* check: can_flow secret public (FAILS!) *)
                 Y := X+Y*2 (* check: can_flow secret secret (OK!)  *)
               }>).
Proof. apply cf_type_checker_complete. reflexivity. Qed.

(* ================================================================= *)
(** ** Implicit flow prevented by [cf_well_typed]: *)

Example not_cf_wt_insecure_com2 :
  ~(LXP |-cf- <{ if Y=0  (* check: L |-b- Y=0 \in public (FAILS!) *)
                 then Y := 42
                 else X := X+1 (* <- bad implicit flow! *)
                 end }>).
Proof. apply cf_type_checker_complete. reflexivity. Qed.

(* ================================================================= *)
(** ** Noninterference enforced by [cf_well_typed] *)

(** We start with a few lemmas connecting public equivalence with
    state updates: public equivalence of two states is preserved by
    assigning the _same_ value to a variable in both states, and also
    by updating a _secret_ variable on either side (or on both sides,
    with _any_ two values). *)

Lemma pub_equiv_update_same : forall L s1 s2 x v,
  pub_equiv L s1 s2 ->
  pub_equiv L (x !-> v; s1) (x !-> v; s2).
Proof.
  intros L s1 s2 x v Heq y Hy. unfold t_update.
  (* the two sides differ only in the [else] branch *)
  rewrite (Heq y Hy). reflexivity.
Qed.

Lemma pub_equiv_update_secret_l : forall L s1 s2 x v,
  pub_equiv L s1 s2 ->
  L x = secret ->
  pub_equiv L (x !-> v; s1) s2.
Proof.
  intros L s1 s2 x v Heq Hx y Hy.
  (* the secret [x] cannot be the public [y] *)
  assert (Hxy : x <> y).
  { intro Hc. subst. rewrite Hy in Hx. discriminate Hx. }
  rewrite (t_update_neq _ _ _ _ _ Hxy). apply Heq. apply Hy.
Qed.

Lemma pub_equiv_update_secret_r : forall L s1 s2 x v,
  pub_equiv L s1 s2 ->
  L x = secret ->
  pub_equiv L s1 (x !-> v; s2).
Proof.
  intros L s1 s2 x v Heq Hx. apply pub_equiv_sym.
  apply pub_equiv_update_secret_l.
  - apply pub_equiv_sym. apply Heq.
  - apply Hx.
Qed.

Lemma pub_equiv_update_secret : forall L s1 s2 x v1 v2,
  pub_equiv L s1 s2 ->
  L x = secret ->
  pub_equiv L (x !-> v1; s1) (x !-> v2; s2).
Proof.
  intros L s1 s2 x v1 v2 Heq Hx.
  apply pub_equiv_update_secret_l.
  - apply pub_equiv_update_secret_r.
    + apply Heq.
    + apply Hx.
  - apply Hx.
Qed.

(** We show that all [cf_well_typed] commands are [noninterferent]: *)

Theorem cf_well_typed_noninterferent : forall L c,
  L |-cf- c ->
  noninterferent_com L c.
Proof.
  intros L c Hwt s1 s2 s1' s2' Heq Heval1 Heval2.
  generalize dependent s2'. generalize dependent s2.
  induction Heval1; intros s2 Heq s2' Heval2;
    inversion Heval2; inversion Hwt; subst.
  - (* Skip *) assumption.
  - (* Asgn *)
    unfold can_flow in H8. apply orb_true_iff in H8.
    destruct H8 as [Hl | Hx].
    + (* l = public: both sides assign the same value to x *)
      rewrite Hl in H7. rewrite (noninterferent_aexp Heq H7).
      apply pub_equiv_update_same. assumption.
    + (* L x = secret: the assigned values don't matter *)
      apply negb_true_iff in Hx.
      apply pub_equiv_update_secret; assumption.
  - (* Seq *)
    eapply IHHeval1_2; try eassumption.
    eapply IHHeval1_1; eassumption.
  - (* IfTrue + IfTrue *) eapply IHHeval1; eassumption.
  - (* IfTrue + IfFalse - contradiction (prevented by typing) *)
    rewrite (noninterferent_bexp Heq H10) in H.
    rewrite H in H5. discriminate H5.
  - (* IfFalse + IfTrue - contradiction (prevented by typing) *)
    rewrite (noninterferent_bexp Heq H10) in H.
    rewrite H in H5. discriminate H5.
  - (* IfFalse + IfFalse *) eapply IHHeval1; eassumption.
  - (* WhileFalse + WhileFalse *) assumption.
  - (* WhileFalse + WhileTrue - contradiction (prevented by typing) *)
    rewrite (noninterferent_bexp Heq H9) in H.
    rewrite H in H2. discriminate H2.
  - (* WhileTrue + WhileFalse - contradiction (prevented by typing) *)
    rewrite (noninterferent_bexp Heq H7) in H.
    rewrite H in H4. discriminate H4.
  - (* WhileTrue + WhileTrue *)
    eapply IHHeval1_2; try eassumption. eapply IHHeval1_1; eassumption.
Qed.

(** Remember the definition of [noninterferent_com] is as follows:

forall s1 s2 s1' s2',
  pub_equiv L s1 s2 ->
  s1 =[ c ]=> s1' ->
  s2 =[ c ]=> s2' ->
  pub_equiv L s1' s2'.

   The main intuition is that the two executions will proceed "in
   lockstep", because all the branch conditions are enforced to be
   public, so they will evaluate to the same boolean in both executions. *)

(** The proof is by induction on [s1 =[ c ]=> s1'] and inversion
    on [s2 =[ c ]=> s2'] and [L |-cf- c]. Here is an informal sketch of
    the two most interesting cases:

    - In the conditional case we have that [c] is [if b then c1 else c2],
      [L |-cf- c1], [L |-cf- c2], and [L |-b- b \in public]. Given this
      last fact we can apply noninterference of boolean expressions to
      show that [beval st1 b = beval st2 b]. If they are both [true],
      we use the induction hypothesis for [c1], and if they are both
      false we use the induction hypothesis for [c2] to conclude.

    - In the assignment case we have that [c] is [X := a],
      [L |-a- a \in l], and [can_flow l (L X) = true], which expands out
      to [l = public \/ L X = secret].

      If [l = public] then by noninterference of arithmetic
      expressions [aeval st1 a = aeval s2 a], so we are
      assigning the same value to X, which leads to public equivalent
      final states, since the initial states were public equivalent.
      Formally, this case uses lemma [pub_equiv_update_same] above.

      If [L X = secret] then the value we assign to [X] doesn't matter
      for determining whether the final states are [pub_equiv].
      Formally, this case uses lemma [pub_equiv_update_secret] above. *)

(* ================================================================= *)
(** ** [cf_well_typed] too strong for just noninterference *)

(** While we have just proved that [cf_well_typed] implies
    noninterference, this type system is too restrictive for enforcing just
    noninterference. For instance, the following program is rejected
    by the type system just because it branches on a secret: *)

(** **** Exercise: 1 star, standard (not_cf_wt_noninterferent_com) *)

(** Use the type-checker to prove that the following program is
    not [cf_well_typed] (Hint: This can be proved very easily, if
    stuck see examples above): *)
Example not_cf_wt_noninterferent_com :
  ~(LXP |-cf- <{ if Y=0 (* check: L |-b- Y=0 \in public (fails!) *)
                 then Z := 0
                 else skip
                 end }>).
Proof. (* FILL IN HERE *) Admitted.
(** [] *)

(** Yet this program contains no explicit flows and no implicit flows
    (since the assigned variable [Z] is secret), so it is intuitively secure. *)

(** With a bit more work we can prove this formally: *)
Example not_cf_wt_noninterferent_com_is_noninterferent:
  noninterferent_com LXP <{ if Y=0
                             then Z := 0
                             else skip
                             end }>.
Proof.
  unfold noninterferent_com.
  intros s1 s2 s1' s2' H red1 red2.
  invert red1; invert red2; invert H6; invert H8.
  - (* both runs assign to the secret [Z] *)
    apply pub_equiv_update_secret; [apply H | reflexivity].
  - (* only the first run assigns to [Z] *)
    apply pub_equiv_update_secret_l; [apply H | reflexivity].
  - (* only the second run assigns to [Z] *)
    apply pub_equiv_update_secret_r; [apply H | reflexivity].
  - (* neither run assigns, so the states unchanged *)
    apply H.
Qed.

(** We will later show that [cf_well_typed] enforces not just
    noninterference, but also a security notion called Control Flow
    security, which prevents some side-channel attacks and which also
    serves as the base for cryptographic constant-time. *)

(* ################################################################# *)
(** * IFC type system allowing branching on secrets *)

(** Let's now investigate a more permissive type system for
    noninterference in which we do allow branching on secrets
    [Volpano et al 1996] (in Bib.v).

    Now to prevent implicit flows we need to track whether we have
    branched on secrets. We do this with a _program counter_ ([pc])
    label, which records the labels of the branches we have taken at
    the current point in the execution (joined together). *)

(**
                      ----------------                      (NIWT_Skip)
                      L ;; pc |-ni- skip

      L |-a- a \in la   can_flow (join pc la) (L X) = true
      ----------------------------------------------------  (NIWT_Asgn)
                     L ;; pc |-ni- X := a

                L ;; pc |-ni- c1    L ;; pc |-ni- c2
                --------------------------------             (NIWT_Seq)
                      L ;; pc |-ni- c1;c2

           L |-b- b \in l    L ;; join pc l |-ni- c1
                             L ;; join pc l |-ni- c2
           ---------------------------------------            (NIWT_If)
                L ;; pc |-ni- if b then c1 else c2

              L |-b- b \in l    L ;; join pc l |-ni- c
              --------------------------------------       (NIWT_While)
                L ;; pc |-ni- while b then c end
*)

(** We now allow branching on arbitrary boolean expressions in [if]
    and [while], but join the label of the branch expression to the
    [pc]. Then in the assignment rule we require that also the [pc]
    label flows to the label of the assigned variable, in order to
    still prevent implicit flows. *)

(** Also the sequence rule is more interesting than it may look: both [c1]
    and [c2] are type-checked under the _same_ [pc] label as the whole
    sequence. In particular, branching on secrets _inside_ [c1] raises
    the pc label only for the branches of [c1]: once these branches
    finish, the control flow joins back at a single program point, and
    [c2] gets executed no matter which branch was taken. So it is fine
    to type-check [c2] at the original [pc] label, unaffected by the
    branching in [c1]. For instance,
    [[if Y = 0 then Z := 0 else skip end; X := 42]] is well-typed:
    the assignment to the public variable [X] happens
    only after the control flow has joined, so it doesn't leak any
    information about the secret [Y]. Resetting the pc label this way
    is possible because Imp only has structured control flow; in a
    language with unstructured jumps (e.g. [goto]) tracking the pc
    label would be much harder. *)

Reserved Notation "L ';;' pc '|-ni-' c" (at level 40).

Inductive ni_well_typed (L:label_map) : label -> com -> Prop :=
  | NIWT_Com : forall pc,
      L ;; pc |-ni- <{ skip }>
  | NIWT_Asgn : forall pc X a la,
      L |-a- a \in la ->
      can_flow (join pc la) (L X) = true ->
      L ;; pc |-ni- <{ X := a }>
  | NIWT_Seq : forall pc c1 c2,
      L ;; pc |-ni- c1 ->
      L ;; pc |-ni- c2 ->
      L ;; pc |-ni- <{ c1 ; c2 }>
  | NIWT_If : forall pc b l c1 c2,
      L |-b- b \in l ->
      L ;; (join pc l) |-ni- c1 ->
      L ;; (join pc l) |-ni- c2 ->
      L ;; pc |-ni- <{ if b then c1 else c2 end }>
  | NIWT_While : forall pc b l c1,
      L |-b- b \in l ->
      L ;; (join pc l) |-ni- c1 ->
      L ;; pc |-ni- <{ while b do c1 end }>

where "L ';;' pc '|-ni-' c" := (ni_well_typed L pc c).

(* ================================================================= *)
(** ** Type-Checker for [ni_well_typed] relation *)

Fixpoint ni_type_checker (L:label_map) (pc:label) (c:com) : bool :=
  match c with
  | <{ skip }> => true
  | <{ X := a }> => can_flow (join pc (label_of_aexp L a)) (L X)
  | <{ c1 ; c2 }> => ni_type_checker L pc c1 && ni_type_checker L pc c2
  | <{ if b then c1 else c2 end }> =>
      ni_type_checker L (join pc (label_of_bexp L b)) c1 &&
      ni_type_checker L (join pc (label_of_bexp L b)) c2
  | <{ while b do c1 end }> =>
      ni_type_checker L (join pc (label_of_bexp L b)) c1
  end.

Lemma ni_type_checker_sound : forall L pc c,
  ni_type_checker L pc c = true ->
  L ;; pc |-ni- c.
Proof.
  intros L pc c. generalize dependent pc.
  induction c; intros pc H; simpl in *; econstructor;
    try rewrite andb_true_iff in *;
    try destruct H; try tauto;
    eauto using label_of_aexp_sound, label_of_bexp_sound.
Qed.

Lemma ni_type_checker_complete : forall L pc c,
  ni_type_checker L pc c = false ->
  ~(L ;; pc |-ni- c).
Proof.
  intros L pc c H Hc. induction Hc; simpl in *;
    try rewrite andb_false_iff in *; try tauto; try congruence.
  - apply label_of_aexp_unique in H0.
    rewrite H0 in *. congruence.
  - destruct H; apply label_of_bexp_unique in H0; subst; eauto.
  - destruct H; apply label_of_bexp_unique in H0; subst; eauto.
Qed.

(** With this more permissive type system we can accept more
    noninterferent programs that were rejected by [cf_well_typed],
    including an extension of the one we saw above: *)

Example ni_wt_noninterferent_com :
  LXP ;; public |-ni-
    <{ if Y=0 (* raises pc label from public to secret *)
       then Z := 0 (* check: [can_flow secret secret] (OK!) *)
       else skip
       end;
       X := 42 (* pc reset to public;
                  check: [can_flow public public] (OK!) *) }>.
Proof. apply ni_type_checker_sound. reflexivity. Qed.

(** And we still prevent implicit flows: *)

Example not_ni_wt_insecure_com2 :
  ~(LXP ;; public |-ni-
    <{ if Y=0  (* raises pc label from public to secret *)
       then Y := 42
       else X := X+1 (* check: [can_flow secret public] (FAILS!)  *)
       end }>).
Proof. apply ni_type_checker_complete. reflexivity. Qed.

(* ================================================================= *)
(** ** Dealing with unsynchronized executions running different code *)

(** For proving that the type system above still enforces
    noninterference even though it allows branching on secrets the
    [different_code] corollary below is crucial, and its proof follows
    easily from the following basic lemma: *)

Lemma secret_run : forall L c s s',
  L;; secret |-ni- c ->
  s =[ c ]=> s' ->
  pub_equiv L s s'.
Proof.
  intros L c s s' Hwt Heval. induction Heval; inversion Hwt;
    subst; eauto using pub_equiv_trans, pub_equiv_refl.
  - (* assignment case: crucial for preventing implicit flows *)
    apply pub_equiv_update_secret_r.
    + apply pub_equiv_refl.
    + (* the type system prevents public variables from
         being assigned after branching on secrets *)
      rewrite join_secret_l in H4. apply negb_true_iff. apply H4.
Qed.

Corollary different_code : forall L c1 c2 s1 s2 s1' s2',
  L;; secret |-ni- c1 ->
  L;; secret |-ni- c2 ->
  pub_equiv L s1 s2 ->
  s1 =[ c1 ]=> s1' ->
  s2 =[ c2 ]=> s2' ->
  pub_equiv L s1' s2'.
Proof.
  intros L c1 c2 s1 s2 s1' s2' Hwt1 Hwt2 Hequiv Heval1 Heval2.
  eapply secret_run in Hwt1; [| eassumption].
  eapply secret_run in Hwt2; [| eassumption].
  apply pub_equiv_sym in Hwt1.
  eapply pub_equiv_trans; try eassumption.
  eapply pub_equiv_trans; eassumption.
Qed.

(* ================================================================= *)
(** ** We show that [ni_well_typed] commands are noninterferent *)

Theorem ni_well_typed_noninterferent : forall L pc c,
  L;; pc |-ni- c ->
  noninterferent_com L c.
Proof.
  intros L pc c Hwt s1 s2 s1' s2' Heq Heval1 Heval2.
  generalize dependent s2'. generalize dependent s2.
  generalize dependent pc.
  induction Heval1; intros pc Hwt s2 Heq s2' Heval2;
    inversion Heval2; inversion Hwt; subst.
  - assumption.
  - (* Asgn *)
    unfold can_flow in H9. apply orb_true_iff in H9. destruct H9 as [Hl | Hx].
    + (* l = public: both sides assign the same value to x *)
      apply join_public in Hl. destruct Hl as [_ Hl]. subst.
      rewrite (noninterferent_aexp Heq H8).
      apply pub_equiv_update_same. assumption.
    + (* L x = secret: the assigned values don't matter *)
      apply negb_true_iff in Hx.
      apply pub_equiv_update_secret; assumption.
  - eapply IHHeval1_2; try eassumption. eapply IHHeval1_1; eassumption.
  - (* if true-true *)
    eapply IHHeval1; eassumption.
  - (* if true-false *) destruct l.
    + rewrite (noninterferent_bexp Heq H11) in H.
      rewrite H in H5. discriminate H5.
    + repeat rewrite join_secret_r in *.
      eapply different_code with (c1:=c1) (c2:=c2); eassumption.
  - (* if false-true *) destruct l.
    + rewrite (noninterferent_bexp Heq H11) in H.
      rewrite H in H5. discriminate H5.
    + repeat rewrite join_secret_r in *.
      eapply different_code with (c1:=c2) (c2:=c1); eassumption.
  - (* if false-false *)
    eapply IHHeval1; eassumption.
  - (* while false-false *) assumption.
  - (* while false-true *) destruct l.
    + rewrite (noninterferent_bexp Heq H10) in H.
      rewrite H in H2. discriminate H2.
    + repeat rewrite join_secret_r in *.
      eapply different_code with (c1:=<{skip}>) (c2:=<{c;while b do c end}>);
        repeat (try eassumption; try econstructor).
  - (* while true-false *) destruct l.
    + rewrite (noninterferent_bexp Heq H8) in H.
      rewrite H in H4. discriminate H4.
    + repeat rewrite join_secret_r in *.
      eapply different_code with (c1:=<{c;while b do c end}>) (c2:=<{skip}>);
        repeat (try eassumption; try econstructor).
  - (* while true-true *)
    eapply IHHeval1_2; try eassumption. eapply IHHeval1_1; eassumption.
Qed.

(** The noninterference proof is still relatively simple, since the
    cases in which we take different branches based on secret
    information are all handled by the [different_code] lemma.

    Another key ingredient for having a simple noninterference proof
    is working with a big-step semantics for Imp. *)

(* ################################################################# *)
(** * Type system for termination-sensitive noninterference *)

(** The noninterference notion we used above was "termination
    insensitive". If we reject loop conditions depending on secrets we
    can actually enforce termination-sensitive noninterference (TSNI),
    in which the attacker can also observe whether the program
    terminates or not. *)

(** So we can prove that [cf_well_typed] enforces TSNI, but that
    typing relation is too restrictive, since for TSNI we can allow
    if-then-else conditions to depend on secrets. So we define another
    type system that only prevents _loop_ conditions from depending on
    secrets [Volpano and Smith 1997] (in Bib.v). *)

(** We just need to update the while rule of [ni_well_typed].
    Here is the old rule for termination-insensitive noninterference (TINI):

              L |-b- b \in l    L ;; join pc l |-ni- c
              --------------------------------------       (NIWT_While)
                L ;; pc |-ni- while b then c end

    Here is the new rule for termination-sensitive noninterference (TSNI):

          L |-b- b \in public    L ;; public |-ts- c
          ------------------------------------------       (TSWT_While)
             L ;; public |-ts- while b then c end

   Beyond requiring the label of [b] to be [public], this rule also
   requires that once one branches on secrets with if-then-else
   (i.e. [pc=secret]) no while loops are allowed. *)

Reserved Notation "L ';;' pc '|-ts-' c" (at level 40).

Inductive ts_well_typed (L:label_map) : label -> com -> Prop :=
  | TSWT_Com : forall pc,
      L;; pc |-ts- <{ skip }>
  | TSWT_Asgn : forall pc X a la,
      L |-a- a \in la ->
      can_flow (join pc la) (L X) = true ->
      L;; pc |-ts- <{ X := a }>
  | TSWT_Seq : forall pc c1 c2,
      L;; pc |-ts- c1 ->
      L;; pc |-ts- c2 ->
      L;; pc |-ts- <{ c1 ; c2 }>
  | TSWT_If : forall pc b l c1 c2,
      L |-b- b \in l ->
      L;; (join pc l) |-ts- c1 ->
      L;; (join pc l) |-ts- c2 ->
      L;; pc |-ts- <{ if b then c1 else c2 end }>
  | TSWT_While : forall b c1,
      L |-b- b \in public -> (* <-- NEW *)
      L;; public |-ts- c1 -> (* <-- ONLY pc=public *)
      L;; public |-ts- <{ while b do c1 end }>

where "L ';;' pc '|-ts-' c" := (ts_well_typed L pc c).

(* ================================================================= *)
(** ** TSNI Type-Checker *)

(** In the following exercises you will write a type-checker for the TSNI type
    system above and prove your type-checker sound and complete. *)

(** **** Exercise: 2 stars, standard (ts_type_checker) *)
Fixpoint ts_type_checker (L:label_map) (pc:label) (c:com) : bool :=
  match c with
  | <{ skip }> => true
  | <{ X := a }> => can_flow (join pc (label_of_aexp L a)) (L X)
  | <{ c1 ; c2 }> => ts_type_checker L pc c1 && ts_type_checker L pc c2
  | <{ if b then c1 else c2 end }> =>
      ts_type_checker L (join pc (label_of_bexp L b)) c1 &&
      ts_type_checker L (join pc (label_of_bexp L b)) c2
  (* FILL IN HERE *)
   | _ => false (* <--- Add your type-checking code for while here *)
    end.
(** [] *)

(** **** Exercise: 2 stars, standard (ts_type_checker_sound) *)
Lemma ts_type_checker_sound : forall L pc c,
  ts_type_checker L pc c = true ->
  L ;; pc |-ts- c.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard (ts_type_checker_complete) *)
Lemma ts_type_checker_complete : forall L pc c,
  ts_type_checker L pc c = false ->
  ~(L ;; pc |-ts- c).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** With this termination-sensitive type system, we reject programs
    where the termination behavior itself leaks secret information: *)

Print termination_leak.
(* =  <{ if Y = 0                    (* Y is a secret variable *)
         then while true do skip end (* if Y = 0 run forever *)
         else skip                   (* if Y <> 0 terminate immediately *)
         end }>. *)

(** Our previous termination-insensitive type system accepts this program: *)

Example ni_termination_leak :
  LXP ;; public |-ni- termination_leak.
Proof. apply ni_type_checker_sound. reflexivity. Qed.

(** But our new termination-sensitive type system rejects it,
    and you can use your own type-checker to prove it: *)

(** **** Exercise: 1 star, standard (not_ts_non_termination_com) *)
Example not_ts_non_termination_com :
  ~(LXP ;; public |-ts- termination_leak).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** We defined TSNI in [Noninterference] as follows: *)

Print tsni_com_R.
(* fun R L c => *)
(*   forall s1 s2 s1', *)
(*   R c s1 s1' -> *)
(*   pub_equiv L s1 s2 -> *)
(*   (exists s2', R c s2 s2' /\ pub_equiv L s1' s2'). *)

(** We just instantiate relation [R] in this definition to [ceval]: *)

Definition tsni_com := tsni_com_R ceval.

(* ================================================================= *)
(** ** Equivalent [tsni] characterization *)

(** To prove the security of the termination-sensitive type system,
    we rely on an equivalent characterization of [tsni]: *)

Definition pub_equiv_equiterminating L c := forall s1 s1',
  s1 =[ c ]=> s1' ->
  forall s2, pub_equiv L s1 s2 ->
  exists s2', s2 =[ c ]=> s2'.

Definition tsni_alt L c :=
  noninterferent_com L c /\ pub_equiv_equiterminating L c.

Lemma tsni_com_tsni_alt_same: forall L c,
  tsni_com L c <-> tsni_alt L c.
Proof.
  unfold tsni_com, tsni_com_R, tsni_alt. split.
  (* tsni_com -> tsni_alt *)
  - intros H. split.
    + (* noninterferent *)
      unfold noninterferent_com.
      intros s1 s2 s1' s2' PEQ E1 E2.
      eapply H in E1; eauto. destruct E1 as [s2'' [E2' PEQ']].
      (* The [tsni] definition requires that Imp is deterministic. *)
      eapply ceval_deterministic in E2; eauto. subst. eauto.
    + (* pub_equiv_equiterminating *)
      unfold pub_equiv_equiterminating. intros s1 s1' E1 s2 PEQ1.
      eapply H in E1; eauto. destruct E1 as [s2' [E2 PEQ2]].
      eexists. eassumption.
  (* tsni_alt -> tsni_com *)
  - intros [NI EQT] s1 s2 s1' E1 PEQ.
    specialize (EQT s1 s1' E1 s2 PEQ). destruct EQT as [s2' E].
    specialize (NI s1 s2 s1' s2' PEQ E1 E).
    exists s2'. split; auto.
Qed.

(* ================================================================= *)
(** ** We first prove that [ts_well_typed] enforces [noninterference] *)

(** We show that [ts_well_typed] implies [ni_well_typed], so by our
    previous theorem also (termination-insensitive) [noninterference]. *)

Theorem ts_well_typed_ni_well_typed : forall L c pc,
  L;; pc |-ts- c ->
  L;; pc |-ni- c.
Proof.
  intros L c pc H. induction H; econstructor; eassumption.
Qed.

Theorem ts_well_typed_noninterferent : forall L c,
  L;; public |-ts- c ->
  noninterferent_com L c.
Proof.
  intros L c H. apply ts_well_typed_ni_well_typed in H.
  apply ni_well_typed_noninterferent in H. apply H.
Qed.

(* ================================================================= *)
(** ** We use this to show [ts_well_typed] enforces equitermination *)

(** Then we show that [L;; secret |-ts- c] ensures that [c] terminates
    for all initial states: *)

Lemma ts_secret_run_terminating : forall L c s,
  L;; secret |-ts- c ->
  exists s', s =[ c ]=> s'.
Proof.
  intros L c s Hwt. remember secret as l.
  generalize dependent s. induction Hwt; intro s.
  - eexists. econstructor.
  - eexists. econstructor. reflexivity.
  - destruct (IHHwt1 Heql s) as  [s' IH1].
    destruct (IHHwt2 Heql s') as [s'' IH2]. eexists. econstructor; eassumption.
  - rewrite Heql in *. rewrite join_secret_l in *.
    destruct (IHHwt1 Logic.eq_refl s) as [s1 IH1].
    destruct (IHHwt2 Logic.eq_refl s) as [s2 IH2].
    destruct (beval s b) eqn:Heq; eexists; econstructor; eassumption.
  - discriminate Heql.
Qed.

(** We use this to show that [ts_well_typed] implies equitermination.
    This proof uses [ts_well_typed_noninterferent], since otherwise
    induction doesn't go through for the [E_Seq] and [E_WhileTrue] cases: *)

Print pub_equiv_equiterminating.
(* = fun L c => forall s1 s1', *)
(*     s1 =[ c ]=> s1' -> *)
(*     forall s2, pub_equiv L s1 s2 -> *)
(*     exists s2', s2 =[ c ]=> s2'. *)

Theorem ts_wt_pub_equiv_equiterminating : forall L c,
  L;; public |-ts- c ->
  pub_equiv_equiterminating L c.
Proof.
  intros L C Hwt s1 s1' Heval.
  induction Heval; intros s2 Heq; inversion Hwt; subst.
  - eexists. constructor.
  - eexists. econstructor. reflexivity.
  - destruct (IHHeval1 H2 _ Heq) as [s2' IH1].
    assert (Heq' : pub_equiv L st' s2').
    { eapply ts_well_typed_noninterferent;
        [ | eassumption | eassumption | eassumption]. assumption. }
    destruct (IHHeval2 H3 _ Heq') as [s2'' IH2].
    eexists. econstructor; eassumption.
  - rewrite join_public_l in *. destruct l.
    + destruct (IHHeval H5 _ Heq) as [s2' IH1].
      eexists. apply E_IfTrue; [ | eassumption ].
      * eapply noninterferent_bexp in Heq; [ | eassumption ]. congruence.
    + eapply ts_secret_run_terminating in H5. destruct H5 as [s1' H5].
      eapply ts_secret_run_terminating in H6. destruct H6 as [s2' H6].
      destruct (beval s2 b) eqn:Heq2; eexists; econstructor; eassumption.
  - rewrite join_public_l in *. destruct l.
    + destruct (IHHeval H6 _ Heq) as [s2' IH1].
      eexists. apply E_IfFalse; [ | eassumption ].
      * eapply noninterferent_bexp in Heq; [ | eassumption ]. congruence.
    + eapply ts_secret_run_terminating in H5. destruct H5 as [s1' H5].
      eapply ts_secret_run_terminating in H6. destruct H6 as [s2' H6].
      destruct (beval s2 b) eqn:Heq2; eexists; econstructor; eassumption.
  - eapply noninterferent_bexp in Heq; [ | eassumption ].
    eexists. apply E_WhileFalse. congruence.
  - destruct (IHHeval1 H3 _ Heq) as [s2' IH1].
    assert (Heq' : pub_equiv L st' s2').
    { eapply ts_well_typed_noninterferent;
        [ | eassumption | eassumption | eassumption]. assumption. }
    destruct (IHHeval2 Hwt _ Heq') as [s2'' IH2].
    eapply noninterferent_bexp in Heq; [ | eassumption ].
    eexists. eapply E_WhileTrue; try congruence; eassumption.
Qed.

(* ================================================================= *)
(** ** We put things together to prove [ts_well_typed] enforces [tsni] *)

(** Finally, (termination-insensitive) noninterference together with
    equitermination directly implies [tsni]: *)

Corollary ts_well_typed_tsni : forall L c,
  L;; public |-ts- c ->
  tsni_com L c.
Proof.
  intros L c Hwt. apply tsni_com_tsni_alt_same. split.
  - apply ts_well_typed_noninterferent. assumption.
  - eapply ts_wt_pub_equiv_equiterminating. assumption.
Qed.

(** **** Exercise: 2 stars, standard (cf_well_typed_tsni) *)

(** The restrictive [cf_well_typed] relation from the beginning of the
    chapter is stronger than [ts_well_typed]: it prevents not only
    loop conditions from depending on secrets, but any branching on
    secrets at all. Prove that any [cf_well_typed] command is also
    [ts_well_typed] under the [public] pc label. (Hint: this proof can
    be done in one line.) *)

Theorem cf_well_typed_ts_well_typed : forall L c,
  L |-cf- c ->
  L;; public |-ts- c.
Proof.
  (* FILL IN HERE *) Admitted.

(** Use this to conclude that [cf_well_typed] also enforces [tsni]: *)

Corollary cf_well_typed_tsni : forall L c,
  L |-cf- c ->
  tsni_com L c.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ################################################################# *)
(** * Control Flow security *)

(** Especially for cryptographic code one is also worried about
    side-channel attacks, in which secrets are for instance leaked via
    the execution time of the program. Running different sequences of
    instructions will likely result in different execution times.
    Moreover, most processors have instruction caches, which make
    executing cached instructions faster than non-cached ones.
    To prevent such timing attacks, cryptographic code is normally
    written without any branching on secrets.

    To formalize this at a high-level we introduce a security notion
    called _Control Flow (CF) security_ (sometimes called PC security
    [Molnar et al 2005] (in Bib.v)), which considers the program's branching
    visible to the attacker. More precisely, we instrument the
    operational semantics of [Imp] to also record the control-flow
    decisions of the program. *)

Definition branches := list bool.

(* ================================================================= *)
(** ** Instrumented semantics with branches

                     ---------------------                         (CFE_Skip)
                     st =[ skip ]=> st, []

                       aeval st a = n
               -----------------------------------                 (CFE_Asgn)
               st =[ x := a ]=> (x !-> n ; st), []

      st  =[ c1 ]=> st', bs1   st' =[ c2 ]=> st'', bs2
      ------------------------------------------------              (CFE_Seq)
               st =[ c1;c2 ]=> st'', (bs1++bs2)

            beval st b = true     st =[ c1 ]=> st', bs1
        -------------------------------------------------        (CFE_IfTrue)
        st =[ if b then c1 else c2 end ]=> st', true::bs1

            beval st b = false    st =[ c2 ]=> st', bs2
       --------------------------------------------------       (CFE_IfFalse)
       st =[ if b then c1 else c2 end ]=> st', false::bs2

 st =[ if b then (c; while b do c end) else skip end ]=> st', bs
 ---------------------------------------------------------------  (CFE_While)
           st =[ while b do c end ]=> st', bs
*)

Reserved Notation
         "st '=[' c ']=>' st' , bs"
         (at level 40, c custom com at level 99,
          st constr, st' constr at next level).

Inductive cf_ceval : com -> state -> state -> branches -> Prop :=
  | CFE_Skip : forall st,
      st =[ skip ]=> st, []
  | CFE_Asgn  : forall st a n x,
      aeval st a = n ->
      st =[ x := a ]=> (x !-> n ; st), []
  | CFE_Seq : forall c1 c2 st st' st'' bs1 bs2,
      st  =[ c1 ]=> st', bs1  ->
      st' =[ c2 ]=> st'', bs2 ->
      st  =[ c1 ; c2 ]=> st'', (bs1++bs2)
  | CFE_IfTrue : forall st st' b c1 c2 bs1,
      beval st b = true ->
      st =[ c1 ]=> st', bs1 ->
      st =[ if b then c1 else c2 end]=> st', (true::bs1)
  | CFE_IfFalse : forall st st' b c1 c2 bs1,
      beval st b = false ->
      st =[ c2 ]=> st', bs1 ->
      st =[ if b then c1 else c2 end]=> st', (false::bs1)
  | CFE_While : forall b st st' os c, (* <- Nice trick: evaluate while to if+while *)
      st =[ if b then c; while b do c end else skip end ]=> st', os ->
      st =[ while b do c end ]=> st', os

  where "st =[ c ]=> st' , bs" := (cf_ceval c st st' bs).

Lemma cf_ceval_ceval : forall c st st' bs,
  st =[ c ]=> st', bs ->
  st =[ c ]=> st'.
Proof.
  intros c st st' bs H. induction H; try (econstructor; eassumption).
  - (* need to justify the while trick *)
    inversion IHcf_ceval.
    + inversion H6. subst. eapply E_WhileTrue; eauto.
    + subst. invert H6. eapply E_WhileFalse; eauto.
Qed.

(* ================================================================= *)
(** ** Control Flow security definition *)

(** Using the instrumented semantics we define Control Flow (CF) security: *)

Definition cf_secure L c := forall s1 s2 s1' s2' bs1 bs2,
  pub_equiv L s1 s2 ->
  s1 =[ c ]=> s1', bs1 ->
  s2 =[ c ]=> s2', bs2 ->
  bs1 = bs2.

(** CF security is mostly orthogonal to noninterference and
    instead of relating the final states it requires the branches of
    the program to be independent of secrets. *)

(* ================================================================= *)
(** ** Control Flow security proof *)

(** Our restrictive [cf_well_typed] relation enforces both
    noninterference (as we already proved at the beginning of the
    chapter) and CF security, as shown below: *)

Theorem cf_well_typed_cf_secure : forall L c,
  L |-cf- c ->
  cf_secure L c.
Proof.
  intros L c Hwt s1 s2 s1' s2' bs1 bs2 Heq Heval1 Heval2.
  generalize dependent s2'. generalize dependent s2.
  generalize dependent bs2.
  induction Heval1; intros bs2' s2 Heq s2' Heval2;
    inversion Heval2; inversion Hwt; subst.
  - reflexivity.
  - reflexivity.
  - destruct (IHHeval1_1 H8 bs0 s2 Heq st'0 H1).
    (* the proof does rely on noninterference for the sequencing case *)
    assert (Heq': pub_equiv L st' st'0).
    { eapply cf_ceval_ceval in Heval1_1.
      eapply cf_ceval_ceval in H1.
      eapply cf_well_typed_noninterferent with (c:=c1); eauto. }
    erewrite IHHeval1_2; eauto.
  - f_equal. eapply IHHeval1; try eassumption.
  - rewrite (noninterferent_bexp Heq H11) in H.
    rewrite H in H6. discriminate H6.
  - rewrite (noninterferent_bexp Heq H11) in H.
    rewrite H in H6. discriminate H6.
  - f_equal. eapply IHHeval1; eassumption.
  - eapply IHHeval1; try eassumption. repeat constructor; eassumption.
Qed.

(** Similarly to our previous equitermination proof, this proof relies
    on typing implying noninterference, since otherwise the induction
    doesn't go through for the sequencing case (and indirectly for the
    while case too, since in our instrumented semantics while
    evaluates to one loop unrolling sequenced with the rest of the loop). *)

(** Finally, it is worth noting that control flow security forms the
    foundation on which we will define cryptographic constant time in
    the [SpecCT] chapter. *)

(** This diagram summarizes the type systems from this chapter, the
    strength relations between them, and the semantic security notions
    they enforce. Even stronger (so at the top) is cryptographic
    constant time, which we will see next in the [SpecCT] chapter.

       typing               |          semantic security
                            |        state         observations
   -------------------------+--------------------------------------
                            |
    cct_well_typed  --------|-------------------->  cct_secure
        :                   |                           :
        v                   |                           v
    cf_well_typed  ---------|-------------------->  cf_secure
        |                   |
        v                   |
    ts_well_typed  ---------|------>   tsni
        |                   |           |
        v                   |           v
    ni_well_typed  ---------|------>  noninterferent
*)

(** **** Exercise: 4 stars, standard (cf_well_typed_ts_cf_secure) *)

(** We can also define a stronger, termination-sensitive version of
    control flow security: *)

Definition ts_cf_secure L c := forall s1 s2 s1' bs1,
  pub_equiv L s1 s2 ->
  s1 =[ c ]=> s1', bs1 ->
  exists s2', s2 =[ c ]=> s2', bs1.

(** In this exercise, you have to prove that [cf_well_typed] also
    implies [ts_cf_secure]. The while case should actually be quite
    easy, if you exploit how we reduced evaluation of while to
    sequencing and [if-then-else] in rule [CFE_While] above. *)

Theorem cf_well_typed_ts_cf_secure : forall L c,
  L |-cf- c ->
  ts_cf_secure L c.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ################################################################# *)
(** * Exercise: Adding public outputs *)

Module OUTPUT.

(** **** Exercise: 5 stars, standard (public_outputs) *)

(** Imp, the simple imperative language we have considered so far, doesn't
    have an output operation. In practice, however, programs often
    need to produce publicly-observable outputs. In this exercise, we
    extend our language with an output command and introduce an
    additional security property to be enforced for such programs. *)

Definition outputs := list nat.

Inductive com : Type :=
  | Skip
  | Asgn (x : string) (a : aexp)
  | Seq (c1 c2 : com)
  | If (b : bexp) (c1 c2 : com)
  | While (b : bexp) (c : com)
  | Output (a: aexp). (* <-- NEW *)

Open Scope com_scope.

Notation "'skip'"  :=
  Skip (in custom com at level 0) : com_scope.
Notation "x := y"  :=
  (Asgn x y)
    (in custom com at level 0, x constr at level 0,
      y custom com at level 85, no associativity) : com_scope.
Notation "x ; y" :=
  (Seq x y)
    (in custom com at level 90, right associativity) : com_scope.
Notation "'if' x 'then' y 'else' z 'end'" :=
  (If x y z)
    (in custom com at level 89, x custom com at level 99,
     y at level 99, z at level 99) : com_scope.
Notation "'while' x 'do' y 'end'" :=
  (While x y)
    (in custom com at level 89, x custom com at level 99, y at level 99) : com_scope.

Notation "'output' x" :=
  (Output x)
    (in custom com at level 89, x at level 99) : com_scope.

Check <{ skip }>.
Check <{ output 42 }>.

Reserved Notation
         "st '=[' c ']=>' st' , os"
         (at level 40, c custom com at level 99,
          st constr, st' constr at next level).

(** We modify the command evaluation to explicitly track outputs.
    Instead of the previous evaluation relation [st =[ c ]=> st'], we
    now use the [st =[ c ]=> st', os] relation below, where [os]
    represents the sequence of outputs produced during evaluation. *)

Inductive oceval : com -> state -> state -> outputs -> Prop :=
  | OE_Skip : forall st,
      st =[ skip ]=> st, []
  | OE_Asgn  : forall st a n x,
      aeval st a = n ->
      st =[ x := a ]=> (x !-> n ; st), []
  | OE_Seq : forall c1 c2 st st' st'' os1 os2,
      st  =[ c1 ]=> st', os1  ->
      st' =[ c2 ]=> st'', os2 ->
      st  =[ c1 ; c2 ]=> st'', (os1++os2)
  | OE_If : forall st st' b c1 c2 os, (* <- Trick: one rule for both if branches *)
      let c := if (beval st b) then c1 else c2 in
      st =[ c ]=> st', os ->
      st =[ if b then c1 else c2 end]=> st', os
  | OE_While : forall b st st' os c, (* <- Trick: evaluate while to if+while *)
      st =[ if b then c; while b do c end else skip end ]=> st', os ->
      st =[ while b do c end ]=> st', os
  | OE_Output : forall st a n, (* <-- NEW *)
      aeval st a = n ->
      st =[ output a ]=> st, [n]
  where "st =[ c ]=> st' , os" := (oceval c st st' os).

(** The original noninterference definition, which only compares final
    states, does not guarantee security of the publicly-observable outputs.

    Although [output_insecure_com1] and [output_insecure_com2] below obviously leak
    secrets through their outputs, they still satisfy noninterference. *)

Definition noninterferent L c := forall s1 s2 s1' os1 s2' os2,
  pub_equiv L s1 s2 ->
  s1 =[ c ]=> s1', os1 ->
  s2 =[ c ]=> s2', os2 ->
  pub_equiv L s1' s2'.

Definition output_insecure_com1 : com :=
  <{ output Y }>.

Lemma noninterferent_output_insecure_com1 :
  noninterferent LXP output_insecure_com1.
Proof.
  unfold noninterferent. intros.
  invert H0. invert H1. auto.
Qed.

Definition output_insecure_com2 : com :=
  <{ if Y=0 then (output 1) else skip end }>.

Lemma noninterferent_output_insecure_com2 :
  noninterferent LXP output_insecure_com2.
Proof.
  unfold noninterferent. intros.
  invert H0. invert H1. simpl in *.
  destruct (s1 Y), (s2 Y);
  simpl in *; subst c c0; invert H8; invert H7; auto.
Qed.

(** We define an output security property inspired by control flow
    security. Instead of relating final states like noninterference,
    we require that a program's outputs be independent of secrets. *)

Definition output_secure L c := forall s1 s2 s1' os1 s2' os2,
  pub_equiv L s1 s2 ->
  s1 =[ c ]=> s1', os1 ->
  s2 =[ c ]=> s2', os2 ->
  os1 = os2.

(** This property disallows programs whose outputs depend on secrets: *)

Lemma output_insecure_output_insecure_com1 :
  ~ output_secure LXP output_insecure_com1.
Proof.
  unfold output_secure, output_insecure_com1.
  intro Hc.

  set (s1 := Y !-> 0).
  set (s2 := Y !-> 1).

  specialize (Hc s1 s2).

  assert (PEQUIV: pub_equiv LXP s1 s2).
  { clear Hc. intros x H. apply LXP_public in H. subst. reflexivity. }

  specialize (Hc s1 [0] s2 [1] PEQUIV). subst s1 s2.

  assert (Hcontra: [0] = [1]).
  { eapply Hc; econstructor; simpl; auto. }

  discriminate Hcontra.
Qed.

Lemma output_insecure_output_insecure_com2 :
  ~ output_secure LXP output_insecure_com2.
Proof.
  unfold output_secure, output_insecure_com2.
  intro Hc.

  set (s1 := Y !-> 0).
  set (s2 := Y !-> 1).

  specialize (Hc s1 s2).

  assert (PEQUIV: pub_equiv LXP s1 s2).
  { clear Hc. intros x H. apply LXP_public in H. subst. reflexivity. }

  specialize (Hc s1 [1] s2 [] PEQUIV). subst s1 s2.

  assert (Hcontra: [1] = []).
  { eapply Hc.
    - repeat econstructor; simpl; auto.
    - eapply OE_If; simpl; auto. econstructor. }

  discriminate Hcontra.
Qed.

(** In the following tasks, you will define a type system enforcing
    both noninterference and output security. Then, you will write a
    type-checker and prove that it is sound and complete with respect
    to the type system. Finally, you will prove that your type system
    implies both noninterference and output security.

    All lemmas and theorems marked as [Admitted] provide partial
    credit, even if you cannot prove everything. *)

Reserved Notation "L ';;' pc '|-ni-' c" (at level 40).

Inductive oni_well_typed (L:label_map) : label -> com -> Prop :=
  | ONIWT_Com : forall pc,
      L ;; pc |-ni- <{ skip }>
  | ONIWT_Asgn : forall pc X a la,
      L |-a- a \in la ->
      can_flow (join pc la) (L X) = true ->
      L ;; pc |-ni- <{ X := a }>
  | ONIWT_Seq : forall pc c1 c2,
      L ;; pc |-ni- c1 ->
      L ;; pc |-ni- c2 ->
      L ;; pc |-ni- <{ c1 ; c2 }>
  | ONIWT_If : forall pc b l c1 c2,
      L |-b- b \in l ->
      L ;; (join pc l) |-ni- c1 ->
      L ;; (join pc l) |-ni- c2 ->
      L ;; pc |-ni- <{ if b then c1 else c2 end }>
  | ONIWT_While : forall pc b l c1,
      L |-b- b \in l ->
      L ;; (join pc l) |-ni- c1 ->
      L ;; pc |-ni- <{ while b do c1 end }>
  (* FILL IN HERE *)
      (* <--- Add your new typing rule for output here *)

where "L ';;' pc '|-ni-' c" := (oni_well_typed L pc c).

Fixpoint oni_type_checker (L:label_map) (pc:label) (c:com) : bool :=
  match c with
  | <{ skip }> => true
  | <{ X := a }> => can_flow (join pc (label_of_aexp L a)) (L X)
  | <{ c1 ; c2 }> => oni_type_checker L pc c1 && oni_type_checker L pc c2
  | <{ if b then c1 else c2 end }> =>
      oni_type_checker L (join pc (label_of_bexp L b)) c1 &&
      oni_type_checker L (join pc (label_of_bexp L b)) c2
  | <{ while b do c1 end }> =>
      oni_type_checker L (join pc (label_of_bexp L b)) c1
  (* FILL IN HERE *)
   | _ => false (* <--- Add your new type-checking code for output here *)
    end.

Lemma oni_type_checker_sound : forall L pc c,
  oni_type_checker L pc c = true ->
  L ;; pc |-ni- c.
Proof.
  intros L pc c. generalize dependent pc.
  induction c; intros pc H; simpl in *; try econstructor;
    try repeat rewrite andb_true_iff in *;
    try destruct H; try tauto;
    eauto using label_of_aexp_sound, label_of_bexp_sound.
  (* FILL IN HERE *) Admitted.

Lemma oni_type_checker_complete : forall L pc c,
  oni_type_checker L pc c = false ->
  ~(L ;; pc |-ni- c).
Proof.
  intros L pc c H Hc. induction Hc; simpl in *;
    try rewrite andb_false_iff in *; try tauto; try congruence.
  - apply label_of_aexp_unique in H0.
    rewrite H0 in *. congruence.
  - destruct H; apply label_of_bexp_unique in H0; subst; eauto.
  - apply label_of_bexp_unique in H0. subst. auto.
  (* FILL IN HERE *) Admitted.

Example not_ni_wt_output1 :
  ~(LXP ;; public |-ni- output_insecure_com1).
Proof.
  (* FILL IN HERE *) Admitted.

Example not_ni_wt_output2 :
  ~(LXP ;; public |-ni- output_insecure_com2).
Proof.
  (* FILL IN HERE *) Admitted.

(** The noninterference proof follows the same structure as for [ni_well_typed]: *)

Lemma secret_run : forall L c s s' os,
  L;; secret |-ni- c ->
  s =[ c ]=> s', os ->
  pub_equiv L s s'.
Proof.
  intros L c s s' os Hwt Heval. induction Heval; inversion Hwt;
    subst; eauto using pub_equiv_trans, pub_equiv_refl.
  - (* assignment case: crucial for preventing implicit flows *)
    apply pub_equiv_update_secret_r.
    + apply pub_equiv_refl.
    + (* the type system prevents public variables from being assigned *)
      rewrite join_secret_l in H4. apply negb_true_iff. apply H4.
  - simpl in *. destruct (beval st b); eapply IHHeval; eauto.
  - rewrite join_secret_l in H3.
    eapply IHHeval. econstructor; eauto; simpl; econstructor; eauto.
Qed.

Corollary different_code : forall L c1 c2 s1 s2 s1' s2' os1 os2,
  L;; secret |-ni- c1 ->
  L;; secret |-ni- c2 ->
  pub_equiv L s1 s2 ->
  s1 =[ c1 ]=> s1', os1 ->
  s2 =[ c2 ]=> s2', os2 ->
  pub_equiv L s1' s2'.
Proof.
  intros L c1 c2 s1 s2 s1' s2' os1 os2 Hwt1 Hwt2 Hequiv Heval1 Heval2.
  eapply secret_run in Hwt1; [| eassumption].
  eapply secret_run in Hwt2; [| eassumption].
  apply pub_equiv_sym in Hwt1.
  eapply pub_equiv_trans; try eassumption.
  eapply pub_equiv_trans; eassumption.
Qed.

Theorem oni_well_typed_noninterferent : forall L pc c,
  L;; pc |-ni- c ->
  noninterferent L c.
Proof.
  intros L pc c Hwt s1 s2 s1' os1 s2' os2 Heq Heval1 Heval2.
  generalize dependent s2'. generalize dependent os2. generalize dependent s2.
  generalize dependent pc.
  induction Heval1; intros pc Hwt s2 Heq os2' s2' Heval2; invert Heval2; auto.
  - (* Asgn *) invert Hwt.
    apply orb_true_iff in H3. destruct H3 as [Hl | Hx].
    + (* l = public: both sides assign the same value to x *)
      apply join_public in Hl. destruct Hl as [_ Hl]. subst.
      rewrite (noninterferent_aexp Heq H2).
      apply pub_equiv_update_same. assumption.
    + (* L x = secret: the assigned values don't matter *)
      apply negb_true_iff in Hx.
      apply pub_equiv_update_secret; assumption.
  - (* Seq *) invert Hwt. eapply IHHeval1_2; try eassumption.
    eapply IHHeval1_1; eassumption.
  (* We defined rules OE_If and OE_While so that the remaining cases
     shouldn't be too hard (our proof has 15 lines for these cases) *)
  (* FILL IN HERE *) Admitted.

(** To prove [output_secure] you can use a similar corollary to
    [different_code], but about the outputs: *)

Lemma secret_run_no_output : forall L c s s' os,
  L;; secret |-ni- c ->
  s =[ c ]=> s', os ->
  os = [].
Proof.
  (* FILL IN HERE *) Admitted.

Corollary different_code_no_output : forall L c1 c2 s1 s2 s1' s2' os1 os2,
  L;; secret |-ni- c1 ->
  L;; secret |-ni- c2 ->
  pub_equiv L s1 s2 ->
  s1 =[ c1 ]=> s1', os1 ->
  s2 =[ c2 ]=> s2', os2 ->
  os1 = os2.
Proof.
  intros L c1 c2 s1 s2 s1' s2' os1 os2 Hwt1 Hwt2 Hequiv Heval1 Heval2.
  eapply secret_run_no_output in Hwt1; [| eassumption].
  eapply secret_run_no_output in Hwt2; [| eassumption].
  subst. auto.
Qed.

Theorem oni_well_typed_output_secure : forall L pc c,
  L;; pc |-ni- c ->
  output_secure L c.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

End OUTPUT.

(* 2026-07-15 18:25 *)
