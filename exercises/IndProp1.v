(** * IndProp1: Inductively Defined Propositions - part 1 *)

Set Warnings "-notation-overridden".
From LF Require Export Logic.

(* ################################################################# *)
(** * Inductively Defined Propositions *)

(** In the [Logic] chapter, we looked at several ways of writing
    propositions, including conjunction, disjunction, and existential
    quantification.

    In this chapter, we bring yet another new tool into the mix:
    _inductively defined propositions_.

    To begin, some examples... *)

(* ================================================================= *)
(** ** Example: The Collatz Conjecture *)

(** The _Collatz Conjecture_ is a famous open problem in number
    theory.

    Its statement is quite simple.  First, we define a function [csf]
    on numbers, as follows (where [csf] stands for "Collatz step function"): *)

Fixpoint div2 (n : nat) : nat :=
  match n with
    0 => 0
  | 1 => 0
  | S (S n) => S (div2 n)
  end.

Definition csf (n : nat) : nat :=
  if even n then div2 n
  else (3 * n) + 1.

(** Next, we look at what happens when we repeatedly apply [csf] to
    some given starting number.  For example, [csf 12] is [6], and
    [csf 6] is [3], so by repeatedly applying [csf] we get the
    sequence [12, 6, 3, 10, 5, 16, 8, 4, 2, 1].

    Similarly, if we start with [19], we get the longer sequence [19,
    58, 29, 88, 44, 22, 11, 34, 17, 52, 26, 13, 40, 20, 10, 5, 16, 8,
    4, 2, 1].

    Both of these sequences eventually reach [1].  The question posed
    by Collatz was: Is the sequence starting from _any_ positive
    natural number guaranteed to reach [1] eventually? *)

(** To formalize this question in Rocq, we might try to define a
    recursive _function_ that calculates the total number of steps
    that it takes for such a sequence to reach [1]. *)

Fail Fixpoint reaches1_in (n : nat) : nat :=
  if n =? 1 then 0
  else 1 + reaches1_in (csf n).

(** You can write this definition in a standard programming language.
    This definition is, however, rejected by Rocq's termination
    checker, since the argument to the recursive call, [csf n], is not
    "obviously smaller" than [n].

    Indeed, this isn't just a pointless limitation: functions in Rocq
    are required to be total, to ensure logical consistency.

    Moreover, we can't fix it by devising a more clever termination
    checker: deciding whether this particular function is total
    would be equivalent to settling the Collatz conjecture! *)

(** Another idea could be to express the concept of "eventually
    reaches [1] in the Collatz sequence" as an _recursively defined
    property_ of numbers [Collatz_holds_for : nat -> Prop]. *)

Fail Fixpoint Collatz_holds_for (n : nat) : Prop :=
  match n with
  | 0 => False
  | 1 => True
  | _ => if even n then Collatz_holds_for (div2 n)
                   else Collatz_holds_for ((3 * n) + 1)
  end.

(** This recursive function is also rejected by the termination
    checker, since, while we could in principle convince Rocq that
    [div2 n] is smaller than [n], we certainly can't convince it that
    [(3 * n) + 1] is smaller than [n]! *)

(** Fortunately, there is another way to do it: We can express the
    concept "reaches [1] eventually in the Collatz sequence" as an
    _inductively defined property_ of numbers. Intuitively, this
    property is defined by a set of rules:

                  ------------------- (Chf_one)
                  Collatz_holds_for 1

     even n = true      Collatz_holds_for (div2 n)
     --------------------------------------------- (Chf_even)
                     Collatz_holds_for n

     even n = false    Collatz_holds_for ((3 * n) + 1)
     ------------------------------------------------- (Chf_odd)
                    Collatz_holds_for n

    So there are three ways to prove that a number [n] eventually
    reaches 1 in the Collatz sequence:
        - [n] is 1;
        - [n] is even and [div2 n] eventually reaches 1;
        - [n] is odd and [(3 * n) + 1] eventually reaches 1.
*)
(** We can prove that a number reaches 1 by constructing a (finite)
    derivation using these rules. For instance, here is the derivation
    proving that 12 reaches 1 (where we left out the evenness/oddness
    premises):

                    ———————————————————— (Chf_one)
                    Collatz_holds_for 1
                    ———————————————————— (Chf_even)
                    Collatz_holds_for 2
                    ———————————————————— (Chf_even)
                    Collatz_holds_for 4
                    ———————————————————— (Chf_even)
                    Collatz_holds_for 8
                    ———————————————————— (Chf_even)
                    Collatz_holds_for 16
                    ———————————————————— (Chf_odd)
                    Collatz_holds_for 5
                    ———————————————————— (Chf_even)
                    Collatz_holds_for 10
                    ———————————————————— (Chf_odd)
                    Collatz_holds_for 3
                    ———————————————————— (Chf_even)
                    Collatz_holds_for 6
                    ———————————————————— (Chf_even)
                    Collatz_holds_for 12
*)

(** Formally in Rocq, the [Collatz_holds_for] property is
    _inductively defined_: *)

Inductive Collatz_holds_for : nat -> Prop :=
  | Chf_one : Collatz_holds_for 1
  | Chf_even (n : nat) : even n = true ->
                         Collatz_holds_for (div2 n) ->
                         Collatz_holds_for n
  | Chf_odd (n : nat) :  even n = false ->
                         Collatz_holds_for ((3 * n) + 1) ->
                         Collatz_holds_for n.

(** What we've done here is to use Rocq's [Inductive] definition
    mechanism to characterize the property "Collatz holds for..." by
    stating three different ways in which it can hold: (1) Collatz
    holds for [1], (2) if Collatz holds for [div2 n] and [n] is even
    then Collatz holds for [n], and (3) if Collatz holds for [(3 * n)
    + 1] and [n] is odd then Collatz holds for [n]. This Rocq definition
    directly corresponds to the three rules we wrote informally above. *)

(** For particular numbers, we can now prove that the Collatz sequence
    reaches [1] (we'll look more closely at how it works a bit later
    in the chapter): *)

Example Collatz_holds_for_12 : Collatz_holds_for 12.
Proof.
  apply Chf_even. reflexivity. simpl.
  apply Chf_even. reflexivity. simpl.
  apply Chf_odd. reflexivity. simpl.
  apply Chf_even. reflexivity. simpl.
  apply Chf_odd. reflexivity. simpl.
  apply Chf_even. reflexivity. simpl.
  apply Chf_even. reflexivity. simpl.
  apply Chf_even. reflexivity. simpl.
  apply Chf_even. reflexivity. simpl.
  apply Chf_one.
Qed.

(** The Collatz conjecture then states that the sequence beginning
    from _any_ positive number reaches [1]: *)

Conjecture collatz : forall n, n <> 0 -> Collatz_holds_for n.

(** If you succeed in proving this conjecture, you've got a bright
    future as a number theorist!  But don't spend too long on it --
    it's been open since 1937. *)

(* ================================================================= *)
(** ** Example: Binary relation for comparing numbers *)

(** A binary _relation_ on a set [X] has Rocq type [X -> X -> Prop].
    This is a family of propositions parameterized by two elements of
    [X] -- i.e., a proposition about pairs of elements of [X]. *)

(** For example, one familiar binary relation on [nat] is [le : nat ->
    nat -> Prop], the less-than-or-equal-to relation, which can be
    inductively defined by the following two rules: *)

(**

                           ------ (le_n)
                           le n n

                           le n m
                         ---------- (le_S)
                         le n (S m)
*)
(** These rules say that there are two ways to show that a
    number is less than or equal to another: either observe that they
    are the same number, or, if the second has the form [S m], give
    evidence that the first is less than or equal to [m]. *)

(** This corresponds to the following inductive definition in Rocq: *)

Module LePlayground.

Inductive le : nat -> nat -> Prop :=
  | le_n (n : nat)   : le n n
  | le_S (n m : nat) : le n m -> le n (S m).

Notation "n <= m" := (le n m) (at level 70).

(** This definition is a bit simpler and more elegant than the Boolean function
    [leb] we defined in [Basics]. As usual, [le] and [leb] are
    equivalent, and there is an exercise about that later. *)

Example le_3_5 : 3 <= 5.
Proof.
  apply le_S. apply le_S. apply le_n. Qed.

End LePlayground.

(* ================================================================= *)
(** ** Example: Transitive Closure *)

(** Another example: The _transitive closure_ of a relation [R] is the smallest
    relation that contains [R] and that is transitive. This can be defined by
    the following two rules:

                     R x y
                ---------------- (t_step)
                clos_trans R x y

       clos_trans R x y    clos_trans R y z
       ------------------------------------ (t_trans)
                clos_trans R x z

    In Rocq this looks as follows:
*)

Inductive clos_trans {X: Type} (R: X->X->Prop) : X->X->Prop :=
  | t_step (x y : X) :
      R x y ->
      clos_trans R x y
  | t_trans (x y z : X) :
      clos_trans R x y ->
      clos_trans R y z ->
      clos_trans R x z.

(** For example, suppose we define a "parent of" relation on a group
    of people... *)

Inductive Person : Type := Sage | Cleo | Ridley | Moss.

Inductive parent_of : Person -> Person -> Prop :=
  po_SC : parent_of Sage Cleo
| po_SR : parent_of Sage Ridley
| po_CM : parent_of Cleo Moss.

(** In this example, [Sage] is a parent of both [Cleo] and
    [Ridley]; and [Cleo] is a parent of [Moss]. *)

(** The [parent_of] relation is not transitive, but we can define
   an "ancestor of" relation as its transitive closure: *)

Definition ancestor_of : Person -> Person -> Prop :=
  clos_trans parent_of.

(** Here is a derivation showing that Sage is an ancestor of Moss:

 ———————————————————(po_SC)     ———————————————————(po_CM)
 parent_of Sage Cleo            parent_of Cleo Moss
—————————————————————(t_step)  —————————————————————(t_step)
ancestor_of Sage Cleo          ancestor_of Cleo Moss
————————————————————————————————————————————————————(t_trans)
                ancestor_of Sage Moss
*)

Example ancestor_of_ex : ancestor_of Sage Moss.
Proof.
  unfold ancestor_of. apply t_trans with Cleo.
  - apply t_step. apply po_SC.
  - apply t_step. apply po_CM. Qed.

(** Computing the transitive closure can be undecidable even for
    a relation R that is decidable (e.g., the [cms] relation below), so in
    general we can't expect to define transitive closure as a boolean
    function. Fortunately, Rocq allows us to define transitive closure
    as an inductive relation.

    The transitive closure of a binary relation cannot, in general, be
    expressed in first-order logic. The logic of Rocq is, however, much
    more powerful, and can easily define such inductive relations. *)

(* ================================================================= *)
(** ** Example: Reflexive and Transitive Closure *)

(** As another example, the _reflexive and transitive closure_
    of a relation [R] is the
    smallest relation that contains [R] and that is reflexive and
    transitive. This can be defined by the following three rules
    (where we added a reflexivity rule to [clos_trans]):

                        R x y
                --------------------- (rt_step)
                clos_refl_trans R x y

                --------------------- (rt_refl)
                clos_refl_trans R x x

     clos_refl_trans R x y    clos_refl_trans R y z
     ---------------------------------------------- (rt_trans)
                clos_refl_trans R x z
*)

Inductive clos_refl_trans {X: Type} (R: X->X->Prop) : X->X->Prop :=
  | rt_step (x y : X) :
      R x y ->
      clos_refl_trans R x y
  | rt_refl (x : X) :
      clos_refl_trans R x x
  | rt_trans (x y z : X) :
      clos_refl_trans R x y ->
      clos_refl_trans R y z ->
      clos_refl_trans R x z.

(** For instance, this enables an equivalent definition of the Collatz
    conjecture.  First we define a binary relation corresponding to
    the "Collatz step function" [csf]: *)

Definition cs (n m : nat) : Prop := csf n = m.

(** This Collatz step relation can be used in conjunction with the
    reflexive and transitive closure operation to define a _Collatz
    multi-step_ ([cms]) relation, expressing that a number [n]
    reaches another number [m] in zero or more Collatz steps: *)

Definition cms n m := clos_refl_trans cs n m.
Conjecture collatz' : forall n, n <> 0 -> cms n 1.

(** This [cms] relation defined in terms of
    [clos_refl_trans] allows for more interesting derivations than the
    linear ones of the directly-defined [Collatz_holds_for] relation:

csf 16 = 8         csf 8 = 4         csf 4 = 2         csf 2 = 1
————————(rt_step)  ———————(rt_step)  ———————(rt_step)  ———————(rt_step)
cms 16 8           cms 8 4           cms 4 2           cms 2 1
—————————————————————————(rt_trans)  ————————————————————————(rt_trans)
        cms 16 4                              cms 4 1
        —————————————————————————————————————————————(rt_trans)
                           cms 16 1
*)

(** **** Exercise: 1 star, standard, optional (clos_refl_trans_sym)

    How would you modify the [clos_refl_trans] definition above so as
    to define the reflexive, symmetric, and transitive closure? *)

(* FILL IN HERE

    [] *)

(* ================================================================= *)
(** ** Example: Permutations *)

(** The familiar mathematical concept of _permutation_ also has an
    elegant formulation as an inductive relation.  For simplicity,
    let's focus on permutations of lists with exactly three
    elements.

    We can define such permulations by the following rules:

               --------------------- (perm3_swap12)
               Perm3 [a;b;c] [b;a;c]

               --------------------- (perm3_swap23)
               Perm3 [a;b;c] [a;c;b]

            Perm3 l1 l2       Perm3 l2 l3
            ----------------------------- (perm3_trans)
                     Perm3 l1 l3

    For instance we can derive [Perm3 [1;2;3] [3;2;1]] as follows:

    ————————(perm_swap12)  —————————————————————(perm_swap23)
    Perm3 [1;2;3] [2;1;3]  Perm3 [2;1;3] [2;3;1]
    ——————————————————————————————(perm_trans)  ————————————(perm_swap12)
        Perm3 [1;2;3] [2;3;1]                   Perm [2;3;1] [3;2;1]
        —————————————————————————————————————————————————————(perm_trans)
                          Perm3 [1;2;3] [3;2;1]
*)

(** This definition says:
      - If [l2] can be obtained from [l1] by swapping the first and
        second elements, then [l2] is a permutation of [l1].
      - If [l2] can be obtained from [l1] by swapping the second and
        third elements, then [l2] is a permutation of [l1].
      - If [l2] is a permutation of [l1] and [l3] is a permutation of
        [l2], then [l3] is a permutation of [l1]. *)

(** In Rocq [Perm3] is given the following inductive definition: *)

Inductive Perm3 {X : Type} : list X -> list X -> Prop :=
  | perm3_swap12 (a b c : X) :
      Perm3 [a;b;c] [b;a;c]
  | perm3_swap23 (a b c : X) :
      Perm3 [a;b;c] [a;c;b]
  | perm3_trans (l1 l2 l3 : list X) :
      Perm3 l1 l2 -> Perm3 l2 l3 -> Perm3 l1 l3.

(** **** Exercise: 1 star, standard, optional (perm)

    According to this definition, is [[1;2;3]] a permutation of
    itself? *)

(* FILL IN HERE

    [] *)

(* ================================================================= *)
(** ** Example: Evenness (yet again) *)

(** We've already seen two ways of stating a proposition that a number
    [n] is even: We can say

      (1) [even n = true] (using the recursive boolean function [even]), or

      (2) [exists k, n = double k] (using an existential quantifier). *)

(** A third possibility, which we'll use as a simple running example
    in this chapter, is to say that a number is even if we can
    _establish_ its evenness from the following two rules:

                          ---- (ev_0)
                          ev 0

                          ev n
                      ------------ (ev_SS)
                      ev (S (S n))
*)

(** Intuitively these rules say that:
       - The number [0] is even.
       - If [n] is even, then [S (S n)] is even. *)

(** (Defining evenness in this way may seem a bit confusing,
    since we have already seen two perfectly good ways of doing
    it. It makes a convenient running example because it is
    simple and compact, but we will soon return to the more compelling
    examples above.) *)

(** To illustrate how this new definition of evenness works, let's
    imagine using it to show that [4] is even:

                           ———— (ev_0)
                           ev 0
                       ———————————— (ev_SS)
                       ev (S (S 0))
                   ———————————————————— (ev_SS)
                   ev (S (S (S (S 0))))
*)

(** In words, to show that [4] is even, by rule [ev_SS], it
   suffices to show that [2] is even. This, in turn, is again
   guaranteed by rule [ev_SS], as long as we can show that [0] is
   even. But this last fact follows directly from the [ev_0] rule. *)

(** We can translate the informal definition of evenness from above
    into a formal [Inductive] declaration, where each "way that a
    number can be even" corresponds to a separate constructor: *)

Inductive ev : nat -> Prop :=
  | ev_0                       : ev 0
  | ev_SS (n : nat) (H : ev n) : ev (S (S n)).

(** Such definitions are interestingly different from previous uses of
    [Inductive] for defining inductive datatypes like [nat] or [list].
    For one thing, we are defining not a [Type] (like [nat]) or a
    function yielding a [Type] (like [list]), but rather a function
    from [nat] to [Prop] -- that is, a property of numbers. But what
    is really new is that, because the [nat] argument of [ev] appears
    to the _right_ of the colon on the first line, it is allowed to
    take _different_ values in the types of different constructors:
    [0] in the type of [ev_0] and [S (S n)] in the type of [ev_SS].
    Accordingly, the type of each constructor must be specified
    explicitly (after a colon), and each constructor's type must have
    the form [ev n] for some natural number [n].

    In contrast, recall the definition of [list]:

    Inductive list (X:Type) : Type :=
      | nil
      | cons (x : X) (l : list X).

    or (equivalently but more explicitly):

    Inductive list (X:Type) : Type :=
      | nil                       : list X
      | cons (x : X) (l : list X) : list X.

   This definition introduces the [X] parameter _globally_, to the
   _left_ of the colon, forcing the result of [nil] and [cons] to be
   the same type (i.e., [list X]).  But if we had tried to bring [nat]
   to the left of the colon in defining [ev], we would have seen an
   error: *)

Fail Inductive wrong_ev (n : nat) : Prop :=
  | wrong_ev_0 : wrong_ev 0
  | wrong_ev_SS (H: wrong_ev n) : wrong_ev (S (S n)).
(* ===> Error: Last occurrence of "[wrong_ev]" must have "[n]" as 1st
        argument in "[wrong_ev 0]". *)

(** In an [Inductive] definition, an argument to the type constructor
    on the left of the colon is called a "parameter", whereas an
    argument on the right is called an "index" or "annotation."

    For example, in [Inductive list (X : Type) := ...], the [X] is a
    parameter, while in [Inductive ev : nat -> Prop := ...], the
    unnamed [nat] argument is an index. *)

(** We can think of the inductive definition of [ev] as defining a
    Rocq property [ev : nat -> Prop], together with two "evidence
    constructors": *)

Check ev_0 : ev 0.
Check ev_SS : forall (n : nat), ev n -> ev (S (S n)).

(** Indeed, Rocq also accepts the following equivalent definition of [ev]: *)

Module EvPlayground.

Inductive ev : nat -> Prop :=
  | ev_0  : ev 0
  | ev_SS : forall (n : nat), ev n -> ev (S (S n)).

End EvPlayground.

(** These evidence constructors can be thought of as "primitive
    evidence of evenness", and they can be used later on just like proven
    theorems.  In particular, we can use Rocq's [apply] tactic with the
    constructor names to obtain evidence for [ev] of particular
    numbers... *)

Theorem ev_4 : ev 4.
Proof. apply ev_SS. apply ev_SS. apply ev_0. Qed.

(** ... or we can use function application syntax to combine several
    constructors: *)

Theorem ev_4' : ev 4.
Proof. apply (ev_SS 2 (ev_SS 0 ev_0)). Qed.

(** In this way, we can also prove theorems that have hypotheses
    involving [ev]. *)

Theorem ev_plus4 : forall n, ev n -> ev (4 + n).
Proof.
  intros n. simpl. intros Hn.  apply ev_SS. apply ev_SS. apply Hn.
Qed.

(** **** Exercise: 1 star, standard (ev_double) *)
Theorem ev_double : forall n,
  ev (double n).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ================================================================= *)
(** ** Constructing Evidence for Permutations *)

(** Similarly we can apply the evidence constructors to obtain
    evidence of [Perm3 [1;2;3] [3;2;1]]: *)

Lemma Perm3_rev : Perm3 [1;2;3] [3;2;1].
Proof.
  apply perm3_trans with (l2:=[2;3;1]).
  - apply perm3_trans with (l2:=[2;1;3]).
    + apply perm3_swap12.
    + apply perm3_swap23.
  - apply perm3_swap12.
Qed.

(** And again we can equivalently use function application syntax to
    combine several constructors. (Note that the Rocq type checker can
    infer not only types, but also nats and lists, when they are clear
    from the context.) *)

Lemma Perm3_rev' : Perm3 [1;2;3] [3;2;1].
Proof.
  apply (perm3_trans _ [2;3;1] _
          (perm3_trans _ [2;1;3] _
            (perm3_swap12 _ _ _)
            (perm3_swap23 _ _ _))
          (perm3_swap12 _ _ _)).
Qed.

(** So the informal derivation trees we drew above are not too far
    from what's happening formally.  Formally we're using the evidence
    constructors to build _evidence trees_, similar to the finite trees we
    built using the constructors of data types such as nat, list,
    binary trees, etc. *)

(** **** Exercise: 1 star, standard (Perm3) *)
Lemma Perm3_ex1 : Perm3 [1;2;3] [2;3;1].
Proof.
  (* FILL IN HERE *) Admitted.

Lemma Perm3_refl : forall (X : Type) (a b c : X),
  Perm3 [a;b;c] [a;b;c].
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ################################################################# *)
(** * Using Evidence in Proofs *)

(** Besides _constructing_ evidence that numbers are even, we can also
    _destruct_ such evidence, reasoning about how it could have been
    built.

    Defining [ev] with an [Inductive] declaration tells Rocq not
    only that the constructors [ev_0] and [ev_SS] are valid ways to
    build evidence that some number is [ev], but also that these two
    constructors are the _only_ ways to build evidence that numbers
    are [ev]. *)

(** In other words, if someone gives us evidence [E] for the proposition
    [ev n], then we know that [E] must be one of two things:

      - [E = ev_0] and [n = O], or
      - [E = ev_SS n' E'] and [n = S (S n')], where [E'] is
        evidence for [ev n']. *)

(** This suggests that it should be possible to analyze a
    hypothesis of the form [ev n] much as we do inductively defined
    data structures; in particular, it should be possible to argue either by
    _case analysis_ or by _induction_ on such evidence.  Let's look at a
    few examples to see what this means in practice. *)

(* ================================================================= *)
(** ** Destructing and Inverting Evidence *)

(** Suppose we are proving some fact involving a number [n], and
    we are given [ev n] as a hypothesis.  We already know how to
    perform case analysis on [n] using [destruct] or [induction],
    generating separate subgoals for the case where [n = O] and the
    case where [n = S n'] for some [n'].  But for some proofs we may
    instead want to analyze the evidence for [ev n] _directly_.

    As a tool for such proofs, we can formalize the intuitive
    characterization that we gave above for evidence of [ev n], using
    [destruct]. *)

Lemma ev_inversion : forall (n : nat),
    ev n ->
    (n = 0) \/ (exists n', n = S (S n') /\ ev n').
Proof.
  intros n E.  destruct E as [ | n' E'] eqn:EE.
  - (* E = ev_0 : ev 0 *)
    left. reflexivity.
  - (* E = ev_SS n' E' : ev (S (S n')) *)
    right. exists n'. split. reflexivity. apply E'.
Qed.

(** Facts like this are often called "inversion lemmas" because they
    allow us to "invert" some given information to reason about all
    the different ways it could have been derived.

    Here there are two ways to prove [ev n], and the inversion
    lemma makes this explicit. *)

(** **** Exercise: 1 star, standard (le_inversion)

    Let's prove a similar inversion lemma for [le]. *)
Lemma le_inversion : forall (n m : nat),
  le n m ->
  (n = m) \/ (exists m', m = S m' /\ le n m').
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** We can use the inversion lemma that we proved above to help
    structure proofs: *)

Theorem evSS_ev : forall n, ev (S (S n)) -> ev n.
Proof.
  intros n E. apply ev_inversion in E. destruct E as [H0|H1].
  - discriminate H0.
  - destruct H1 as [n' [Hnn' E']]. injection Hnn' as Hnn'.
    rewrite Hnn'. apply E'.
Qed.

(** Note how the inversion lemma produces two subgoals, which
    correspond to the two ways of proving [ev].  The first subgoal is
    a contradiction that is discharged with [discriminate].  The
    second subgoal makes use of [injection] and [rewrite].

    Rocq provides a handy tactic called [inversion] that factors out
    this common pattern, saving us the trouble of explicitly stating
    and proving an inversion lemma for every [Inductive] definition we
    make.

    Here, the [inversion] tactic can detect (1) that the first case,
    where [n = 0], does not apply and (2) that the [n'] that appears
    in the [ev_SS] case must be the same as [n].  It includes an
    "[as]" annotation similar to [destruct], allowing us to assign
    names rather than have Rocq choose them. *)

Theorem evSS_ev' : forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros n E.  inversion E as [| n' E' Hnn'].
  (* We are in the [E = ev_SS n' E'] case now. *)
  apply E'.
Qed.

(** The [inversion] tactic can apply the principle of explosion to
    "obviously contradictory" hypotheses involving inductively defined
    properties, something that takes a bit more work using our
    inversion lemma. Compare: *)

Theorem one_not_even : ~ ev 1.
Proof.
  intros H. apply ev_inversion in H.  destruct H as [ | [m [Hm _]]].
  - discriminate H.
  - discriminate Hm.
Qed.

Theorem one_not_even' : ~ ev 1.
Proof. intros H. inversion H. Qed.

(** **** Exercise: 1 star, standard (inversion_practice)

    Prove the following result using [inversion].  (For extra
    practice, you can also prove it using the inversion lemma.) *)

Theorem SSSSev__even : forall n,
  ev (S (S (S (S n)))) -> ev n.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 1 star, standard (ev5_nonsense)

    Prove the following result using [inversion]. *)

Theorem ev5_nonsense :
  ev 5 -> 2 + 2 = 9.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** The [inversion] tactic does quite a bit of work. For
    example, when applied to an equality assumption, it does the work
    of both [discriminate] and [injection]. In addition, it carries
    out the [intros] and [rewrite]s that are typically necessary in
    the case of [injection]. It can also be applied to analyze
    evidence for arbitrary inductively defined propositions, not just
    equality.  As examples, we'll use it to re-prove some theorems
    from chapter [Tactics].  (Here we are being a bit lazy by
    omitting the [as] clause from [inversion], thereby asking Rocq to
    choose names for the variables and hypotheses that it introduces.) *)

Theorem inversion_ex1 : forall (n m o : nat),
  [n; m] = [o; o] -> [n] = [m].
Proof.
  intros n m o H. inversion H. reflexivity. Qed.

Theorem inversion_ex2 : forall (n : nat),
  S n = O -> 2 + 2 = 5.
Proof.
  intros n contra. inversion contra. Qed.

(** Here's how [inversion] works in general.
      - Suppose the name [H] refers to an assumption [P] in the
        current context, where [P] has been defined by an [Inductive]
        declaration.
      - Then, for each of the constructors of [P], [inversion H]
        generates a subgoal in which [H] has been replaced by the
        specific conditions under which this constructor could have
        been used to prove [P].
      - Some of these subgoals will be self-contradictory; [inversion]
        throws these away.
      - The ones that are left represent the cases that must be proved
        to establish the original goal.  For those, [inversion] adds
        to the proof context all equations that must hold of the
        arguments given to [P] -- e.g., [n' = n] in the proof of
        [evSS_ev]). *)

(** The [ev_double] exercise above allows us to easily show that
    our new notion of evenness is implied by the two earlier ones
    (since, by [even_bool_prop] in chapter [Logic], we already
    know that those are equivalent to each other). To show that all
    three coincide, we just need the following lemma. *)

Lemma ev_Even_firsttry : forall n,
  ev n -> Even n.
Proof.
  (* WORKED IN CLASS *) unfold Even. intros n E.

(** We start by instantiating the existential with [div2 n]: *)

  exists (div2 n).

(** We are left to prove that [n = double (div2 n)] knowing [E : ev n].

    We could try to proceed by case analysis or induction on [n].  But
    since [ev] is mentioned in [E], this strategy seems
    unpromising, because (as we've noted before) the induction
    hypothesis will talk about [n-1] (which is _not_ even!).  Thus, it
    seems better to first try [inversion] on the evidence [E].
    Indeed, the first case can be solved trivially. *)

  inversion E as [EQ' | n' E' EQ'].
  - (* E = ev_0 *) reflexivity.

  - (* E = ev_SS n' E' *)
    simpl. f_equal. f_equal.

(** Unfortunately, the second case is harder.  We need to show
    that [n' = double (div2 n')], but this is another instance
    of the fact about [double] and [div2] we were trying to prove
    before, just for [n'] instead of [n].

    We do have evidence [E' : ev n'], but what we are missing
    is an induction hypothesis corresponding to this evidence.

    So we are stuck! *)
Abort.

(* ================================================================= *)
(** ** Induction on Evidence *)

(** If this story feels familiar, it is no coincidence: We
    encountered similar problems in the [Induction] chapter, when
    trying to use case analysis to prove results that required
    induction.  And once again the solution is... induction! *)

(** The behavior of [induction] on evidence is the same as its
    behavior on data: It causes Rocq to generate one subgoal for each
    constructor that could have been used to build that evidence, while
    providing an induction hypothesis for each recursive occurrence of
    the property in question.

    To prove that a property of [n] holds for all even numbers (i.e.,
    those for which [ev n] holds), we can use induction on [ev
    n]. This requires us to prove two things, corresponding to the two
    ways in which [ev n] could have been constructed. If it was
    constructed by [ev_0], then [n=0] and the property must hold of
    [0]. If it was constructed by [ev_SS], then the evidence of [ev n]
    is of the form [ev_SS n' E'], where [n = S (S n')] and [E'] is
    evidence for [ev n']. In this case, the inductive hypothesis says
    that the property we are trying to prove holds for [n']. *)

(** Let's try proving that lemma again: *)

Lemma ev_Even : forall n,
  ev n -> Even n.
Proof.
  unfold Even. intros n E. exists (div2 n).
  induction E as [|n' E' IH].
  - (* E = ev_0 *)
    reflexivity.
  - (* E = ev_SS n' E',  with IH : n' = double (div2 n') *)
    simpl. f_equal. f_equal. apply IH.
Qed.

(** Here, we can see that Rocq produced an [IH] that corresponds
    to [E'], the single recursive occurrence of [ev] in its own
    definition.  Since [E'] mentions [n'], the induction hypothesis
    talks about [n'], as opposed to [n] or some other number. *)

(** The equivalence between the second and third definitions of
    evenness now follows. *)

Theorem ev_Even_iff : forall n,
  ev n <-> Even n.
Proof.
  intros n. split.
  - (* -> *) apply ev_Even.
  - (* <- *) unfold Even. intros [k Hk]. rewrite Hk. apply ev_double.
Qed.

(** As we will see in later chapters, induction on evidence is a
    recurring technique across many areas -- in particular for
    formalizing the semantics of programming languages. *)

(** The following exercises provide simpler examples of this
    technique, to help you familiarize yourself with it. *)

(** **** Exercise: 2 stars, standard (ev_sum) *)
Theorem ev_sum : forall n m, ev n -> ev m -> ev (n + m).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, advanced, especially useful (ev_ev__ev) *)
Theorem ev_ev__ev : forall n m,
  ev (n+m) -> ev n -> ev m.
  (* Hint: There are two pieces of evidence you could attempt to induct upon
      here. If one doesn't work, try the other. *)
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, standard, optional (ev_plus_plus)

    This exercise can be completed without induction or case analysis.
    But, you will need a clever assertion and some tedious rewriting.
    Hint: Is [(n+m) + (n+p)] even? *)

Theorem ev_plus_plus : forall n m p,
  ev (n+m) -> ev (n+p) -> ev (m+p).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ================================================================= *)
(** ** Multiple Induction Hypotheses *)

(** Recall the definition of the reflexive, transitive, closure of a
    relation: *)

Module clos_refl_trans_remainder.
Inductive clos_refl_trans {X: Type} (R: X->X->Prop) : X->X->Prop :=
  | rt_step (x y : X) :
      R x y ->
      clos_refl_trans R x y
  | rt_refl (x : X) :
      clos_refl_trans R x x
  | rt_trans (x y z : X) :
      clos_refl_trans R x y ->
      clos_refl_trans R y z ->
      clos_refl_trans R x z.
End clos_refl_trans_remainder.

(** Let's say that a relation on a type [X] is _diagonal_ if it
    refines the identity relation -- i.e., if [R x y] implies [x = y]. *)

Definition isDiagonal {X : Type} (R: X -> X -> Prop) :=
  forall x y, R x y -> x = y.

(** Now consider the following lemma about diagonal relations: *)

Lemma closure_of_diagonal_is_diagonal: forall X (R: X -> X -> Prop),
  isDiagonal R ->
  isDiagonal (clos_refl_trans R).
Proof.
  intros X R IsDiag x y H.
  induction H as [ x y H | x | x y z H IH H' IH' ].
  (* The two first cases go as you'd expect... *)
  - specialize (IsDiag x y H). rewrite -> IsDiag. reflexivity.
  - reflexivity.
  - (* ...  but something interesting happens here: there are two
       induction hypotheses, [IH] and [IH']! If you think about it, it
       is not that weird: we are in the case [srt_trans], which has
       two recursive components, [H], relating [x] to [y] and [H'],
       relating [y] to [z]. Hence we may want (and will actually need)
       an induction hypothesis for [H] and one for [H'] -- they are
       called [IH] and [IH'] here. In general, Rocq will always
       generate one induction hypothesis per recursive constructor of
       the type being inducted over. *)
   rewrite -> IH, <- IH'. reflexivity.
Qed.

(** **** Exercise: 4 stars, advanced, optional (ev'_ev)

    In general, there may be multiple ways of defining a
    property inductively.  For example, here's a (slightly contrived)
    alternative definition for [ev]: *)

Inductive ev' : nat -> Prop :=
  | ev'_0 : ev' 0
  | ev'_2 : ev' 2
  | ev'_sum n m (Hn : ev' n) (Hm : ev' m) : ev' (n + m).

(** Prove that this definition is logically equivalent to the old one.
    To streamline the proof, use the technique (from the [Logic]
    chapter) of applying theorems to arguments, and note that the same
    technique works with constructors of inductively defined
    propositions. *)

Theorem ev'_ev : forall n, ev' n <-> ev n.
Proof.
 (* FILL IN HERE *) Admitted.
(** [] *)

(** We can do similar inductive proofs on the [Perm3] relation,
    which we defined earlier as follows: *)

Module Perm3Reminder.

Inductive Perm3 {X : Type} : list X -> list X -> Prop :=
  | perm3_swap12 (a b c : X) :
      Perm3 [a;b;c] [b;a;c]
  | perm3_swap23 (a b c : X) :
      Perm3 [a;b;c] [a;c;b]
  | perm3_trans (l1 l2 l3 : list X) :
      Perm3 l1 l2 -> Perm3 l2 l3 -> Perm3 l1 l3.

End Perm3Reminder.

Lemma Perm3_symm : forall (X : Type) (l1 l2 : list X),
  Perm3 l1 l2 -> Perm3 l2 l1.
Proof.
  intros X l1 l2 E.
  induction E as [a b c | a b c | l1 l2 l3 E12 IH12 E23 IH23].
  - apply perm3_swap12.
  - apply perm3_swap23.
  - apply (perm3_trans _ l2 _).
    * apply IH23.
    * apply IH12.
Qed.

(** **** Exercise: 2 stars, standard (Perm3_In) *)
Lemma Perm3_In : forall (X : Type) (x : X) (l1 l2 : list X),
    Perm3 l1 l2 -> In x l1 -> In x l2.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 1 star, standard, optional (Perm3_NotIn) *)
Lemma Perm3_NotIn : forall (X : Type) (x : X) (l1 l2 : list X),
    Perm3 l1 l2 -> ~In x l1 -> ~In x l2.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (NotPerm3)

    Proving that something is NOT a permutation is quite tricky. Some
    of the lemmas above, like [Perm3_In] can be useful for this. *)
Example Perm3_example2 : ~ Perm3 [1;2;3] [1;2;4].
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ################################################################# *)
(** * Exercising with Inductive Relations *)

(** A proposition parameterized by a number (such as [ev])
    can be thought of as a _property_ -- i.e., it defines
    a subset of [nat], namely those numbers for which the proposition
    is provable.  In the same way, a two-argument proposition can be
    thought of as a _relation_ -- i.e., it defines a set of pairs for
    which the proposition is provable. *)

Module Playground.

(** Just like properties, relations can be defined inductively.  One
    useful example is the "less than or equal to" relation on numbers
    that we briefly saw above. *)

Inductive le : nat -> nat -> Prop :=
  | le_n (n : nat)                : le n n
  | le_S (n m : nat) (H : le n m) : le n (S m).

Notation "n <= m" := (le n m).

(** (We've written the definition a bit differently this time,
    giving explicit names to the arguments to the constructors and
    moving them to the left of the colons.) *)

(** Proofs of facts about [<=] using the constructors [le_n] and
    [le_S] follow the same patterns as proofs about properties, like
    [ev] above. We can [apply] the constructors to prove [<=]
    goals (e.g., to show that [3<=3] or [3<=6]), and we can use
    tactics like [inversion] to extract information from [<=]
    hypotheses in the context (e.g., to prove that [(2 <= 1) ->
    2+2=5].) *)

(** Here are some sanity checks on the definition.  (Notice that,
    although these are the same kind of simple "unit tests" as we gave
    for the testing functions we wrote in the first few lectures, we
    must construct their proofs explicitly -- [simpl] and
    [reflexivity] don't do the job, because the proofs aren't just a
    matter of simplifying computations.) *)

Theorem test_le1 :
  3 <= 3.
Proof.
  (* WORKED IN CLASS *)
  apply le_n.  Qed.

Theorem test_le2 :
  3 <= 6.
Proof.
  (* WORKED IN CLASS *)
  apply le_S. apply le_S. apply le_S. apply le_n.  Qed.

Theorem test_le3 :
  (2 <= 1) -> 2 + 2 = 5.
Proof.
  (* WORKED IN CLASS *)
  intros H. inversion H. inversion H2.  Qed.

(** The "strictly less than" relation [n < m] can now be defined
    in terms of [le]. *)

Definition lt (n m : nat) := le (S n) m.

Notation "n < m" := (lt n m).

(** The [>=] operation is defined in terms of [<=]. *)

Definition ge (m n : nat) : Prop := le n m.
Notation "m >= n" := (ge m n).

End Playground.

(** From the definition of [le], we can sketch the behaviors of
    [destruct], [inversion], and [induction] on a hypothesis [H]
    providing evidence of the form [le e1 e2].  Doing [destruct H]
    will generate two cases. In the first case, [e1 = e2], and it
    will replace instances of [e2] with [e1] in the goal and context.
    In the second case, [e2 = S n'] for some [n'] for which [le e1 n']
    holds, and it will replace instances of [e2] with [S n'].
    Doing [inversion H] will remove impossible cases and add generated
    equalities to the context for further use. Doing [induction H]
    will, in the second case, add the induction hypothesis that the
    goal holds when [e2] is replaced with [n']. *)

(** Here are a number of facts about the [<=] and [<] relations that
    we are going to need later in the course.  The proofs make good
    practice exercises. *)

(** **** Exercise: 3 stars, standard, especially useful (le_facts) *)
Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem O_le_n : forall n,
  0 <= n.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem n_le_m__Sn_le_Sm : forall n m,
  n <= m -> S n <= S m.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem le_plus_l : forall a b,
  a <= a + b.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard, especially useful (plus_le_facts1) *)

Theorem plus_le : forall n1 n2 m,
  n1 + n2 <= m ->
  n1 <= m /\ n2 <= m.
Proof.
 (* FILL IN HERE *) Admitted.

Theorem plus_le_cases : forall n m p q,
  n + m <= p + q -> n <= p \/ m <= q.
  (** Hint: May be easiest to prove by induction on [n]. *)
Proof.
(* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard, especially useful (plus_le_facts2) *)

Theorem plus_le_compat_l : forall n m p,
  n <= m ->
  p + n <= p + m.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem plus_le_compat_r : forall n m p,
  n <= m ->
  n + p <= m + p.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem le_plus_trans : forall n m p,
  n <= m ->
  n <= m + p.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, standard, optional (lt_facts) *)
Theorem lt_ge_cases : forall n m,
  n < m \/ n >= m.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem n_lt_m__n_le_m : forall n m,
  n < m ->
  n <= m.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem plus_lt : forall n1 n2 m,
  n1 + n2 < m ->
  n1 < m /\ n2 < m.
Proof.
(* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 4 stars, standard, optional (leb_le) *)
Theorem leb_sound : forall n m,
  n <=? m = true -> n <= m.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem leb_complete : forall n m,
  n <= m ->
  n <=? m = true.
Proof.
  (* FILL IN HERE *) Admitted.

(** Hint: The next two can easily be proved without using [induction]. *)

Theorem leb_iff : forall n m,
  n <=? m = true <-> n <= m.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem leb_true_trans : forall n m o,
  n <=? m = true -> m <=? o = true -> n <=? o = true.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

Module R.

(** **** Exercise: 3 stars, standard, especially useful (R_provability)

    We can define three-place relations, four-place relations,
    etc., in just the same way as binary relations.  For example,
    consider the following three-place relation on numbers: *)

Inductive R : nat -> nat -> nat -> Prop :=
  | c1                                     : R 0     0     0
  | c2 m n o (H : R m     n     o        ) : R (S m) n     (S o)
  | c3 m n o (H : R m     n     o        ) : R m     (S n) (S o)
  | c4 m n o (H : R (S m) (S n) (S (S o))) : R m     n     o
  | c5 m n o (H : R m     n     o        ) : R n     m     o.

(** - Which of the following propositions are provable?
      - [R 1 1 2]
      - [R 2 2 6]

    - If we dropped constructor [c5] from the definition of [R],
      would the set of provable propositions change?  Briefly (1
      sentence) explain your answer.

    - If we dropped constructor [c4] from the definition of [R],
      would the set of provable propositions change?  Briefly (1
      sentence) explain your answer. *)

(* FILL IN HERE *)

(* Do not modify the following line: *)
Definition manual_grade_for_R_provability : option (nat*string) := None.
(** [] *)

(** **** Exercise: 3 stars, standard, optional (R_fact)

    The relation [R] above actually encodes a familiar function.
    Figure out which function; then state and prove this equivalence
    in Rocq. *)

Definition fR : nat -> nat -> nat
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Theorem R_equiv_fR : forall m n o, R m n o <-> fR m n = o.
Proof.
(* FILL IN HERE *) Admitted.
(** [] *)

End R.

(** **** Exercise: 4 stars, advanced (subsequence)

    A list is a _subsequence_ of another list if all of the elements
    in the first list occur in the same order in the second list,
    possibly with some extra elements in between. For example,

      [1;2;3]

    is a subsequence of each of the lists

      [1;2;3]
      [1;1;1;2;2;3]
      [1;2;7;3]
      [5;6;1;9;9;2;7;3;8]

    but it is _not_ a subsequence of any of the lists

      [1;2]
      [1;3]
      [5;6;2;1;7;3;8].

    - Define an inductive proposition [subseq] on [list nat] that
      captures what it means to be a subsequence.  There are a number
      of correct ways to do this. You should make sure that your
      definition behaves correctly on all the positive and negative
      examples above, but you do not need to prove this formally.

    - Prove [subseq_refl] that subsequence is reflexive, that is,
      any list is a subsequence of itself.

    - Prove [subseq_app] that for any lists [l1], [l2], and [l3],
      if [l1] is a subsequence of [l2], then [l1] is also a subsequence
      of [l2 ++ l3].

    - (Harder) Prove [subseq_trans] that subsequence is transitive --
      that is, if [l1] is a subsequence of [l2] and [l2] is a
      subsequence of [l3], then [l1] is a subsequence of [l3]. *)

Inductive subseq : list nat -> list nat -> Prop :=
(* FILL IN HERE *)
.

Theorem subseq_refl : forall (l : list nat), subseq l l.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem subseq_app : forall (l1 l2 l3 : list nat),
  subseq l1 l2 ->
  subseq l1 (l2 ++ l3).
Proof.
  (* FILL IN HERE *) Admitted.

Theorem subseq_trans : forall (l1 l2 l3 : list nat),
  subseq l1 l2 ->
  subseq l2 l3 ->
  subseq l1 l3.
Proof.
  (* Hint: be careful about what you are doing induction on and which
     other things need to be generalized... *)
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (R_provability2)

    Suppose we give Rocq the following definition:

    Inductive R : nat -> list nat -> Prop :=
      | c1                    : R 0     []
      | c2 n l (H: R n     l) : R (S n) (n :: l)
      | c3 n l (H: R (S n) l) : R n     l.

    Which of the following propositions are provable?

    - [R 2 [1;0]]
    - [R 1 [1;2;1;0]]
    - [R 6 [3;2;1;0]]  *)

(* FILL IN HERE

    [] *)

(** **** Exercise: 2 stars, standard, optional (total_relation)

    Define an inductive binary relation [total_relation] that holds
    between every pair of natural numbers. *)

Inductive total_relation : nat -> nat -> Prop :=
  (* FILL IN HERE *)
.

Theorem total_relation_is_total : forall n m, total_relation n m.
  Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (empty_relation)

    Define an inductive binary relation [empty_relation] (on numbers)
    that never holds. *)

Inductive empty_relation : nat -> nat -> Prop :=
  (* FILL IN HERE *)
.

Theorem empty_relation_is_empty : forall n m, ~ empty_relation n m.
  Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ################################################################# *)
(** * Case Study: Regular Expressions *)

(** Many of the examples above were simple and -- in the case of
    the [ev] property -- even a bit artificial. To give a better sense
    of the power of inductively defined propositions, we now show how
    to use them to model a classic concept in computer science:
    _regular expressions_. *)

(* ================================================================= *)
(** ** Definitions *)

(** Regular expressions are a natural language for describing sets of
    strings.  Their syntax is defined as follows: *)

Inductive reg_exp (T : Type) : Type :=
  | EmptySet
  | EmptyStr
  | Char (t : T)
  | App (r1 r2 : reg_exp T)
  | Union (r1 r2 : reg_exp T)
  | Star (r : reg_exp T).

Arguments EmptySet {T}.
Arguments EmptyStr {T}.
Arguments Char {T} _.
Arguments App {T} _ _.
Arguments Union {T} _ _.
Arguments Star {T} _.

(** Note that this definition is _polymorphic_: Regular
    expressions in [reg_exp T] describe strings with characters drawn
    from [T] -- which in this exercise we represent as _lists_ with
    elements from [T]. *)

(** (Technical aside: We depart slightly from standard practice in
    that we do not require the type [T] to be finite.  This results in
    a somewhat different theory of regular expressions, but the
    difference is not significant for present purposes.) *)

(** We connect regular expressions and strings by defining when a
    regular expression _matches_ some string.

    Informally this looks as follows:

      - The regular expression [EmptySet] does not match any string.

      - [EmptyStr] matches the empty string [[]].

      - [Char x] matches the one-character string [[x]].

      - If [re1] matches [s1], and [re2] matches [s2],
        then [App re1 re2] matches [s1 ++ s2].

      - If at least one of [re1] and [re2] matches [s],
        then [Union re1 re2] matches [s].

      - Finally, if we can write some string [s] as the concatenation
        of a sequence of strings [s = s_1 ++ ... ++ s_k], and the
        expression [re] matches each one of the strings [s_i],
        then [Star re] matches [s].

        In particular, the sequence of strings may be empty, so
        [Star re] always matches the empty string [[]] no matter what
        [re] is. *)

(** We can easily translate this intuition into a set of rules,
    where we write [s =~ re] to say that [re] matches [s]:

                        -------------- (MEmpty)
                        [] =~ EmptyStr

                        --------------- (MChar)
                        [x] =~ (Char x)

                    s1 =~ re1     s2 =~ re2
                  --------------------------- (MApp)
                  (s1 ++ s2) =~ (App re1 re2)

                           s1 =~ re1
                     --------------------- (MUnionL)
                     s1 =~ (Union re1 re2)

                           s2 =~ re2
                     --------------------- (MUnionR)
                     s2 =~ (Union re1 re2)

                        --------------- (MStar0)
                        [] =~ (Star re)

                           s1 =~ re
                        s2 =~ (Star re)
                    ----------------------- (MStarApp)
                    (s1 ++ s2) =~ (Star re)
*)

(** This directly corresponds to the following [Inductive] definition.
    We use the notation [s =~ re] in  place of [exp_match s re].
    (By "reserving" the notation before defining the [Inductive],
    we can use it in the definition.) *)

Reserved Notation "s =~ re" (at level 80).

Inductive exp_match {T} : list T -> reg_exp T -> Prop :=
  | MEmpty : [] =~ EmptyStr
  | MChar x : [x] =~ (Char x)
  | MApp s1 re1 s2 re2
             (H1 : s1 =~ re1)
             (H2 : s2 =~ re2)
           : (s1 ++ s2) =~ (App re1 re2)
  | MUnionL s1 re1 re2
                (H1 : s1 =~ re1)
              : s1 =~ (Union re1 re2)
  | MUnionR s2 re1 re2
                (H2 : s2 =~ re2)
              : s2 =~ (Union re1 re2)
  | MStar0 re : [] =~ (Star re)
  | MStarApp s1 s2 re
                 (H1 : s1 =~ re)
                 (H2 : s2 =~ (Star re))
               : (s1 ++ s2) =~ (Star re)

  where "s =~ re" := (exp_match s re).

(** Notice that these rules are not _quite_ the same as the
    intuition that we gave at the beginning of the section. First, we
    don't need to include a rule explicitly stating that no string is
    matched by [EmptySet]; indeed, the syntax of inductive definitions
    doesn't even _allow_ us to give such a "negative rule." We just
    don't happen to include any rule that would have the effect of
    [EmptySet] matching some string.

    Second, the intuition we gave for [Union] and [Star] correspond
    to two constructors each: [MUnionL] / [MUnionR], and [MStar0] /
    [MStarApp].  The result is logically equivalent to the original
    intuition but more convenient to use in Rocq, since the recursive
    occurrences of [exp_match] are given as direct arguments to the
    constructors, making it easier to perform induction on evidence.
    (The [exp_match_ex1] and [exp_match_ex2] exercises below ask you
    to prove that the constructors given in the inductive declaration
    and the ones that would arise from a more literal transcription of
    the intuition is indeed equivalent.)

    Let's illustrate these rules with a few examples. *)

(* ================================================================= *)
(** ** Examples *)

Example reg_exp_ex1 : [1] =~ Char 1.
Proof.
  apply MChar.
Qed.

Example reg_exp_ex2 : [1; 2] =~ App (Char 1) (Char 2).
Proof.
  apply (MApp [1]).
  - apply MChar.
  - apply MChar.
Qed.

(** (Notice how the last example applies [MApp] to the string
    [[1]] directly.  Since the goal mentions [[1; 2]] instead of
    [[1] ++ [2]], Rocq wouldn't be able to figure out how to split
    the string on its own.)

    Using [inversion], we can also show that certain strings do _not_
    match a regular expression: *)

Example reg_exp_ex3 : ~ ([1; 2] =~ Char 1).
Proof.
  intros H. inversion H.
Qed.

(** We can define helper functions for writing down regular
    expressions. The [reg_exp_of_list] function constructs a regular
    expression that matches exactly the string that it receives as an
    argument: *)

Fixpoint reg_exp_of_list {T} (l : list T) :=
  match l with
  | [] => EmptyStr
  | x :: l' => App (Char x) (reg_exp_of_list l')
  end.

Example reg_exp_ex4 : [1; 2; 3] =~ reg_exp_of_list [1; 2; 3].
Proof.
  simpl. apply (MApp [1]).
  { apply MChar. }
  apply (MApp [2]).
  { apply MChar. }
  apply (MApp [3]).
  { apply MChar. }
  apply MEmpty.
Qed.

(** We can also prove general facts about [exp_match].  For instance,
    the following lemma shows that every string [s] matched by [re]
    is also matched by [Star re]. *)

Lemma MStar1 :
  forall T s (re : reg_exp T) ,
    s =~ re ->
    s =~ Star re.
Proof.
  intros T s re H.
  rewrite <- (app_nil_r _ s).
  apply MStarApp.
  - apply H.
  - apply MStar0.
Qed.

(** (Note the use of [app_nil_r] to change the goal of the theorem to
    exactly the shape expected by [MStarApp].) *)

(** **** Exercise: 3 stars, standard (exp_match_ex1)

    The following lemmas show that the intuition about matching given
    at the beginning of the chapter can be obtained from the formal
    inductive definition. *)

Lemma EmptySet_is_empty : forall T (s : list T),
  ~ (s =~ EmptySet).
Proof.
  (* FILL IN HERE *) Admitted.

Lemma MUnion' : forall T (s : list T) (re1 re2 : reg_exp T),
  s =~ re1 \/ s =~ re2 ->
  s =~ Union re1 re2.
Proof.
  (* FILL IN HERE *) Admitted.

(** The next lemma is stated in terms of the [fold] function from the
    [Poly] chapter: If [ss : list (list T)] represents a sequence of
    strings [s1, ..., sn], then [fold app ss []] is the result of
    concatenating them all together. *)

Lemma MStar' : forall T (ss : list (list T)) (re : reg_exp T),
  (forall s, In s ss -> s =~ re) ->
  fold app ss [] =~ Star re.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (EmptyStr_not_needed)

    It turns out that the [EmptyStr] constructor is actually not
   needed, since the regular expression matching the empty string can
   also be defined from [Star] and [EmptySet]: *)
Definition EmptyStr' {T:Type} := @Star T (EmptySet).

(** State and prove that this [EmptyStr'] definition matches exactly
   the same strings as the [EmptyStr] constructor. *)

(* FILL IN HERE

    [] *)

(* 2026-06-17 17:08 *)
