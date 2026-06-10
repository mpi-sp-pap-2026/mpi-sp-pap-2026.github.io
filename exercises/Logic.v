(** * Logic: Logic in Rocq - part 2 *)

Set Warnings "-notation-overridden".
Require Nat.
From LF Require Export Logic1.

(* ################################################################# *)
(** * Recap -- Logical connectives in Rocq *)

(** Here is a summary of the logical connectives in Rocq: *)

(** **** Basic connectives:
       - [and : Prop -> Prop -> Prop] (conjunction):
         - introduced with the [split] tactic
         - eliminated with [destruct H as [H1 H2]]
       - [or : Prop -> Prop -> Prop] (disjunction):
         - introduced with [left] and [right] tactics
         - eliminated with [destruct H as [H1 | H2]]
       - [False : Prop]
         - eliminated with [destruct H as []]
       - [True : Prop]
         - introduced with [apply I], but not as useful
       - [ex : forall A:Type, (A -> Prop) -> Prop] (existential)
         - introduced with [exists w]
         - eliminated with [destruct H as [x H]]
*)
(** **** Derived connectives:
       - [not : Prop -> Prop] (negation):
         - [not P] defined as [P -> False]
       - [iff : Prop -> Prop -> Prop] (logical equivalence):
         - [iff P Q] defined as [(P -> Q) /\ (Q -> P)]

    **** Fundamental connectives we've been using since the beginning:
       - equality ([e1 = e2])
       - implication ([P -> Q])
       - universal quantification ([forall x, P]) *)

(* ################################################################# *)
(** * Programming with Propositions *)

(** The logical connectives that we have seen provide a rich
    vocabulary for defining complex propositions from simpler ones.
    To illustrate, let's look at how to express the claim that an
    element [x] occurs in a list [l].  Notice that this property has a
    simple recursive structure:

       - If [l] is the empty list, then [x] cannot occur in it, so the
         property "[x] appears in [l]" is simply false.

       - Otherwise, [l] has the form [x' :: l'].  In this case, [x]
         occurs in [l] if it is equal to [x'] or it occurs in [l']. *)

(** We can translate this directly into a straightforward recursive
    function taking an element and a list and returning... a proposition! *)

Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
  match l with
  | [] => False
  | x' :: l' => x' = x \/ In x l'
  end.

(** When [In] is applied to a concrete list, it expands into a
    concrete sequence of nested disjunctions. *)

Example In_example_1 : In 4 [1; 2; 3; 4; 5].
Proof.
  (* WORKED IN CLASS *)
  simpl. right. right. right. left. reflexivity.
Qed.

Example In_example_2 :
  forall n, In n [2; 4] -> Even n.
Proof.
  (* WORKED IN CLASS *)
  intros n H. unfold Even. simpl in H.
  destruct H as [H | [H | []]].
  - rewrite <- H. exists 1. reflexivity.
  - rewrite <- H. exists 2. reflexivity.
Qed.
(** (Notice the use of the empty pattern to discharge the last case
    _en passant_.) *)

(** We can also reason about more generic statements involving [In]. *)

Theorem In_map :
  forall (A B : Type) (f : A -> B) (l : list A) (x : A),
         In x l ->
         In (f x) (map f l).
Proof.
  intros A B f l x H.
  induction l as [|x' l' IHl'].
  - (* l = nil, contradiction *)
    simpl. simpl in H. destruct H as [].
  - (* l = x' :: l' *)
    simpl. simpl in H. destruct H as [H | H].
    + rewrite H. left. reflexivity.
    + right. apply IHl'. apply H.
Qed.

(** (Note here how [In] starts out applied to a variable and only
    gets expanded when we do case analysis on this variable.) *)

(** This way of defining propositions recursively is very convenient in
    some cases, less so in others.  In particular, it is subject to Rocq's
    usual restrictions regarding definitions of recursive functions,
    e.g., the requirement that they be "obviously terminating."

    In the next chapter, we will see how to define propositions
    _inductively_ -- a different technique with its own strengths and
    limitations. *)

(** **** Exercise: 2 stars, standard (In_map_iff) *)
Theorem In_map_iff :
  forall (A B : Type) (f : A -> B) (l : list A) (y : B),
         In y (map f l) <->
         exists x, f x = y /\ In x l.
Proof.
  intros A B f l y. split.
  - induction l as [|x l' IHl'].
    (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard (In_app_iff) *)
Theorem In_app_iff : forall A l l' (a:A),
  In a (l++l') <-> In a l \/ In a l'.
Proof.
  intros A l. induction l as [|a' l' IH].
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, standard, especially useful (All)

    We noted above that functions returning propositions can be seen as
    _properties_ of their arguments. For instance, if [P] has type
    [nat -> Prop], then [P n] says that property [P] holds of [n].

    Drawing inspiration from [In], write a recursive function [All]
    stating that some property [P] holds of all elements of a list
    [l]. To make sure your definition is correct, prove the [All_In]
    lemma below.  (Of course, your definition should _not_ just
    restate the left-hand side of [All_In].) *)

Fixpoint All {T : Type} (P : T -> Prop) (l : list T) : Prop
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Theorem All_In :
  forall T (P : T -> Prop) (l : list T),
    (forall x, In x l -> P x) <->
    All P l.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (combine_odd_even)

    Complete the definition of [combine_odd_even] below.  It takes as
    arguments two properties of numbers, [Podd] and [Peven], and it should
    return a property [P] such that [P n] is equivalent to [Podd n] when
    [n] is [odd] and equivalent to [Peven n] otherwise. *)

Definition combine_odd_even (Podd Peven : nat -> Prop) : nat -> Prop
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

(** To test your definition, prove the following facts: *)

Theorem combine_odd_even_intro :
  forall (Podd Peven : nat -> Prop) (n : nat),
    (odd n = true -> Podd n) ->
    (odd n = false -> Peven n) ->
    combine_odd_even Podd Peven n.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem combine_odd_even_elim_odd :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    odd n = true ->
    Podd n.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem combine_odd_even_elim_even :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    odd n = false ->
    Peven n.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ################################################################# *)
(** * Applying Theorems to Arguments *)

(** One feature that distinguishes Rocq from some other popular proof
    assistants (e.g., ACL2 and Isabelle) is that it treats _proofs_ as
    first-class objects.

    There is a great deal to be said about this, but it is not necessary to
    understand it all in order to use Rocq.  This section gives just a
    taste, leaving a deeper exploration for the optional chapters
    [ProofObjects] and [IndPrinciples]. *)

(** We have seen that we can use [Check] to ask Rocq to check whether
    an expression has a given type: *)

Check plus : nat -> nat -> nat.
Check @rev : forall X, list X -> list X.

(** We can also use it to check what theorem a particular identifier
    refers to: *)

Check add_comm        : forall n m : nat, n + m = m + n.
Check plus_id_example : forall n m : nat, n = m -> n + n = m + m.

(** Rocq checks the _statements_ of the [add_comm] and
    [plus_id_example] theorems in the same way that it checks the
    _type_ of any term (e.g., plus). If we leave off the colon and
    type, Rocq will print these types for us.

    Why? *)

(** The reason is that the identifier [add_comm] actually refers to a
    _proof object_ -- a logical derivation establishing the truth of the
    statement [forall n m : nat, n + m = m + n].  The type of this object
    is the proposition that it is a proof of.

    The type of an ordinary function tells us what we can do with it.
       - If we have a term of type [nat -> nat -> nat], we can give it two
         [nat]s as arguments and get a [nat] back.

    Similarly, the statement of a theorem tells us what we can use that
    theorem for.
       - If we have a term of type [forall n m, n = m -> n + n = m + m] and we
         provide it two numbers [n] and [m] and a third "argument" of type
         [n = m], we get back a proof object of type [n + n = m + m]. *)

(** Operationally, this analogy goes even further: by applying a
    theorem as if it were a function, i.e., applying it to values and
    hypotheses with matching types, we can specialize its result
    without having to resort to intermediate assertions.  For example,
    suppose we wanted to prove the following result: *)

Lemma add_comm3 :
  forall x y z, x + (y + z) = (z + y) + x.

(** It appears at first sight that we ought to be able to prove this by
    rewriting with [add_comm] twice to make the two sides match.  The
    problem is that the second [rewrite] will undo the effect of the
    first. *)

Proof.
  intros x y z.
  rewrite add_comm.
  rewrite add_comm.
  (* We are back where we started... *)
Abort.

(** We encountered similar issues back in [Induction], and we saw
    one way to work around them by using [assert] to derive a specialized
    version of [add_comm] that can be used to rewrite exactly where we
    want. *)

Lemma add_comm3_take2 :
  forall x y z, x + (y + z) = (z + y) + x.
Proof.
  intros x y z.
  rewrite add_comm.
  assert (H : y + z = z + y).
    { rewrite add_comm. reflexivity. }
  rewrite H.
  reflexivity.
Qed.

(** A more elegant alternative is to apply [add_comm] directly
    to the arguments we want to instantiate it with, in much the same
    way as we apply a polymorphic function to a type argument. *)

Lemma add_comm3_take3 :
  forall x y z, x + (y + z) = (z + y) + x.
Proof.
  intros x y z.
  rewrite add_comm.
  rewrite (add_comm y z).
  reflexivity.
Qed.

(** If we really wanted, we could in fact do it for both rewrites. *)

Lemma add_comm3_take4 :
  forall x y z, x + (y + z) = (z + y) + x.
Proof.
  intros x y z.
  rewrite (add_comm x (y + z)).
  rewrite (add_comm y z).
  reflexivity.
Qed.

(** Here's another example of using a theorem about lists like
    a function.  Suppose we have proved the following simple fact
    about lists... *)

Theorem in_not_nil :
  forall A (x : A) (l : list A), In x l -> l <> [].
Proof.
  intros A x l H. unfold not. intro Hl.
  rewrite Hl in H.
  simpl in H.
  apply H.
Qed.

(** (I.e., if a list [l] contains some element [x], then [l]
    must be nonempty.) *)

(** Note that one quantified variable ([x]) does not appear in
    the conclusion ([l <> []]). *)

(** Intuitively, we should be able to use this theorem to prove the special
    case where [x] is [42]. However, simply invoking the tactic [apply
    in_not_nil] on the goal will fail because it cannot infer the value of [x]. *)

Lemma in_not_nil_42 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  Fail apply in_not_nil.
Abort.

(** There are several ways to work around this: *)

(** We can use [apply ... in ...] to do a forward proof instead: *)
Lemma in_not_nil_42_take2 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply in_not_nil in H.
  apply H.
Qed.

(** Or we can stick with a backward proof and use [apply ... with ...]: *)
Lemma in_not_nil_42_take3 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply in_not_nil with (x := 42).
  apply H.
Qed.

(** Or -- this is the new one -- we can explicitly
    apply the lemma to the value [42] for [x]: *)
Lemma in_not_nil_42_take4 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply (in_not_nil nat 42).
  apply H.
Qed.

(** We can also explicitly apply the lemma to a hypothesis,
    causing the values of the other parameters to be inferred: *)
Lemma in_not_nil_42_take5 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply (in_not_nil _ _ _ H).
Qed.

(** You can "use a theorem as a function" in this way with almost any
    tactic that can take a theorem's name as an argument.

    Note, also, that theorem application uses the same inference
    mechanisms as function application; thus, it is possible, for
    example, to supply wildcards as arguments to be inferred, or to
    declare some hypotheses to a theorem as implicit by default.
    These features are illustrated in the proof below. (The details of
    how this proof works are not critical -- the goal here is just to
    illustrate applying theorems to arguments.) *)

Example lemma_application_ex :
  forall {n : nat} {ns : list nat},
    In n (map (fun m => m * 0) ns) ->
    n = 0.
Proof.
  intros n ns H.
  destruct (proj1 _ _ (In_map_iff _ _ _ _ _) H)
           as [m [Hm _]].
  rewrite mul_0_r in Hm. rewrite <- Hm. reflexivity.
Qed.

(** We will see many more examples in later chapters. *)

(* ----------------------------------------------------------------- *)
(** *** The Curry-Howard Correspondence *)

(** This is an example of a deep connection between logic and
    typed, purely functional programming:

                 propositions are types!
*)
Check in_not_nil : forall A (x:A) (l:list A), In x l -> l <> [].
Check in_not_nil_42_take5 : forall l : list nat, In 42 l -> l <> [].

(** ... and there's more to it:

                 proofs are programs!
*)
Print in_not_nil_42_take5.
  (* fun (l : list nat) (H : In 42 l) => in_not_nil nat 42 l H *)

Definition in_not_nil_42_take6 := in_not_nil _ 42.
Check in_not_nil_42_take6 : forall l : list nat, In 42 l -> l <> [].

(** If this sounds interesting have a look at the optional chapter on
    [ProofObjects], where you can learn to write such proof objects for all
    of Rocq's logical connectives. *)

(* ################################################################# *)
(** * Working with Decidable Properties *)

(** We've seen two different ways of expressing logical claims in Rocq:
    with _booleans_ (of type [bool]), and with _propositions_ (of type
    [Prop]).

    Here are the key differences between [bool] and [Prop]:

                                           bool     Prop
                                           ====     ====
           decidable?                      yes       no
           useable with match?             yes       no
           works with rewrite tactic?      no        yes
*)

(** The crucial difference between the two worlds is _decidability_.
    Every (closed) Rocq expression of type [bool] can be simplified in a
    finite number of steps to either [true] or [false] -- i.e., there is a
    terminating mechanical procedure for deciding whether or not it is
    [true].

    This means that, for example, the type [nat -> bool] is inhabited only
    by functions that, given a [nat], always yield either [true] or [false]
    in finite time; and this, in turn, means (by a standard computability
    argument) that there is _no_ function in [nat -> bool] that checks
    whether a given number is the code of a terminating Turing machine.

    By contrast, the type [Prop] includes both decidable and undecidable
    mathematical propositions; in particular, the type [nat -> Prop] does
    contain functions representing properties like "the nth Turing machine
    halts."

    The second row in the table follows directly from this essential
    difference.  To evaluate a pattern match (or conditional) on a boolean,
    we need to know whether the scrutinee evaluates to [true] or [false];
    this only works for [bool], not [Prop].

    The third row highlights an important practical difference:
    equality functions like [eqb_nat] that return a boolean cannot be
    used directly to justify rewriting with the [rewrite] tactic;
    propositional equality is required for this. *)



(** Since [Prop] includes _both_ decidable and undecidable properties,
    when we want to formalize a property that happens to be decidable
    we have two options: we can express it as a boolean computation
    _or_ as a function into [Prop]. *)

Example even_42_bool : even 42 = true.
Proof. reflexivity. Qed.

(** ... or that there exists some [k] such that [n = double k]. *)
Example even_42_prop : Even 42.
Proof. unfold Even. exists 21. reflexivity. Qed.

(** Of course, it would be deeply strange if these two
    characterizations of evenness did not describe the same set of
    natural numbers!

    Fortunately, they do! *)

(** To prove this, we first need two helper lemmas. *)

Lemma even_double : forall k, even (double k) = true.
Proof.
  intros k. induction k as [|k' IHk'].
  - reflexivity.
  - simpl. apply IHk'.
Qed.

(** **** Exercise: 3 stars, standard (even_double_conv) *)
Lemma even_double_conv : forall n, exists k,
  n = if even n then double k else S (double k).
Proof.
  (* Hint: Use the [even_S] lemma from [Induction.v]. *)
  (* FILL IN HERE *) Admitted.
(** [] *)

(** Now the main theorem: *)

Theorem even_bool_prop : forall n,
  even n = true <-> Even n.
Proof.
  intros n. split.
  - intros H. destruct (even_double_conv n) as [k Hk].
    rewrite Hk. rewrite H. exists k. reflexivity.
  - intros [k Hk]. rewrite Hk. apply even_double.
Qed.

(** In view of this theorem, we can say that the boolean computation
    [even n] is _reflected_ in the truth of the proposition
    [exists k, n = double k]. *)

(** Similarly, to state that two numbers [n] and [m] are equal, we can
    say either
      - (1) that [n =? m] returns [true], or
      - (2) that [n = m].
    Again, these two notions are equivalent: *)

Theorem eqb_eq : forall n1 n2 : nat,
  n1 =? n2 = true <-> n1 = n2.
Proof.
  intros n1 n2. split.
  - apply eqb_true.
  - intros H. rewrite H. rewrite eqb_refl. reflexivity.
Qed.

(** So what should we do in situations where some claim could be
    formalized as either a proposition or a boolean computation? Which
    should we choose?

    In general, _both_ can be useful. *)

(** For example, booleans are more useful for defining computations.
    There is no effective way to _test_ whether or not a [Prop] is
    true, so we cannot use [Prop]s in conditional expressions. The
    following definition is rejected: *)

Fail
Definition is_even_prime n :=
  if n = 2 then true
  else false.

(** Rocq complains that [n = 2] has type [Prop], while it expects an
    element of [bool] (or some other inductive type with two constructors).
    This has to do with the _computational_ nature of Rocq's core language,
    which is designed so that every function it can express is computable
    and total. (One reason for this is to allow the extraction of
    executable programs from Rocq developments.) As a consequence, [Prop] in
    Rocq does _not_ have a universal case analysis operation telling whether
    any given proposition is true or false, since such an operation would
    allow us to write non-computable functions.  *)

(** Rather, we have to state this definition using a boolean equality
    test. *)

Definition is_even_prime n :=
  if n =? 2 then true
  else false.

(** Beyond the fact that non-computable properties are impossible in
    general to phrase as boolean computations, even many _computable_
    properties are easier to express using [Prop] than [bool], since
    recursive function definitions in Rocq are subject to significant
    restrictions.  For instance, the next chapter shows how to define the
    property that a regular expression matches a given string using [Prop].
    Doing the same with [bool] would amount to writing a regular expression
    matching algorithm, which would be more complicated, harder to
    understand, and harder to reason about than a simple (non-algorithmic)
    definition of this property.

    Conversely, an important side benefit of stating facts using booleans
    is enabling some proof automation through computation with Rocq terms, a
    technique known as _proof by reflection_.

    Consider the following statement: *)

Example even_1000 : Even 1000.

(** The most direct way to prove this is to give the value of [k]
    explicitly. *)

Proof. unfold Even. exists 500. reflexivity. Qed.

(** The proof of the corresponding boolean statement is simpler, because we
    don't have to invent the witness [500]: Rocq's computation mechanism
    does it for us! *)

Example even_1000' : even 1000 = true.
Proof. reflexivity. Qed.

(** Now, the useful observation is that, since the two notions are
    equivalent, we can use the boolean formulation to prove the other one
    without mentioning the value 500 explicitly: *)

Example even_1000'' : Even 1000.
Proof. apply even_bool_prop. reflexivity. Qed.

(** Although we haven't gained much in terms of proof-script
    line count in this case, larger proofs can often be made considerably
    simpler by the use of reflection.  As an extreme example, a famous
    Rocq proof of the even more famous _4-color theorem_ uses
    reflection to reduce the analysis of hundreds of different cases
    to a boolean computation. *)

(** Another advantage of booleans is that the _negation_ of a claim
    about booleans is straightforward to state and (when true) prove:
    simply flip the expected boolean result. *)

Example not_even_1001 : even 1001 = false.
Proof.
  reflexivity.
Qed.

(** In contrast, propositional negation can be difficult to work with
    directly.

    For example, suppose we state the non-evenness of [1001]
    propositionally: *)

Example not_even_1001' : ~(Even 1001).

(** Proving this directly -- by assuming that there is some [n] such that
    [1001 = double n] and then somehow reasoning to a contradiction --
    would be rather complicated.

    But if we convert it to a claim about the boolean [even] function, we
    can let Rocq do the work for us. *)

Proof.
  (* WORKED IN CLASS *)
  rewrite <- even_bool_prop.
  unfold not.
  simpl.
  intro H.
  discriminate H.
Qed.

(** Conversely, there are situations where it can be easier to work
    with propositions rather than booleans.

    In particular, knowing that [(n =? m) = true] is generally of
    little direct help in the middle of a proof involving [n] and [m].
    But if we convert the statement to the equivalent form [n = m],
    then we can easily [rewrite] with it. *)

Lemma plus_eqb_example : forall n m p : nat,
  n =? m = true -> n + p =? m + p = true.
Proof.
  (* WORKED IN CLASS *)
  intros n m p H.
  rewrite eqb_eq in H.
  rewrite H.
  rewrite eqb_eq.
  reflexivity.
Qed.

(** We won't discuss reflection any further for the moment, but
    it serves as a good example showing the different strengths of
    booleans and general propositions. *)

(** Being able to cross back and forth between the boolean and
    propositional worlds will often be convenient in later chapters. *)

(** **** Exercise: 2 stars, standard (logical_connectives)

    The following theorems relate the propositional connectives studied
    in this chapter to the corresponding boolean operations. *)

Theorem andb_true_iff : forall b1 b2:bool,
  b1 && b2 = true <-> b1 = true /\ b2 = true.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem orb_true_iff : forall b1 b2,
  b1 || b2 = true <-> b1 = true \/ b2 = true.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 1 star, standard (eqb_neq)

    The following theorem is an alternate "negative" formulation of
    [eqb_eq] that is more convenient in certain situations.  (We'll see
    examples in later chapters.)  Hint: [not_true_iff_false]. *)

Theorem eqb_neq : forall x y : nat,
  x =? y = false <-> x <> y.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, standard (eqb_list)

    Given a boolean operator [eqb] for testing equality of elements of
    some type [A], we can define a function [eqb_list] for testing
    equality of lists with elements in [A].  Complete the definition
    of the [eqb_list] function below.  To make sure that your
    definition is correct, prove the lemma [eqb_list_true_iff]. *)

Fixpoint eqb_list {A : Type} (eqb : A -> A -> bool)
                  (l1 l2 : list A) : bool
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Theorem eqb_list_true_iff :
  forall A (eqb : A -> A -> bool),
    (forall a1 a2, eqb a1 a2 = true <-> a1 = a2) ->
    forall l1 l2, eqb_list eqb l1 l2 = true <-> l1 = l2.
Proof.
(* FILL IN HERE *) Admitted.

(** [] *)

(** **** Exercise: 2 stars, standard, especially useful (All_forallb)

    Prove the theorem below, which relates [forallb], from the
    exercise [forall_exists_challenge] in chapter [Tactics], to
    the [All] property defined above. *)

(** Copy the definition of [forallb] from your [Tactics] here
    so that this file can be graded on its own. *)
Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Theorem forallb_true_iff : forall X test (l : list X),
  forallb test l = true <-> All (fun x => test x = true) l.
Proof.
  (* FILL IN HERE *) Admitted.

(** (Ungraded thought question) Are there any important properties of
    the function [forallb] which are not captured by this
    specification? *)

(* FILL IN HERE

    [] *)

(* ################################################################# *)
(** * The Logic of Rocq *)

(** Rocq's logical core, the _Calculus of Inductive
    Constructions_, differs in some important ways from other formal
    systems that are used by mathematicians to write down precise and
    rigorous definitions and proofs -- in particular from
    Zermelo-Fraenkel Set Theory (ZFC), the most popular foundation for
    paper-and-pencil mathematics.

    We conclude this chapter with a brief discussion of some of the
    most significant differences between these two worlds. *)

(* ================================================================= *)
(** ** Functional Extensionality *)

(** Rocq's logic is quite minimalistic.  This means that one occasionally
    encounters cases where translating standard mathematical reasoning into
    Rocq is cumbersome -- or even impossible -- unless we enrich its core
    logic with additional axioms. *)

(** For example, the equality assertions that we have seen so far
    mostly have concerned elements of inductive types ([nat], [bool],
    etc.).  But, since Rocq's equality operator is polymorphic, we can use
    it at _any_ type -- in particular, we can write propositions claiming
    that two _functions_ are equal to each other:

    In certain cases Rocq can successfully prove equality propositions stating
    that two _functions_ are equal to each other: **)

Example function_equality_ex1 :
  (fun x => 3 + x) = (fun x => (pred 4) + x).
Proof. reflexivity. Qed.

(** These two functions are equal just by simplification, but in general
    functions can be equal for more interesting reasons. *)

(** In common mathematical practice, two functions [f] and [g] are
    considered equal if they produce the same output on every input:

    (forall x, f x = g x) -> f = g

    This is known as the principle of _functional extensionality_. *)

(** (Informally, an "extensional" property is one that pertains to an
    object's observable behavior.  Thus, functional extensionality
    simply means that a function's identity is completely determined
    by what we can observe from it -- i.e., the results we obtain
    after applying it.) *)

(** However, functional extensionality is not part of Rocq's built-in logic.
    This means that some intuitively obvious propositions are not
    provable. *)

Example function_equality_ex2 :
  (fun x => plus x 1) = (fun x => plus 1 x).
Proof.
  Fail reflexivity. Fail rewrite add_comm.
  (* Stuck *)
Abort.

(** However, if we like, we can add functional extensionality to Rocq
    using the [Axiom] command. *)

Axiom functional_extensionality : forall {X Y: Type}
                                    {f g : X -> Y},
  (forall (x:X), f x = g x) -> f = g.

(** Defining something as an [Axiom] has the same effect as stating a
    theorem and skipping its proof using [Admitted], but it alerts the
    reader that this isn't just something we're going to come back and
    fill in later! *)

(** We can now invoke functional extensionality in proofs: *)

Example function_equality_ex2 :
  (fun x => plus x 1) = (fun x => plus 1 x).
Proof.
  apply functional_extensionality. intros x.
  apply add_comm.
Qed.

(** Naturally, we need to be quite careful when adding new axioms into
    Rocq's logic, as this can render it _inconsistent_ -- that is, it may
    become possible to prove every proposition, including [False], [2+2=5],
    etc.!

    In general, there is no simple way of telling whether an axiom is safe
    to add: hard work by highly trained mathematicians is often required to
    establish the consistency of any particular combination of axioms.

    Fortunately, it is known that adding functional extensionality, in
    particular, _is_ consistent. *)

(** To check whether a particular proof relies on any additional
    axioms, use the [Print Assumptions] command:

      Print Assumptions function_equality_ex2.
*)
(* ===>
     Axioms:
     functional_extensionality :
         forall (X Y : Type) (f g : X -> Y),
                (forall x : X, f x = g x) -> f = g

    (If you try this yourself, you may also see [add_comm] listed as
    an assumption, depending on whether the copy of [Tactics.v] in the
    local directory has the proof of [add_comm] filled in.) *)

(** **** Exercise: 4 stars, standard (tr_rev_correct)

    One problem with the definition of the list-reversing function [rev]
    that we have is that it performs a call to [app] on each step.  Running
    [app] takes time asymptotically linear in the size of the list, which
    means that [rev] is asymptotically quadratic.

    We can improve this with the following two-argument definition: *)

Fixpoint rev_append {X} (l1 l2 : list X) : list X :=
  match l1 with
  | [] => l2
  | x :: l1' => rev_append l1' (x :: l2)
  end.

Definition tr_rev {X} (l : list X) : list X :=
  rev_append l [].

(** This version of [rev] is said to be _tail recursive_, because the
    recursive call to the function is the last operation that needs to be
    performed (i.e., we don't have to execute [++] after the recursive
    call); a decent compiler will generate very efficient code in this
    case.

    Prove that the two definitions are indeed equivalent. *)

Theorem tr_rev_correct : forall X, @tr_rev X = @rev X.
Proof.
(* FILL IN HERE *) Admitted.
(** [] *)

(* ================================================================= *)
(** ** Classical vs. Constructive Logic *)

(** We have seen that it is not possible to test whether or not a
    proposition [P] holds while defining a Rocq function.  You may be
    surprised to learn that a similar restriction applies in _proofs_!
    In other words, the following intuitive reasoning principle is not
    derivable in Rocq: *)

Definition excluded_middle := forall P : Prop,
  P \/ ~ P.

(** To understand operationally why this is the case, recall
    that, to prove a statement of the form [P \/ Q], we use the [left]
    and [right] tactics, which effectively require knowing which side
    of the disjunction holds.  But the universally quantified [P] in
    [excluded_middle] is an _arbitrary_ proposition, which we know
    nothing about.  We don't have enough information to choose which
    of [left] or [right] to apply. *)

(** However, in the special case where we happen to know that [P] is
    reflected in some boolean term [b], knowing whether it holds or
    not is trivial: we just have to check the value of [b]. *)

Theorem restricted_excluded_middle : forall P b,
  (P <-> b = true) -> P \/ ~ P.
Proof.
  intros P [] H.
  - left. rewrite H. reflexivity.
  - right. rewrite H. intros contra. discriminate contra.
Qed.

(** In particular, the excluded middle is valid for equations [n = m],
    between natural numbers [n] and [m]. *)

Theorem restricted_excluded_middle_eq : forall (n m : nat),
  n = m \/ n <> m.
Proof.
  intros n m.
  apply (restricted_excluded_middle (n = m) (n =? m)).
  symmetry.
  apply eqb_eq.
Qed.

(** Sadly, this trick only works for decidable propositions. *)

(** It may seem strange that the general excluded middle is not
    available by default in Rocq, since it is a standard feature of familiar
    logics like ZFC.  But there is a distinct advantage in _not_ assuming
    the excluded middle: statements in Rocq make stronger claims than the
    analogous statements in standard mathematics.  Notably, a Rocq proof of
    [exists x, P x] always includes a particular value of [x] for which we
    can prove [P x] -- in other words, every proof of existence is
    _constructive_. *)

(** Logics like Rocq's, which do not assume the excluded middle, are
    referred to as _constructive logics_.

    Logical systems such as ZFC, in which the excluded middle does
    hold for arbitrary propositions, are referred to as _classical_. *)

(** The following example illustrates why assuming the excluded middle may
    lead to non-constructive proofs:

    _Claim_: There exist irrational numbers [a] and [b] such that [a ^
    b] ([a] to the power [b]) is rational.

    _Proof_: It is not difficult to show that [sqrt 2] is irrational.  So if
    [sqrt 2 ^ sqrt 2] is rational, it suffices to take [a = b = sqrt 2] and
    we are done.  Otherwise, [sqrt 2 ^ sqrt 2] is irrational.  In this
    case, we can take [a = sqrt 2 ^ sqrt 2] and [b = sqrt 2], since [a ^ b
    = sqrt 2 ^ (sqrt 2 * sqrt 2) = sqrt 2 ^ 2 = 2].  []

    Do you see what happened here?  We used the excluded middle to
    consider separately the cases where [sqrt 2 ^ sqrt 2] is rational
    and where it is not, without knowing which one actually holds!
    Because of this, we finish the proof knowing that such [a] and [b]
    exist, but not being sure of their actual values.

    As useful as constructive logic is, it does have its limitations:
    There are many statements that can easily be proven in classical
    logic but that have only much more complicated constructive
    proofs, and there are some that are known to have no constructive
    proof at all!  Fortunately, like functional extensionality, the
    excluded middle is known to be compatible with Rocq's logic,
    allowing us to add it safely as an axiom. However, we will not
    need to do so here: the results that we cover in Software
    Foundations can be developed entirely within constructive logic at
    negligible extra cost.

    It takes some practice to understand which proof techniques must
    be avoided in constructive reasoning, but arguments by
    contradiction, in particular, are infamous for leading to
    non-constructive proofs. Here's a typical example: suppose that we
    want to show that there exists [x] with some property [P], i.e.,
    such that [P x].  We start by assuming that our conclusion is
    false; that is, [~ exists x, P x]. From this premise, it is not
    hard to derive [forall x, ~ P x].  If we manage to show that this
    results in a contradiction, we arrive at an existence proof
    without ever exhibiting a value of [x] for which [P x] holds!

    The technical flaw here, from a constructive standpoint, is that we
    claimed to prove [exists x, P x] using a proof of [~ ~ (exists x, P x)].
    Allowing ourselves to remove double negations from arbitrary
    statements is equivalent to assuming the excluded middle law, as shown
    in one of the exercises below.  Thus, this line of reasoning cannot be
    encoded in Rocq without assuming additional axioms. *)

(** **** Exercise: 3 stars, standard (excluded_middle_irrefutable)

    Proving the consistency of Rocq with the general excluded middle
    axiom requires complicated reasoning that cannot be carried out
    within Rocq itself.  However, the following theorem implies that it
    is always safe to assume a decidability axiom (i.e., an instance
    of excluded middle) for any _particular_ Prop [P].  Why?  Because
    the negation of such an axiom leads to a contradiction.  If [~ (P
    \/ ~P)] were provable, then by [de_morgan_not_or] as proved above,
    [P /\ ~P] would be provable, which would be a contradiction. So, it
    is safe to add [P \/ ~P] as an axiom for any particular [P].

    Succinctly: for any proposition P,
        [Rocq is consistent ==> Rocq + (P \/ ~P) is consistent]. *)

Theorem excluded_middle_irrefutable: forall (P : Prop),
  ~ ~ (P \/ ~ P).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, advanced (not_exists_dist)

    It is a theorem of classical logic that the following two
    assertions are equivalent:

    ~ (exists x, ~ P x)
    forall x, P x

    The [dist_not_exists] theorem above proves one side of this
    equivalence. Interestingly, the other direction cannot be proved
    in constructive logic. Your job is to show that it is implied by
    the excluded middle. *)

Theorem not_exists_dist :
  excluded_middle ->
  forall (X:Type) (P : X -> Prop),
    ~ (exists x, ~ P x) -> (forall x, P x).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 5 stars, standard, optional (classical_axioms)

    For those who like a challenge, here is an exercise adapted from the
    Coq'Art book by Bertot and Casteran (p. 123).  Each of the
    following five statements, together with [excluded_middle], can be
    considered as characterizing classical logic.  We can't prove any
    of them in Rocq, but we can consistently add any _one_ of them as an
    axiom if we wish to work in classical logic.

    To see this, prove that all six propositions (these five plus
    [excluded_middle]) are equivalent.

    Hint: Rather than considering all pairs of statements pairwise,
    prove a single circular chain of implications that connects them
    all. *)

Definition peirce := forall P Q: Prop,
  ((P -> Q) -> P) -> P.

Definition double_negation_elimination := forall P:Prop,
  ~~P -> P.

Definition de_morgan_not_and_not := forall P Q:Prop,
  ~(~P /\ ~Q) -> P \/ Q.

Definition implies_to_or := forall P Q:Prop,
  (P -> Q) -> (~P \/ Q).

Definition consequentia_mirabilis := forall P:Prop,
  (~P -> P) -> P.

(* FILL IN HERE

    [] *)

(* 2026-06-10 15:50 *)
