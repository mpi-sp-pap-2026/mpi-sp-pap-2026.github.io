(** * Noninterference1: Defining Secrecy and Secure Multi-Execution for Rocq Functions *)

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Init.Nat.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Arith.EqNat. Import Nat.
Set Default Goal Selector "!".

(** Programmers have to be very careful about how information flows in
    the software they develop to prevent leaking secret data. For
    instance, in course management systems students shouldn't be able
    to obtain information about other students' grades or passwords.
    In crypto protocols the keys should be kept secret and not sent
    over the network in the clear. *)

(** Information-flow control tries to prevent leaking such secret
    information.  But how does one formalize that a program doesn't
    leak any information about the secret inputs to public outputs? *)

(** We first investigate this question of how to define secrecy in the
    very simple setting of Rocq functions taking two arguments, one we
    call the public input and the other one we call the secret
    input. Our functions return a pair where the first element is the
    public output and the second one the secret output. *)

(** Say we have the following function working on natural numbers: *)

Definition secure_f (pi si : nat) : nat*nat := (pi+1, pi+si*2).

(** This function seems intuitively secure, since the first output [pi+1], which
    we assume to be public, only depends on the public input [pi], but not on
    the secret input [si]. The second output [pi+si*2] depends on both the
    public input and the secret input, but that's okay, since we assume this
    second output to be secret. *)

(** Still, how can we mathematically define that this function is
    secure? Let's try it on a couple of inputs: *)

Example example1_secure_f : secure_f 0 0 = (1,0).
Proof. reflexivity. Qed.

Example example2_secure_f : secure_f 0 1 = (1,2).
Proof. reflexivity. Qed.

Example example3_secure_f : secure_f 1 2 = (2,5).
Proof. reflexivity. Qed.

(** In the last two cases the public output is equal to the value
    of the secret input. But that's just a coincidence (i.e. the secret
    input happening to be one more than the public input), and has
    nothing to do with the public output leaking the secret input,
    which wasn't used at all in computing the public output. *)

(* ################################################################# *)
(** * Naive attempt at defining secrecy *)

(** So a naive security definition, which we'll only use as a
    strawman, is one that simply requires that the public output is
    different from the secret input, for all inputs of function [f]: *)

Definition broken_sec_def (f : nat -> nat -> nat*nat) :=
  forall pi si, fst (f pi si) <> si.

(** As discussed above, this broken definition would reject our secure
    function above as insecure: *)

Lemma broken_sec_def_rejects_secure_f : ~broken_sec_def secure_f.
Proof. intros Hc. apply (Hc 0 1). reflexivity. Qed.

(** Even worse, this broken definition of security would allow _insecure_
    functions, such as the following one whose public output is [si+1]: *)

Definition insecure_f (pi si : nat) : nat*nat := (si+1, pi+si*2).

(** This function's public output is _never equal_ to its secret
    input, yet an attacker can easily compute one from the other by
    just subtracting [1]. So the secret is entirely leaked, yet our
    broken definition accepts this as secure: *)

Lemma broken_sec_def_accepts_insecure_f : broken_sec_def insecure_f.
Proof.
  unfold broken_sec_def. intros pi si. induction si as [| si' IH].
  - simpl. intros contra. discriminate contra.
  - simpl in *. intro Hc. injection Hc as Hc. apply IH. apply Hc.
Qed.

(** This naive attempt at defining secure information flow by looking at how
    inputs and outputs are related for a single execution of the
    program was a complete failure. In fact, it is well known in the
    formal security research community that secure information flow
    _cannot_ be defined by looking at just one single program execution. *)

(* ################################################################# *)
(** * Noninterference for pure functions *)

(** The simplest correct way to define secure information flow is a
    property called _noninterference_ [Sabelfeld and Myers 2003] (in Bib.v),
    which in its most standard form looks at _two_ program executions:
    for two different secret inputs the public outputs should not change: *)

Definition noninterferent {PI SI PO SO : Type} (f:PI->SI->PO*SO) :=
  forall (pi:PI) (si1 si2:SI), fst (f pi si1) = fst (f pi si2).

(** This definition prevents changes in secret inputs from changing the
    public outputs, so it prevents secret inputs from interfering with
    public outputs in any way. At the same time it allows secret
    inputs to influence secret outputs and also public inputs to
    influence both public and secret outputs:

                                ┌───╮
                                │ f │
                           pi ─>┼───┼─> po
                                │╲  │
                                │ ╲ │
                                │  ╲│
                           si ─>┼───┼─> so
                                └───╯
*)

(** The definition above states noninterference for arbitrary types
    of inputs and outputs, so we can instantiate them to [nat] when
    looking at our example functions above: *)

Print secure_f. (* fun pi si : nat => (pi + 1, pi + si * 2) *)

Lemma noninterferent_secure_f : noninterferent secure_f.
Proof. unfold noninterferent, secure_f. simpl. reflexivity. Qed.

Print insecure_f. (* fun pi si : nat => (si + 1, pi + si * 2) *)

Lemma interferent_insecure_f : ~noninterferent insecure_f.
Proof.
  (* WORKED IN CLASS *)
  unfold noninterferent. simpl. intros contra.
  specialize (contra 42 3 7). simpl in contra. discriminate contra.
Qed.

(** The [secure_f] function above is quite obviously noninterferent,
    because the expression [pi+1] computing the public output doesn't
    syntactically mention the secret input at all. Since
    noninterference is a semantic property though (not a syntactic
    one), functions where the expression computing the public output
    does syntactically mention the secret input can still be
    noninterferent. Here is a first example: *)

Definition less_obvious_f1 (pi si : nat) : nat*nat := (si * 0, pi+si).

(** This new function is noninterferent; since the public output is
    constant [0], so it can't depend on [si], even if it syntactically
    mentions it: *)

Lemma noninterferent_less_obvious_f1 : noninterferent less_obvious_f1.
Proof.
  unfold noninterferent, less_obvious_f1. intros pi si1 si2. simpl.
  rewrite <- mult_n_O. rewrite <- mult_n_O. reflexivity.
Qed.



(** Here is another example of a function that is noninterferent, even
    if this is not syntactically obvious: *)

Definition less_obvious_f2 (pi si : nat) : nat*nat :=
  (if si =? 1 then si*pi else pi, pi+si).

(** For proving this function noninterferent we first show that the
    public output of this function is in fact always equal to just its
    public input: *)

Lemma po_equal_pi_f2 : forall si pi, (if si =? 1 then si*pi else pi) = pi.
Proof.
  intros si pi. destruct (si =? 1) eqn:Eq.
  - apply Nat.eqb_eq in Eq. rewrite Eq.
    simpl. rewrite <- plus_n_O. reflexivity.
  - reflexivity.
Qed.

Lemma noninterferent_less_obvious_f2 : noninterferent less_obvious_f2.
Proof.
  unfold noninterferent, less_obvious_f2. intros pi si1 si2.
  rewrite po_equal_pi_f2. rewrite po_equal_pi_f2. simpl. reflexivity.
Qed.

(** Branching on a secret can, however, be dangerous, since one can
    easily leak the secret this way, even if both the [then] and the
    [else] branches are public constants. For instance the following
    function leaks whether [si] is zero or not, so it is not secure. *)

Definition less_obvious_f3 (pi si : nat) : nat*nat :=
  (if si =? 0 then 1 else 0, pi+si).

Lemma interferent_less_obvious_f3 : ~noninterferent less_obvious_f3.
Proof.
  unfold noninterferent, less_obvious_f3. simpl. intros contra.
  specialize (contra 42 0 10). simpl in contra. discriminate contra.
Qed.

(* ================================================================= *)
(** ** Noninterference Exercises *)

(** Let's practice with some "prove or disprove noninterference"
    exercises, for which you are required to give constructive proofs,
    i.e. the use of classical axioms like excluded middle is not allowed. *)

(** **** Exercise: 1 star, standard (prove_or_disprove_obvious_f1) *)
Definition obvious_f1 (pi si : nat) : nat*nat := (0,0).

Lemma prove_or_disprove_obvious_f1 :
  noninterferent obvious_f1 \/ ~noninterferent obvious_f1.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 1 star, standard (prove_or_disprove_obvious_f2) *)
Definition obvious_f2 (pi si : nat) : nat*nat := (pi+(2*si),(2*pi)+si).

Lemma prove_or_disprove_obvious_f2 :
  noninterferent obvious_f2 \/ ~noninterferent obvious_f2.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard (prove_or_disprove_less_obvious_f4) *)

Definition less_obvious_f4 (pi si : nat) : nat*nat :=
  (if si =? 0 then si * pi else pi, pi+si).

(** Is the [less_obvious_f4] function noninterferent or not? *)

Lemma prove_or_disprove_less_obvious_f4 :
  noninterferent less_obvious_f4 \/ ~noninterferent less_obvious_f4.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard (prove_or_disprove_less_obvious_f5) *)

Definition less_obvious_f5 (pi si : nat) : nat*nat :=
  (if si =? 0 then si + pi else pi, pi+si).

(** Is the [less_obvious_f5] function noninterferent or not? *)

Lemma prove_or_disprove_less_obvious_f5 :
  noninterferent less_obvious_f5 \/ ~noninterferent less_obvious_f5.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard (prove_or_disprove_less_obvious_f6) *)

Definition less_obvious_f6 (pi si : nat): nat*nat :=
  (if Nat.ltb si pi then 0 else pi, pi+si).

(** Is the [less_obvious_f6] function noninterferent or not? *)

Lemma prove_or_disprove_less_obvious_f6 :
  noninterferent less_obvious_f6 \/ ~noninterferent less_obvious_f6.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, standard, optional (prove_or_disprove_less_obvious_f7) *)

Definition less_obvious_f7 (pi si : nat): nat*nat :=
  if si + pi =? 0 then (si,pi) else (pi,si).

Lemma prove_or_disprove_less_obvious_f7 :
  noninterferent less_obvious_f7 \/ ~noninterferent less_obvious_f7.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard (noninterferent_diff_si_same) *)

(** Finally, consider the following alternative definition of
    noninterference, which requires the two secret inputs to be
    different. It more directly captures the original intuition that
    _changing_ the secret input should not change the public output: *)

Definition noninterferent_diff_si {PI SI PO SO : Type} (f:PI->SI->PO*SO) :=
  forall (pi:PI) (si1 si2:SI), si1 <> si2 -> fst (f pi si1) = fst (f pi si2).

(** Prove that this definition of noninterference is equivalent to the
    original one, at least on type [nat] (which supports decidable
    equality; otherwise we would need excluded middle to prove this). *)

Lemma noninterferent_diff_si_same : forall (f:nat->nat->nat*nat),
  noninterferent_diff_si f <-> noninterferent f.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ################################################################# *)
(** * A too-strong secrecy definition *)

(** In the definition of noninterference above we pass the same public
    inputs to the two executions and this allows public outputs to
    depend on public inputs. To convince ourselves of this, let's look
    at the following overly strong definition of security: *)

Definition too_strong_sec_def {PI SI PO SO : Type} (f:PI->SI->PO*SO) :=
  forall (pi1 pi2:PI) (si1 si2:SI), fst (f pi1 si1) = fst (f pi2 si2).

(** This basically says that the public output of [f] can depend
    neither on the public input nor on the secret input, so it has to
    be constant, which is not the case for our [secure_f]. *)

Print secure_f. (* fun pi si : nat => (pi + 1, pi + si * 2) *)

Lemma secure_f_rejected_again : ~too_strong_sec_def secure_f.
Proof.
  unfold too_strong_sec_def, secure_f. simpl. intros contra.
  specialize (contra 0 1 0 0). discriminate contra.
Qed.

(* ################################################################# *)
(** * Noninterferent the same as being splittable *)

(** Noninterference is still a very strong property, though. In
    particular, [f] being noninterferent is equivalent to [f] being
    splittable into two distinct functions: a public function that
    doesn't get the secret input, and a secret function that does. *)

Definition splittable {PI SI PO SO : Type} (f:PI->SI->PO*SO) :=
  exists (pf : PI -> PO) (sf : PI -> SI -> SO),
    forall pi si , f pi si = (pf pi, sf pi si).

(** One of the equivalence directions is easy: *)

Theorem splittable_noninterferent : forall PI SI PO SO : Type,
  forall f : PI -> SI -> PO*SO, splittable f -> noninterferent f.
Proof.
  unfold splittable, noninterferent.
  intros PI SI PO SO f [pf [sf H]] pi si1 si2.
  rewrite H. rewrite H. simpl. reflexivity.
Qed.

(** The other equivalence direction is more interesting: *)

Theorem noninterferent_splittable : forall PI SI PO SO : Type,
  forall some_si : SI, (* we require SI to be an inhabited type! *)
  forall f : PI -> SI -> PO*SO, noninterferent f -> splittable f.
Proof.
  unfold splittable, noninterferent.
  intros PI SI PO SO some_si f NI.
  (* we construct pf and sf using f itself *)
  (* for pf we pass the SI inhabitant as a dummy secret value! *)
  exists (fun pi => fst (f pi some_si)).
  exists (fun pi si => snd (f pi si)).
  (* we then use NI to change from dummy secret to real one *)
  intros pi si. rewrite (NI _ _ si).
  destruct (f pi si) as [po so]. reflexivity.
Qed.

(* ################################################################# *)
(** * Secure Multi-Execution (SME) *)

(** The previous proof also captures the key idea behind Secure
    Multi-Execution (SME) [Devriese and Piessens 2010] (in Bib.v), an
    enforcement mechanism that can make _any_ function
    noninterferent. To achieve this SME runs the function twice, once
    passing a dummy secret as input to obtain the public output, and
    once using the real secret input to obtain the secret output. *)

Definition sme {PI SI PO SO : Type} (some_si : SI)
  (f:PI->SI->PO*SO) : PI->SI->PO*SO :=
    fun pi si => (fst (f pi some_si), snd (f pi si)).

(** Functions protected by [sme] are guaranteed to satisfy noninterference: *)

Theorem noninterferent_sme :  forall PI SI PO SO : Type,
  forall some_si : SI,
  forall f : PI -> SI -> PO*SO,
    noninterferent (sme some_si f).
Proof. intros PI SI PO SO some_si f pi si1 si2. simpl. reflexivity. Qed.

(** Moreover, if the function we pass to [sme] is already noninterferent,
    then its behavior will not change; so we say that [sme] is a _transparent_
    enforcement mechanism for noninterference: *)

Theorem transparent_sme : forall PI SI PO SO : Type,
  forall some_si : SI,
  forall f : PI -> SI -> PO*SO,
    noninterferent f -> forall pi si, f pi si = sme some_si f pi si.
Proof.
  unfold noninterferent, sme. intros PI SI PO SP some_si f NI.
  (* The rest is the same as [noninterferent_splittable] proof *)
  intros pi si. rewrite (NI _ _ si).
  destruct (f pi si) as [po so]. reflexivity.
Qed.

(** It is interesting to look at what [sme] does for _interferent_ functions,
    like [insecure_f], whose public output was its secret input plus [1]: *)

Print insecure_f. (* fun pi si : nat => (si + 1, pi + si * 2) *)

Example example1_sme_insecure_f: sme 0 insecure_f 0 0 = (1, 0).
Proof. reflexivity. Qed.

Example example2_sme_insecure_f: sme 0 insecure_f 0 1 = (1, 2).
Proof. reflexivity. Qed.

Example example3_sme_insecure_f: sme 0 insecure_f 1 1 = (1, 3).
Proof. reflexivity. Qed.

(** Now the public output of [sme insecure_f 0] is the dummy secret
    [0] plus [1], so always the constant [1]. *)

Lemma constant_sme_insecure_f: forall pi si,
  fst (sme 0 insecure_f pi si) = 1.
Proof. unfold sme, insecure_f. reflexivity. Qed.

(** This is a secure behavior, but it is different from that of the
    original [insecure_f] function. So we are giving up some
    correctness for security. There is no free lunch! *)

(** Of course the public output of [sme] does not always become constant,
    since some functions still use the public input. *)

Definition another_insecure_f (pi si : nat) := (pi+si, pi+si).

Lemma sme_another_insecure_f : forall pi si,
  sme 0 (another_insecure_f) pi si = (pi,pi+si).
Proof. unfold sme, another_insecure_f.
  intros pi si. simpl. rewrite <- plus_n_O. reflexivity. Qed.

(** **** Exercise: 1 star, standard (sme_another_insecure_f2) *)
Definition another_insecure_f2 (pi si : nat) : nat*nat :=
  (if si =? 0 then 2*pi else pi, pi+si).

Lemma sme_another_insecure_f2 : forall pi si,
    sme 0 (another_insecure_f2) pi si = (2*pi, pi+si).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard (sme_another_insecure_f3) *)
Definition another_insecure_f3 (pi si : nat) : nat*nat :=
  (if si =? pi then si * pi else pi, pi+si).

Lemma sme_another_insecure_f3 : forall pi si,
    sme 0 (another_insecure_f3) pi si = (pi, pi+si).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 1 star, standard (sme_correct_so)

    While the public output of [sme] can be incorrect,
    the secret output of [sme] is obviously always correct: *)
Lemma sme_correct_so : forall PI SI PO SO : Type,
  forall some_si : SI,
  forall f : PI -> SI -> PO*SO,
  forall pi si, snd (f pi si) = snd (sme some_si f pi si).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** Beyond giving up on correctness for the public outputs of insecure functions,
    the other downside of SME is that we have to run the function
    twice for our two security levels, public and secret. In general,
    we need to run the program as many times as we have security
    levels, which can be a large number (e.g., exponential if we take our
    security levels to be sets of users). This is inefficient! *)

(** Other information-flow control mechanisms overcome these downsides,
    but have their own pros and cons, for instance:
        - _Information-flow type systems_ ([StaticIFC]) do not
          introduce any runtime overhead, but use static
          overapproximations that reject some secure programs.
        - _Relational Hoare Logic_ is static and precise, but requires
          nontrivial manual proofs for each individual program.
        - _Dynamic information-flow control_ (a secure variant of dynamic
          taint tracking) is generally more efficient than SME, but
          uses dynamic overapproximations that unnecessarily change
          some program behavior to prevent leaks, for instance forcefully
          terminating even some secure programs (which is not transparent).

    Again, there is no free lunch! *)

(* 2026-06-24 16:36 *)
