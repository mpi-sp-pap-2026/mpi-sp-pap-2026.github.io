(** * Basics: Functional Programming in Coq *)

(* ################################################################# *)
(** * Data and Functions *)

(* ================================================================= *)
(** ** Enumerated Types *)

(** In Coq, we can build practically everything from first
    principles... *)

(* ================================================================= *)
(** ** Days of the Week *)

(** A datatype definition: *)

Inductive day : Type :=
  | monday 
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.

(** A function on days: *)

Definition next_weekday (d:day) : day :=
  match d with
  | monday    => tuesday
  | tuesday   => wednesday
  | wednesday => thursday
  | thursday  => friday
  | _  => monday
  end.

(** Simplification: *)

Compute (next_weekday friday).
(* ==> monday : day *)

Compute (next_weekday (next_weekday (saturday))).
(* ==> tuesday : day *)
