(***************************************************************************
* Formalization of ES calculi						   *
*									   *
* Generic Variables for Programming Language Metatheory                    *
* Brian Aydemir & Arthur Chargu\u00e9raud, July 2007, 	                   *
* Fabien Renaud, 2011	                                                   *
* Flávio L. C. de Moura, 2015                     			   *
***************************************************************************)

Set Implicit Arguments.
Require Import List Max Omega Equalities Arith LibTactics.
Require Import MSetList MSetProperties MSetFacts MSetDecide.
Require Import Eqdep_dec.

(** * Definitions *)

Definition var := nat.


Declare Module Var_as_OT : UsualOrderedType
  with Definition t := var.
Module Import VarSet := MSetList.Make Var_as_OT.

Definition vars := VarSet.t.


Notation "{}" := (VarSet.empty).
Notation "{{ x }}" := (VarSet.singleton x).
Notation "s [=] t " := (VarSet.Equal s t) (at level 70, no associativity). 
Notation "E \u F" := (VarSet.union E F)  (at level 68, left associativity).
Notation "x \in E" := (VarSet.In x E) (at level 69).
Notation "x \notin E" := (~ VarSet.In x E) (at level 69).
Notation "E << F" := (VarSet.Subset E F) (at level 70, no associativity).
Notation "E \rem F" := (VarSet.remove F E) (at level 70).


(* Properties on variables sets *)
Module Import VSP := WPropertiesOn Var_as_OT VarSet.
(* Facts on variables sets *)
Module Import VSF := WFactsOn Var_as_OT VarSet.
(* Some decision procedures on variables sets *)
Module Import VSD := WDecideOn Var_as_OT VarSet.



(** * Basic properties on sets.
The following lemmas already exist in the MSet library.
But it's long to find them and replace them everywhere so we keep them for the moment *)

Lemma in_empty : forall x,   x \in {} -> False.
Proof. VSD.fsetdec. Qed.

Lemma notin_singleton : forall x y,
  x \notin {{y}} <-> x <> y.
Proof. intros ; split ; VSD.fsetdec. Qed.

Lemma in_singleton : forall x y,  x \in {{y}} <-> x = y.
Proof. VSD.fsetdec. Qed.

Lemma in_union : forall x E F,
  x \in (E \u F) <-> (x \in E) \/ (x \in F).
Proof. intros ; split ; VSD.fsetdec. Qed.

Lemma notin_empty : forall x,
  x \notin {}.
Proof. VSD.fsetdec. Qed.

Lemma notin_same : forall x,
  x \notin {{x}} -> False.
Proof. VSD.fsetdec. Qed.

Lemma union_comm : forall E F,
  E \u F [=] F \u E.
Proof. intros. VSD.fsetdec. Qed.

Lemma notin_singleton_r : forall x y,
  x \notin {{y}} -> x <> y.
Proof. intros. VSD.fsetdec. Qed.

Lemma notin_singleton_l : forall x y,
  x <> y -> x \notin {{y}}.
Proof. intros. VSD.fsetdec. Qed.

Lemma notin_singleton_swap : forall x y,
  x \notin {{y}} -> y \notin {{x}}.
Proof.
  intros. apply notin_singleton_l.
  apply sym_not_eq. apply~ notin_singleton_r.
Qed.

Lemma notin_union : forall x E F,
  x \notin (E \u F) <-> (x \notin E) /\ (x \notin F).
Proof. intros. VSD.fsetdec. Qed.


Lemma notin_union_r : forall x E F,
  x \notin (E \u F) -> (x \notin E) /\ (x \notin F).
Proof. introv. rewrite* notin_union. Qed.

Lemma notin_union_r1 : forall x E F,
  x \notin (E \u F) -> (x \notin E).
Proof. introv. rewrite* notin_union. Qed.

Lemma notin_union_r2 : forall x E F,
  x \notin (E \u F) -> (x \notin F).
Proof. introv. rewrite* notin_union. Qed.

Lemma notin_union_l : forall x E F,
  x \notin E -> x \notin F -> x \notin (E \u F).
Proof. intros. rewrite~ notin_union. Qed.

Lemma union_comm_assoc : forall E F G,
  E \u (F \u G) [=] F \u (E \u G).
Proof. VSD.fsetdec. Qed.

Lemma union_assoc : forall E F G,
  E \u (F \u G) [=] (E \u F) \u G.
Proof. VSD.fsetdec. Qed.

Lemma union_same : forall E,
  E \u E [=] E.
Proof. VSD.fsetdec. Qed.

Lemma union_eq : forall E F E' F', E [=] E' -> F [=] F' -> E \u F [=] E' \u F'.
Proof. VSD.fsetdec. Qed.


Lemma union_empty_r : forall E,
  E \u {} [=] E.
Proof. VSD.fsetdec. Qed.

Lemma union_empty_l : forall E,
  {} \u E [=] E.
 Proof.  VSD.fsetdec. Qed.

Lemma subset_refl : forall E,
  E << E.
Proof. intros_all~. Qed.

Lemma subset_trans : forall F E G,
  E << F -> F << G -> E << G.
Proof. VSD.fsetdec. Qed.


Lemma subset_empty_l : forall E,
  {} << E.
Proof. VSD.fsetdec. Qed.

Lemma subset_singleton : forall x E,
  x \in E <-> {{x}} << E.
Proof. intros ; split ; VSD.fsetdec. Qed.

Lemma subset_union_weak_l : forall E F,
  E << (E \u F).
Proof. VSD.fsetdec. Qed.


Lemma subset_union_weak_r : forall E F,
  F << (E \u F).
Proof. VSD.fsetdec. Qed.

Lemma subset_union_trans_l : forall E F F', F << F' -> F \u E << F' \u E.
Proof. VSD.fsetdec. Qed.

Lemma subset_union_trans_r : forall E F F', F << F' -> E \u F << E \u F'.
Proof. VSD.fsetdec. Qed.


Lemma subset_union_l : forall E F G,
  (E \u F) << G <-> (E << G) /\ (F << G).
Proof. intros ; split ; intros ; try split ; VSD.fsetdec. Qed.



Lemma max_lt_l :
  forall (x y z : nat), x <= y -> x <= max y z.
Proof.
  induction x; auto with arith.
  induction y; induction z; simpl; auto with arith.
Qed.


(** * About lists *)
Require Import List.
Open Scope list_scope.

Lemma finite_nat_list_max : forall (l : list nat),
  { n : nat | forall x, In x  l -> x <= n }.
Proof.
  induction l as [ | l ls IHl ].
  exists 0; intros x H; inversion H.
  inversion IHl as [x H].
  exists (max x l); intros y J; simpl in J; inversion J.
    subst; auto with arith.
    assert (y <= x); auto using max_lt_l.
Qed.

Lemma finite_nat_list_max' : forall (l : list nat),
  { n : nat | ~ In n l }.
Proof.
  intros l. case (finite_nat_list_max l); intros x H.
  exists (S x). intros J. assert (K := H _ J); omega.
Qed.


Close Scope list_scope.

(** Finally, we have a means of generating fresh variables. *)
Definition var_gen (L : vars) : var :=
  proj1_sig (finite_nat_list_max' (elements L)).



Lemma var_gen_spec : forall E, (var_gen E) \notin E.
Proof.
  unfold var_gen. intros E.
  destruct (finite_nat_list_max' (elements E)) as [n pf].
  simpl. intros a. 
  destruct pf.
  rewrite elements_iff in a.
  rewrite InA_alt in a.
  destruct a as [y [H1 H2]].
  subst.
  assumption.
Qed.


Lemma notin_var_gen : forall E F,
  (forall x, x \notin E -> x \notin F) ->
  (var_gen E) \notin F.
Proof. intros. auto~ var_gen_spec. Qed.



Lemma var_fresh : forall (L : vars), { x : var | x \notin L }.
Proof.
  intros L. exists (var_gen L). apply var_gen_spec.
Qed.


(* ********************************************************************** *)
(** * Properties of variables *)

Require Import Arith. 
Lemma eq_var_dec : forall x y : var, {x = y} + {x <> y}.
Proof. exact eq_nat_dec. Qed.


Lemma subset_union_var : forall (E F : vars) (x:var), x \notin E -> x \notin F -> E \u {{x}} << F \u {{x}} -> E << F.
Proof. VSD.fsetdec. Qed.

 
(* Attention, conditions x \notin E and x \notin F are necessary, otherwise it's false *)
Lemma fset_union_notin : forall E F x, x \notin E -> x \notin F -> E \u {{x}} [=] F \u {{x}} -> E [=] F.
Proof. VSD.fsetdec. Qed.



(* ********************************************************************** *)
(** * Dealing with list of variables *)
Open Scope list_scope.

(** Freshness of n variables from a set L and from one another. *)
Fixpoint fresh (L : vars) (n : nat) (xs : list var) {struct xs} : Prop :=
  match xs, n with
  | nil, O => True
  | x::xs', S n' => x \notin L /\ fresh (L \u {{x}}) n' xs'
  | _,_ => False
  end.

Hint Extern 1 (fresh _ _ _) => simpl.

(** Triviality : If a list xs contains n fresh variables, then
    the length of xs is n. *)
Lemma fresh_length : forall xs L n,
  fresh L n xs -> n = length xs.
Proof.
  induction xs; simpl; intros; destruct n; 
  try solve [ false~ | fequals* ].
Qed.

(* It is possible to build a list of n fresh variables. *)
Lemma var_freshes : forall L n, 
  { xs : list var | fresh L n xs }.
Proof.
  intros. gen L. induction n; intros L.
  exists* (nil : list var).
  destruct (var_fresh L) as [x Fr].
   destruct (IHn (L \u {{x}})) as [xs Frs].
   exists* (x::xs).
Qed.
