(***************************************************************************
* Formalization of lambda j						   *		
*									   *
* Definitions of explicit substitutions 				   *
* Brian Aydemir & Arthur Chargueraud, July 2007              	   	   *
* Fabien Renaud, 2011							   *
***************************************************************************)

Set Implicit Arguments.
Require Import Metatheory Arith.

(** Grammar of pre-terms. *)
Inductive pterm : Set :=
  | pterm_bvar : nat -> pterm
  | pterm_fvar : var -> pterm
  | pterm_app  : pterm -> pterm -> pterm
  | pterm_abs  : pterm -> pterm
  | pterm_sub : pterm -> pterm -> pterm 
  | pterm_sub' : pterm -> pterm -> pterm  (* labeled explicit substitutions *)
.

Notation "t [ u ]" := (pterm_sub t u) (at level 70).
Notation "t [[ u ]]" := (pterm_sub' t u) (at level 70).

(** Opening up abstractions and substitutions *)
Fixpoint open_rec (k : nat) (u : pterm) (t : pterm) {struct t} : pterm :=
  match t with
  | pterm_bvar i    => if k === i then u else (pterm_bvar i)
  | pterm_fvar x    => pterm_fvar x
  | pterm_app t1 t2 => pterm_app (open_rec k u t1) (open_rec k u t2)
  | pterm_abs t1    => pterm_abs (open_rec (S k) u t1)
  | pterm_sub t1 t2 => pterm_sub (open_rec (S k) u t1) (open_rec k u t2)
  | pterm_sub' t1 t2 => pterm_sub' (open_rec (S k) u t1) (open_rec k u t2)
  end.

Definition open t u := open_rec 0 u t.


Notation "{ k ~> u } t" := (open_rec k u t) (at level 67).
Notation "t ^^ u" := (open t u) (at level 67). (* verificar *)
Notation "t ^ x" := (open t (pterm_fvar x)).   (* verificar *)



(** Variable closing *)
Fixpoint close_rec  (k : nat) (x : var) (t : pterm) {struct t} : pterm :=
  match t with
  | pterm_bvar i    => pterm_bvar i
  | pterm_fvar x'    => if x' == x then (pterm_bvar k) else pterm_fvar x'
  | pterm_app t1 t2 => pterm_app (close_rec k x t1) (close_rec k x t2)
  | pterm_abs t1    => pterm_abs (close_rec (S k) x t1)
  | pterm_sub t1 t2 => pterm_sub (close_rec (S k) x t1) (close_rec k x t2)
  | pterm_sub' t1 t2 => pterm_sub' (close_rec (S k) x t1) (close_rec k x t2)
  end.

Definition close t x := close_rec 0 x t.

Fixpoint fv (t : pterm) {struct t} : vars :=
  match t with
  | pterm_bvar i    => {}
  | pterm_fvar x    => {{x}}
  | pterm_app t1 t2 => (fv t1) \u (fv t2)
  | pterm_abs t1    => (fv t1)
  | pterm_sub t1 t2 => (fv t1) \u (fv t2)
  | pterm_sub' t1 t2 => (fv t1) \u (fv t2)
  end.

  
Fixpoint bswap_rec (k : nat) (t : pterm) {struct t} : pterm :=
  match t with
  | pterm_bvar i    => if k === i then (pterm_bvar (S k))
                       else (if (S k) === i then (pterm_bvar k) else (pterm_bvar i))
  | pterm_fvar x    => pterm_fvar x
  | pterm_app t1 t2 => pterm_app (bswap_rec k t1) (bswap_rec k t2)
  | pterm_abs t1    => pterm_abs (bswap_rec (S k) t1)
  | pterm_sub t1 t2 => pterm_sub (bswap_rec (S k) t1) (bswap_rec k t2)
  | pterm_sub' t1 t2 => pterm_sub' (bswap_rec (S k) t1) (bswap_rec k t2)
  end.

Definition bswap t := bswap_rec 0 t.
Notation "& t" := (bswap t) (at level 67).

Fixpoint swap (x y : var) (t : pterm) {struct t} : pterm :=
  match t with
  | pterm_bvar i    => pterm_bvar i
  | pterm_fvar z    => if z == x then (pterm_fvar y) else 
                       if z == y then (pterm_fvar x) else pterm_fvar z
  | pterm_app t1 t2 => pterm_app (swap x y t1) (swap x y t2)
  | pterm_abs t1    => pterm_abs (swap x y t1)
  | pterm_sub t1 t2 => pterm_sub (swap x y t1) (swap x y t2)
  | pterm_sub' t1 t2 => pterm_sub' (swap x y t1) (swap x y t2)
  end.

Notation "[( x , y )] t" := (swap x y t) (at level 67).

(******************************************************)
(** * Definitions *)

(** ** Size of a term *)
Fixpoint pterm_size (t : pterm) {struct t} : nat :=
 match t with
 | pterm_bvar i    => 1
 | pterm_fvar x    => 1
 | pterm_abs t1    => 1 + (pterm_size t1)
 | pterm_app t1 t2 => 1 + (pterm_size t1) + (pterm_size t2)
 | pterm_sub t1 t2 => 1 + (pterm_size t1) + (pterm_size t2)
 | pterm_sub' t1 t2 => 1 + (pterm_size t1) + (pterm_size t2)
 end.

Lemma pterm_size_non_null : forall t, pterm_size t > 0.
Proof.
  induction t.
  simpl. auto.
  simpl. auto.  
  simpl. omega.
  simpl. omega.
  simpl. omega.
  simpl. omega.
Qed.

  
  (** ** Implicit substitution, for free names *)
Fixpoint subst (z : var) (u : pterm) (t : pterm) {struct t} : pterm :=
  match t with
  | pterm_bvar i    => pterm_bvar i
  | pterm_fvar x    => if x == z then u else (pterm_fvar x)
  | pterm_abs t1    => pterm_abs (subst z u t1)
  | pterm_app t1 t2 => pterm_app (subst z u t1) (subst z u t2)
  | pterm_sub t1 t2 => pterm_sub (subst z u t1) (subst z u t2)
  | pterm_sub' t1 t2 => pterm_sub' (subst z u t1) (subst z u t2)
  end.
Notation "[ z ~> u ] t" := (subst z u t) (at level 62).

(** Terms are locally-closed pre-terms *)
Inductive term : pterm -> Prop :=
  | term_var : forall x,
      term (pterm_fvar x)
  | term_app : forall t1 t2,
      term t1 -> 
      term t2 -> 
      term (pterm_app t1 t2)
  | term_abs : forall L t1,
      (forall x, x \notin L -> term (t1 ^ x)) ->
      term (pterm_abs t1)
  | term_sub : forall L t1 t2,
     (forall x, x \notin L -> term (t1 ^ x)) ->
      term t2 -> 
      term (pterm_sub t1 t2).

Lemma term_size_non_null : forall t, term t -> pterm_size t > 0.
Proof.
  intros t Ht. destruct t.
  simpl; auto.  
  simpl; auto.  
  simpl. omega.
  simpl. omega.
  simpl. omega.
  simpl. omega.
Qed.  

(** Lambda terms ***)
Inductive Lterm : pterm -> Prop :=
  | Lterm_var : forall x,
      Lterm (pterm_fvar x)
  | Lterm_app : forall t1 t2,
      Lterm t1 -> 
      Lterm t2 -> 
      Lterm (pterm_app t1 t2)
  | Lterm_abs : forall L t1,
      (forall x, x \notin L -> Lterm (t1 ^ x)) ->
      Lterm (pterm_abs t1).

(** ** Body *) 
(* Notice, that the "body" of a substitution is its LEFT part *)
Definition body t := exists L, forall x, x \notin L -> term (t ^ x).

(** ** Body for Lambda terms *) 
Definition Lbody t := exists L, forall x, x \notin L -> Lterm (t ^ x).

(* ====================================================================== *)
(** ** Alternative definition for local closure *)


(* ********************************************************************** *)
(** Local closure, recursively defined *)

Fixpoint lc_at (k:nat) (t:pterm) {struct t} : Prop :=
  match t with 
  | pterm_bvar i    => i < k
  | pterm_fvar x    => True
  | pterm_app t1 t2 => lc_at k t1 /\ lc_at k t2
  | pterm_abs t1    => lc_at (S k) t1
  | pterm_sub t1 t2 => (lc_at (S k) t1) /\ lc_at k t2
  | pterm_sub' t1 t2 => False (* verificar *)
  end.

Definition term' t := lc_at 0 t.

Definition body' t := lc_at 1 t.


(* ********************************************************************** *)
(** Local closure for Lambda terms, recursively defined *)

Fixpoint Llc_at (k:nat) (t:pterm) {struct t} : Prop :=
  match t with 
  | pterm_bvar i    => i < k
  | pterm_fvar x    => True
  | pterm_app t1 t2 => Llc_at k t1 /\ Llc_at k t2
  | pterm_abs t1    => Llc_at (S k) t1
  | pterm_sub t1 t2 => False
  | pterm_sub' t1 t2 => False
  end.

Definition Lterm' t := Llc_at 0 t.

Definition Lbody' t := Llc_at 1 t.
