(***************************************************************************
* Formalizing SN for lambda_ex						   *		
*									   *
* Definitions of explicit substitutions 				   *
* Brian Aydemir & Arthur Chargueraud, July 2007              	   	   *
* Fabien Renaud, 2011							   *
* Flávio L. C. de Moura, 2016                                              *
***************************************************************************)

Set Implicit Arguments.
Require Import Metatheory.

(** Pre-terms are expressions arbitrarily built from the following constructors: *)
Inductive pterm : Set :=
  | pterm_bvar : nat -> pterm
  | pterm_fvar : var -> pterm
  | pterm_app  : pterm -> pterm -> pterm
  | pterm_abs  : pterm -> pterm
  | pterm_sub : pterm -> pterm -> pterm 
  | pterm_lsub : pterm -> pterm -> pterm.
(** Bound and free variables have different constructors. In fact, [pterm_bvar] will be used to represent bound variables that are codified by deBruijn indexes. Free variables are represented with names, so the free variable x will be denoted by [pterm_fvar x]. The constructor [pterm_app] and [pterm_abs] are used respectively for representing applications and abstractions. Explicit substitutions appear in two flavors: with or without marks. Therefore, [pterm_sub t u] represents the term [t] with an explicit substitution [u], while [pterm_lsub t u] is the constructor for labeled substitutions. The adopted notations for explicit substitutions are as follows: *)

Notation "t [ u ]" := (pterm_sub t u) (at level 70).
Notation "t [[ u ]]" := (pterm_lsub t u) (at level 70).

(** Opening up abstractions and substitutions *)
Fixpoint open_rec (k : nat) (u : pterm) (t : pterm) {struct t} : pterm :=
  match t with
  | pterm_bvar i    => if k === i then u else (pterm_bvar i)
  | pterm_fvar x    => pterm_fvar x
  | pterm_app t1 t2 => pterm_app (open_rec k u t1) (open_rec k u t2)
  | pterm_abs t1    => pterm_abs (open_rec (S k) u t1)
  | pterm_sub t1 t2 => pterm_sub (open_rec (S k) u t1) (open_rec k u t2)
  | pterm_lsub t1 t2 => pterm_lsub (open_rec (S k) u t1) (open_rec k u t2)
  end.

Definition open t u := open_rec 0 u t.

Notation "{ k ~> u } t" := (open_rec k u t) (at level 67).
Notation "t ^^ u" := (open t u) (at level 67). 
Notation "t ^ x" := (open t (pterm_fvar x)).   

(** Variable closing *)
Fixpoint close_rec  (k : nat) (x : var) (t : pterm) {struct t} : pterm :=
  match t with
  | pterm_bvar i    => pterm_bvar i
  | pterm_fvar x'    => if x' == x then (pterm_bvar k) else pterm_fvar x'
  | pterm_app t1 t2 => pterm_app (close_rec k x t1) (close_rec k x t2)
  | pterm_abs t1    => pterm_abs (close_rec (S k) x t1)
  | pterm_sub t1 t2 => pterm_sub (close_rec (S k) x t1) (close_rec k x t2)
  | pterm_lsub t1 t2 => pterm_lsub (close_rec (S k) x t1) (close_rec k x t2)
  end.

Definition close t x := close_rec 0 x t.

Fixpoint fv (t : pterm) {struct t} : vars :=
  match t with
  | pterm_bvar i    => {}
  | pterm_fvar x    => {{x}}
  | pterm_app t1 t2 => (fv t1) \u (fv t2)
  | pterm_abs t1    => (fv t1)
  | pterm_sub t1 t2 => (fv t1) \u (fv t2)
  | pterm_lsub t1 t2 => (fv t1) \u (fv t2)
  end.

  
Fixpoint bswap_rec (k : nat) (t : pterm) {struct t} : pterm :=
  match t with
  | pterm_bvar i    => if k === i then (pterm_bvar (S k))
                       else (if (S k) === i then (pterm_bvar k) else (pterm_bvar i))
  | pterm_fvar x    => pterm_fvar x
  | pterm_app t1 t2 => pterm_app (bswap_rec k t1) (bswap_rec k t2)
  | pterm_abs t1    => pterm_abs (bswap_rec (S k) t1)
  | pterm_sub t1 t2 => pterm_sub (bswap_rec (S k) t1) (bswap_rec k t2)
  | pterm_lsub t1 t2 => pterm_lsub (bswap_rec (S k) t1) (bswap_rec k t2)
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
  | pterm_lsub t1 t2 => pterm_lsub (swap x y t1) (swap x y t2)
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
 | pterm_lsub t1 t2 => 1 + (pterm_size t1) + (pterm_size t2)
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

(** Implicit substitution, for free names *)
Fixpoint m_sb (z : var) (u : pterm) (t : pterm) : pterm :=
  match t with
  | pterm_bvar i    => pterm_bvar i
  | pterm_fvar x    => if x == z then u else (pterm_fvar x)
  | pterm_abs t1    => pterm_abs (m_sb z u t1)
  | pterm_app t1 t2 => pterm_app (m_sb z u t1) (m_sb z u t2)
  | pterm_sub t1 t2 => pterm_sub (m_sb z u t1) (m_sb z u t2)
  | pterm_lsub t1 t2 => pterm_lsub (m_sb z u t1) (m_sb z u t2)
  end.
Notation "[ z ~> u ] t" := (m_sb z u t) (at level 62).

(** ES terms are expressions without dangling deBruijn indexes. *)
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
  intros t Ht. destruct t. inversion Ht.
  simpl; auto.  
  simpl; auto.  
  simpl. omega.
  simpl. omega.
  simpl. omega. inversion Ht.
Qed.  

(** Body *) 
Definition body t := exists L, forall x, x \notin L -> term (t ^ x).

Hint Constructors term.

(** Pure lambda terms. *)
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

Lemma Lterm_size_non_null : forall t, Lterm t -> pterm_size t > 0.
Proof.
  intros t Ht. destruct t.
  inversion Ht.
  simpl; auto.  
  simpl. omega.
  simpl. omega. inversion Ht. inversion Ht.
Qed.  

(** Body for pure lambda terms *) 
Definition Lbody t := exists L, forall x, x \notin L -> Lterm (t ^ x).

Hint Constructors Lterm.

