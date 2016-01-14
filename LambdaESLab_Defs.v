(********************************************************************************
* Formalization of labelled lambda ex calculus				        *		
*									        *
* Flavio L. C. de Moura & Daniel L. Ventura & Washington R. Segundo, 2014	*
*********************************************************************************)

Set Implicit Arguments.
Require Import Metatheory LambdaES_Defs LambdaES_Infra LambdaES_FV.
Require Import Rewriting_Defs Rewriting_Lib.
Require Import Equation_C Lambda Lambda_Ex.

(*
(** Given a relation Red, constructs its contextual closure just over Lterms *)
Inductive L_contextual_closure (Red : pterm -> pterm -> Prop) : pterm -> pterm -> Prop :=
  | L_redex : forall t s, Red t s -> L_contextual_closure Red t s
  | L_app_left : forall t t' u, Lterm u -> L_contextual_closure Red t t' -> 
	  		L_contextual_closure Red (pterm_app t u) (pterm_app t' u)
  | L_app_right : forall t u u', Lterm t -> L_contextual_closure Red u u' -> 
	  		L_contextual_closure Red (pterm_app t u) (pterm_app t u')
  | L_abs_in : forall t t' L, (forall x, x \notin L -> L_contextual_closure Red (t^x) (t'^x)) 
      -> L_contextual_closure Red (pterm_abs t) (pterm_abs t')
.

(** Given a relation Red, constructs its parallel contextual closure *)
Inductive p_contextual_closure (Red : pterm -> pterm -> Prop) : pterm -> pterm -> Prop :=
  | p_redex : forall t s, Red t s -> p_contextual_closure Red t s
  | p_app : forall t t' u u', p_contextual_closure Red t t' -> p_contextual_closure Red u u' ->
	  		p_contextual_closure Red (pterm_app t u) (pterm_app t' u')
  | p_abs_in : forall t t' L, (forall x, x \notin L -> p_contextual_closure Red (t^x) (t'^x)) -> 
               p_contextual_closure Red (pterm_abs t) (pterm_abs t')
  | p_subst : forall t t' u u' L, (forall x, x \notin L -> p_contextual_closure Red (t^x) (t'^x)) -> 
              p_contextual_closure Red u u' -> 
	      p_contextual_closure Red  (pterm_sub t u) (pterm_sub t' u') .
*)

(** Step 1 *)



(** Grammar of labelled pre-terms. Labelled terms extend the ordinary
 terms with a new constructor for marked explicit substitutions. *)

Inductive lab_term : pterm -> Prop :=
  | lab_term_var : forall x,
      lab_term (pterm_fvar x)
  | lab_term_app : forall t1 t2,
      lab_term t1 -> 
      lab_term t2 -> 
      lab_term (pterm_app t1 t2)
  | lab_term_abs : forall L t1,
      (forall x, x \notin L -> lab_term (t1 ^ x)) ->
      lab_term (pterm_abs t1)
  | lab_term_sub : forall L t1 t2,
     (forall x, x \notin L -> lab_term (t1 ^ x)) ->
      lab_term t2 -> lab_term (t1[t2])
  | lab_term_sub' : forall L t1 t2,
     (forall x, x \notin L -> lab_term (t1 ^ x)) ->
      (term t2) -> (SN lex t2) -> 
      lab_term (t1 [[ t2 ]]).

Definition lab_body (t : pterm) := 
           exists L, forall x, x \notin L -> lab_term (t ^ x).

(** Given a relation Red, constructs the contextual closure for labelled terms. *)

Inductive lab_contextual_closure (Red : pterm -> pterm -> Prop) : pterm -> pterm -> Prop :=
  | lab_redex : forall t s, Red t s -> lab_contextual_closure Red t s
  | lab_app_left : forall t t' u, lab_term u -> lab_contextual_closure Red t t' -> 
	  		lab_contextual_closure Red (pterm_app t u) (pterm_app t' u)
  | lab_app_right : forall t u u', lab_term t -> lab_contextual_closure Red u u' -> 
	  		lab_contextual_closure Red (pterm_app t u) (pterm_app t u')
  | lab_abs_in : forall t t' L, (forall x, x \notin L -> lab_contextual_closure Red (t^x) (t'^x)) 
      -> lab_contextual_closure Red (pterm_abs t) (pterm_abs t')
  | lab_subst_left : forall t t' u L, lab_term u -> 
	  	(forall x, x \notin L -> lab_contextual_closure Red (t^x) (t'^x)) -> 
	        lab_contextual_closure Red  (t[u]) (t'[u])
  | lab_subst_right : forall t u u', lab_body t -> lab_contextual_closure Red u u' -> 
	  	lab_contextual_closure Red  (t[u]) (t[u']) 
  | lab_subst'_left : forall t t' u L, term u -> 
	  	(forall x, x \notin L -> lab_contextual_closure Red (t^x) (t'^x)) -> 
	        lab_contextual_closure Red  (t[[u]]) (t'[[u]])
  | lab_subst'_right : forall t u u', lab_body t -> Red u u' -> 
	  	lab_contextual_closure Red  (t[[u]]) (t[[u']]) 
.

(* ====================================================================== *)
(** ** Alternative definition for local closure *)

(* ********************************************************************** *)
(** Local closure for marked terms. *)

Fixpoint lc_at' (k:nat) (t:pterm) {struct t} : Prop :=
  match t with 
  | pterm_bvar i    => i < k
  | pterm_fvar x    => True
  | pterm_app t1 t2 => lc_at' k t1 /\ lc_at' k t2
  | pterm_abs t1    => lc_at' (S k) t1
  | pterm_sub t1 t2 => (lc_at' (S k) t1) /\ lc_at' k t2
  | pterm_sub' t1 t2 => (lc_at k t2) /\ (SN lex t2) /\ (lc_at' (S k) t1)
  end.

Definition term'' t := lc_at' 0 t.

Definition body'' t := lc_at' 1 t.

(** Labelled lambda ex calculus. There is just one B rule that works
both in the labelled and non-labelled calculus. *)

(** Labelled equations extend the equational system of the unlabelled calculus. *)

Inductive lab_eqc  : pterm -> pterm -> Prop := 
| lab_eqc_eqc: forall t u, eqc t u -> lab_eqc t u
| lab_eqc_rx1 : forall t u v, 
                  lab_term u -> term v -> lab_eqc (t[u][[v]]) ((& t)[[v]][u]) 
| lab_eqc_rx2 : forall t u v, 
                  term u -> lab_term v -> lab_eqc (t[[u]][v]) ((& t)[v][[u]]) 
| lab_eqc_rx3 : forall t u v, 
                  term u -> term v -> lab_eqc (t[[u]][[v]]) ((& t)[[v]][[u]]).

Lemma lab_eqc_refl : forall u, lab_eqc u u.
Proof.
  intro u.
  apply lab_eqc_eqc.
  apply eqc_rf.
Qed.
  
Lemma lab_eqc_sym : forall t u, lab_eqc t u -> lab_eqc u t.
Proof.
  intros t u Heqc.
  destruct Heqc.
  apply lab_eqc_eqc. apply eqc_sym; assumption.
  replace ((t [u]) [[v]]) with (((& (& t)) [u]) [[v]]).
  apply lab_eqc_rx2; assumption.
  rewrite bswap_idemp; trivial.
  replace ((t [[u]]) [v]) with (((& (& t)) [[u]]) [v]).
  apply lab_eqc_rx1; assumption.
  rewrite bswap_idemp; trivial.  
  replace ((t [[u]]) [[v]]) with (((& (& t)) [[u]]) [[v]]).
  apply lab_eqc_rx3; assumption.
  rewrite bswap_idemp; trivial.
Qed.  
  
Lemma lab_eqc_trans : forall t u v, lab_eqc t u -> lab_eqc u v -> lab_eqc t v.
Proof.
  intros t u v Htu Huv.
  destruct Htu.
  destruct Huv.
  apply lab_eqc_eqc.
  apply eqc_trans with t0; assumption.
  assert (lab_eqc ((t0 [u])[[v]]) ((& t0 [[v]])[u])).
  apply lab_eqc_rx1; assumption.
  inversion H; assumption.
  inversion H.
  apply lab_eqc_rx2; assumption.
  inversion H.
  apply lab_eqc_rx3; assumption.
  inversion Huv.
  inversion H1.
  apply lab_eqc_rx1; assumption.
  rewrite bswap_idemp.
  apply lab_eqc_refl.
  inversion Huv.
  inversion H1.
  apply lab_eqc_rx2; assumption.
  rewrite bswap_idemp.
  apply lab_eqc_refl.
  inversion Huv.
  inversion H1.
  apply lab_eqc_rx3; assumption.
  rewrite bswap_idemp.
  apply lab_eqc_refl.
Qed.  
  
Instance lab_eqc_eq : Equivalence lab_eqc.
Proof.
 split; intros_all.
 apply lab_eqc_refl.
 apply lab_eqc_sym; trivial.
 apply lab_eqc_trans with y; assumption.
Qed.

Definition lab_eqC (t: pterm) (u : pterm) :=  trans_closure (lab_contextual_closure lab_eqc) t u . 
Notation "t =~e u" := (lab_eqC t u) (at level 66).

(** =~e is an equivalence relation *)

Lemma lab_eqC_rf : forall t, t =~e t.
Proof.
 intro t. 
 apply one_step_reduction.
 apply lab_redex. reflexivity.
Qed.
   
Lemma lab_ctx_eqc_sym : forall t u, (lab_contextual_closure lab_eqc t u) -> lab_contextual_closure lab_eqc u t. 
Proof.
  intros t u H. induction H.
  apply lab_redex. rewrite H. reflexivity.
  apply lab_app_left; trivial. 
  apply lab_app_right; trivial.
  apply lab_abs_in with L; trivial.
  apply lab_subst_left with (L:=L); trivial.
  apply lab_subst_right; trivial.
  apply lab_subst'_left with L; assumption.
  apply lab_subst'_right; trivial. 
  apply lab_eqc_sym; assumption.
Qed.

Lemma lab_eqC_sym : forall t u, t =~e u -> u =~e t.
Proof.
  intros t u H.
  unfold lab_eqC in *.
  induction H.
  apply one_step_reduction.
  apply lab_ctx_eqc_sym; assumption.
  apply lab_ctx_eqc_sym in H.
  apply (one_step_reduction (lab_contextual_closure lab_eqc)) in H.
  apply transitive_closure_composition with u; assumption.
Qed.  

Lemma lab_eqC_trans : forall t u v, t =~e u -> u =~e v -> t =~e v.
Proof.
 intros t u v H H'.
 apply transitive_closure_composition with (u := u); trivial.
Qed.

Instance lab_eqC_eq : Equivalence lab_eqC.
Proof.
 split; intros_all.
 apply lab_eqC_rf.
 apply lab_eqC_sym; trivial.
 apply lab_eqC_trans with y; trivial.
Qed.



(** TBD:regularity and contextual lemmas are missing. *)

(** Step 2 *)

(** The extended reduction system. This system is used to propagate
terminating labelled substitutions. *)

Inductive lab_sys_x : pterm -> pterm -> Prop :=
| lab_reg_rule_var : forall t, lab_term (pterm_bvar 0 [[t]]) -> lab_sys_x (pterm_bvar 0 [[t]]) t

| lab_reg_rule_gc : forall t u, lab_term t -> lab_term (t[[u]]) -> lab_sys_x (t[[u]]) t

| lab_reg_rule_app : forall t1 t2 u, lab_term (t1[[u]]) -> lab_term (t2[[u]]) ->
  lab_sys_x ((pterm_app t1 t2)[[u]]) (pterm_app (t1[[u]]) (t2[[u]]))

| lab_reg_rule_lamb : forall t u, lab_term ((pterm_abs t)[[u]]) -> 
  lab_sys_x ((pterm_abs t)[[u]]) (pterm_abs ((& t)[[u]]))

| lab_reg_rule_comp : forall t u v, lab_term ((t[u])[[v]]) -> ~ term u -> 
  lab_sys_x (t[u][[v]]) (((& t)[[v]])[u[[v]]]).
Notation "t ->_lab_x u" := (lab_sys_x t u) (at level 59, left associativity).

Inductive lab_sys_lx: pterm -> pterm -> Prop :=
| B_lx : forall t u, t ->_B u -> lab_sys_lx t u
| sys_x_lx : forall t u, t ->_x u -> lab_sys_lx t u
| sys_x_lab_lx : forall t u, t ->_lab_x u -> lab_sys_lx t u.

Definition red_ctx_mod_lab_eqC (R: pterm -> pterm -> Prop) (t: pterm) (u : pterm) := 
           exists t' u', (t =~e t')/\(contextual_closure R t' u')/\(u' =~e u).

Definition lab_ex (t: pterm) (u : pterm) := 
    exists t' u', (t =~e t')/\(lab_contextual_closure lab_sys_x t' u')/\(u' =~e u).

Definition lab_lex (t: pterm) (u : pterm) := 
    exists t' u', (t =~e t')/\(lab_contextual_closure lab_sys_lx t' u')/\(u' =~e u).

Notation "t -->[ex] u" := (lab_ex t u) (at level 59, left associativity).
Notation "t -->[lex] u" := (lab_lex t u) (at level 59, left associativity).

Definition red_lab_regular (R : pterm -> pterm -> Prop) :=
  forall t t',  R t t' -> lab_term t /\ lab_term t'.

Definition red_lab_regular' (R : pterm -> pterm -> Prop) :=
  forall t t',  R t t' -> (lab_term t <-> lab_term t').

(** =~e Rewriting *)

Instance rw_lab_eqC_red : forall R, Proper (lab_eqC ==> lab_eqC ==> iff) (red_ctx_mod_lab_eqC R).
Proof.
  intros_all.
  split.
  intro H1.
  unfold red_ctx_mod_lab_eqC in *.
  destruct H1. destruct H1. destruct H1. destruct H2.
  exists x1. exists x2. split.
  symmetry in H.
  apply lab_eqC_trans with x; assumption.
  split; trivial.
  apply lab_eqC_trans with x0; assumption.
  intro H1.
  unfold red_ctx_mod_lab_eqC in *.
  destruct H1. destruct H1. destruct H1. destruct H2.
  exists x1. exists x2. split. 
  apply lab_eqC_trans with y; assumption.
  split; trivial.
  symmetry in H0.
  apply lab_eqC_trans with y0; assumption.
Qed.  

Instance lab_rw_eqC_trs : forall R, Proper (lab_eqC ==> lab_eqC ==> iff) (trans_closure (red_ctx_mod_lab_eqC R)).
Proof.
  intros_all. split.
  intro H1.
  apply transitive_star_derivation'.
  apply transitive_star_derivation' in H1.
  case H1. clear H1. intro H1. left.
  rewrite H in H1.
  rewrite H0 in H1; assumption.

  intro H2. destruct H2. destruct H2. destruct H3. destruct H3.
  right. rewrite H in *. exists x1. split. assumption.
  exists x2. rewrite H0 in H4.
  split; assumption.

  intro H1.
  apply transitive_star_derivation'.
  apply transitive_star_derivation' in H1.
  case H1.
  clear H1. intro H1. left.
  rewrite <- H in H1.
  rewrite <- H0 in H1; assumption.

  intro H2. destruct H2. destruct H2. destruct H3. destruct H3.
  right. rewrite <- H in *. exists x1. split. assumption.
  exists x2. rewrite <- H0 in H4.
  split; assumption.
Qed.

Instance rw_lab_eqC_lab_body : Proper (lab_eqC ==> iff) lab_body.
Proof.
Admitted.

Instance rw_lab_eqC_term : Proper (lab_eqC ==> iff) lab_term.
Proof.
Admitted.

Instance rw_lab_eqC_fv : Proper (lab_eqC ==> VarSet.Equal) fv.
Proof.
Admitted.

Instance rw_eqC_app : Proper (lab_eqC ++> lab_eqC ++> lab_eqC) pterm_app.
Proof. 
Admitted.
  
Instance rw_lab_eqC_subst_right : forall t, Proper (lab_eqC ++> lab_eqC) (pterm_sub t).
Proof.
Admitted.
  
Instance rw_lab_eqC_lab_subst_right : forall t, Proper (lab_eqC ++> lab_eqC) (pterm_sub' t).
Proof.
Admitted.  
  

  
(** Unlabelled reduction is in the corresponding labelled reduction. *)
Lemma sys_Bx_is_lab_sys_lx: forall t t', t -->lex t' -> t -->[lex] t'.
Proof.

  
(** Unlabelled of S-terms *)
Fixpoint U_lab (t : pterm) : pterm :=
  match t with
  | pterm_bvar i    => pterm_bvar i
  | pterm_fvar x    => pterm_fvar x
  | pterm_app t1 t2 => pterm_app (U_lab t1) (U_lab t2)
  | pterm_abs t1    => pterm_abs (U_lab t1)
  | pterm_sub t1 t2 => pterm_sub (U_lab t1) (U_lab t2)
  | pterm_sub' t1 t2 => pterm_sub (U_lab t1) t2
  end.




(* ********************************************************************** *)
(** pterm lists  properties *)

Fixpoint cr_lc_at_list (n : nat) (l : list pterm) {struct l} : Prop :=
 match l with
 | nil => True
 | t::lu =>  lc_at' n t /\ (cr_lc_at_list (S n) lu) 
 end.

Lemma lc_at_mult_sub : forall n t lu, lc_at' n (t//[lu]) <-> (lc_at' (n + length lu) t /\ cr_lc_at_list n lu).
Proof.
 intros. generalize n; clear n. induction lu; simpl. 
 split. intro. assert (Q : n + 0 = n); try omega. rewrite Q. split; trivial.
 intro. assert (Q : n + 0 = n); try omega. rewrite Q in H. apply H.
 intro n. replace (n + S (length lu)) with ((S n) + length lu). split.
 intro H. destruct H. split. 
 apply IHlu; trivial. split; trivial. apply IHlu; trivial.
 intro H. destruct H. destruct H0. split; trivial. apply IHlu. split; trivial.
 omega.
Qed.


(** Step 3 *)

(** Step 4 *)

