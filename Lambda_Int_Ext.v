Set Implicit Arguments.

Require Import Metatheory LambdaES_Defs LambdaESLab_Defs LambdaES_Infra LambdaES_FV.
Require Import Rewriting_Defs Rewriting_Lib.
Require Import Equation_C Lambda Lambda_Ex.



(*Inductive lab_x_e: pterm -> pterm -> Prop :=*)
(*| xe_left_app : forall t1 t2 t1', *)
        (*lab_term(pterm_app t1 t2) ->*)
        (*t1 ->_Bx t1' ->*)
        (*lab_x_e (pterm_app t1 t2) (pterm_app t1' t2) *)
(*| xe_right_app : forall t1 t2 t2', *)
        (*lab_term(pterm_app t1 t2) ->*)
        (*t2 ->_Bx t2' ->*)
        (*lab_x_e (pterm_app t1 t2) (pterm_app t1 t2') *)
(*| xe_in_lamb : forall t1 t1' L, *)
        (*lab_term (pterm_abs t1) -> *)
        (*(forall x, x \notin L ->  (t1 ^ x) ->_Bx (t1' ^ x)) -> *)
        (*lab_x_e (pterm_abs t1) (pterm_abs t1') *)
(*| xe_in_es_ext : forall t t' u,*)
        (*lab_term (t [u]) ->*)
        (*t ->_Bx t' ->*)
        (*lab_x_e (t [u]) (t' [u])*)
(*| xe_in_es_int : forall t t' u,*)
        (*lab_term (u [t]) ->*)
        (*t ->_Bx t' ->*)
        (*lab_x_e (u [t]) (u [t'])*)
(*| xe_in_les : forall t t' u,*)
        (*lab_term (t [[u]]) ->*)
        (*t ->_Bx t' ->*)
        (*lab_x_e (t [[u]]) (t' [[u]])*)
(*.*)

Inductive ext_lab_contextual_closure (Red : pterm -> pterm -> Prop) : pterm -> pterm -> Prop :=
| lab_redex : forall t s, Red t s -> ext_lab_contextual_closure Red t s
| lab_app_left : forall t t' u, lab_term u -> ext_lab_contextual_closure Red t t' -> 
	  		        ext_lab_contextual_closure Red (pterm_app t u) (pterm_app t' u)
| lab_app_right : forall t u u', lab_term t -> ext_lab_contextual_closure Red u u' -> 
	  		         ext_lab_contextual_closure Red (pterm_app t u) (pterm_app t u')
| lab_abs_in : forall t t' L, (forall x, x \notin L -> ext_lab_contextual_closure Red (t^x) (t'^x)) 
                              -> ext_lab_contextual_closure Red (pterm_abs t) (pterm_abs t')
| lab_subst_left : forall t t' u L, lab_term u -> 
	  	                    (forall x, x \notin L -> ext_lab_contextual_closure Red (t^x) (t'^x)) -> 
	                            ext_lab_contextual_closure Red  (t[u]) (t'[u])
| lab_subst_right : forall t u u', lab_body t -> ext_lab_contextual_closure Red u u' -> 
	  	                   ext_lab_contextual_closure Red  (t[u]) (t[u']) 
| lab_subst'_ext : forall t t' u L, term u -> SN lex u ->
	  	                    (forall x, x \notin L -> ext_lab_contextual_closure Red (t^x) (t'^x)) -> 
	                            ext_lab_contextual_closure Red  (t[[u]]) (t'[[u]])
.

Inductive lab_x_i: pterm -> pterm -> Prop :=
| xi_from_bx_in_les: forall t1 t2 t2', 
                       lab_term (t1 [[ t2 ]]) ->
                       (t2 -->lex t2') ->
                       lab_x_i (t1 [[ t2 ]]) (t1 [[ t2' ]])
| xi_from_x : forall t t', 
                lab_term t ->
                lab_sys_x t t' -> 
                lab_x_i t t'. 

Definition lab_x_i_eq (t: pterm) (u : pterm) := 
    exists t' u', (t =ee t')/\(ext_lab_contextual_closure lab_x_i t' u')/\(u' =ee u).

Definition lab_x_e_eq (t: pterm) (u : pterm) := 
    exists t' u', (t =ee t')/\((ext_lab_contextual_closure sys_Bx) t' u')/\(u' =ee u).

Notation "t -->[lx_i] u" := (lab_x_i_eq t u) (at level 59, left associativity).
Notation "t -->[lx_e] u" := (lab_x_e_eq t u) (at level 59, left associativity).

Lemma lab_sys_x_i_e: forall t t' x x', lab_term t -> (x =~e t) -> (t' =~e x') -> lab_sys_lx t t' -> (x -->[lx_i] x' \/ x -->[lx_e] x').
Proof.
    intros.
    induction H2.  
    constructor 2. exists t u. split*. split. constructor 1. constructor 1. auto. auto. 
    constructor 2. exists t u. split*. split. constructor 1. constructor 2. auto. auto. 
    constructor 1. exists t u. split*. split. constructor 2. auto. constructor 1. auto. auto.
Qed.

Lemma lab_ex_eq_i_e: forall t t', lab_term t -> (t -->[lex] t' <-> (t -->[lx_i] t' \/ t -->[lx_e] t')).
Proof.
    split.
    intro.
    destruct H0.  destruct H0. destruct H0.  destruct H1.
    generalize dependent t.
    generalize dependent t'.
    induction H1. intros.
    apply lab_sys_x_i_e with t0 s; auto. admit.
    Focus 9.


    intros. destruct H0; destruct H0; destruct H0; destruct H0; destruct H1; induction H1.
    exists (t1 [[t2]]) (t1 [[t2']]). split*. split. constructor 8. inversion H1. 
    exists L; auto. inversion H1; auto.  inversion H3. constructor 1; auto.
    constructor 2; auto. auto. 



Qed.
