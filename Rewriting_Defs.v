(***************************************************************************
* Formalization of ES calculi						   *
*									   *
* General rewriting definitions	for explicit substitutions		   * 
*									   *
* Fabien Renaud & St\u00e9phane Zimmerman, 2011				   *
* Flavio L. C. de Moura & Daniel L. Ventura & Washington R. Segundo, 2014  *
***************************************************************************)

Require Import Metatheory.
Require Import LambdaES_Defs.
Require Import LambdaES_Infra.
Require Import LambdaES_FV.
Require Import List.

(** Given a relation Red, constructs its contextual closure *)
Inductive contextual_closure (Red : pterm -> pterm -> Prop) : pterm -> pterm -> Prop :=
  | redex : forall t s, Red t s -> contextual_closure Red t s
  | app_left : forall t t' u, term u -> contextual_closure Red t t' -> 
	  		contextual_closure Red (pterm_app t u) (pterm_app t' u)
  | app_right : forall t u u', term t -> contextual_closure Red u u' -> 
	  		contextual_closure Red (pterm_app t u) (pterm_app t u')
  | abs_in : forall t t' L, (forall x, x \notin L -> contextual_closure Red (t^x) (t'^x)) -> contextual_closure Red (pterm_abs t) (pterm_abs t')
  | subst_left : forall t t' u L, term u -> 
	  	(forall x, x \notin L -> contextual_closure Red (t^x) (t'^x)) -> 
	        contextual_closure Red  (pterm_sub t u) (pterm_sub t' u)
  | subst_right : forall t u u', body t -> contextual_closure Red u u' -> 
	  	contextual_closure Red  (pterm_sub t u) (pterm_sub t u') 
.


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
	      p_contextual_closure Red  (pterm_sub t u) (pterm_sub t' u')
.


(** Given a relation Red, constructs the parallel contextual closure
fr labelled terms. *)
(*
Inductive p_lab_contextual_closure (Red : pterm -> pterm -> Prop) : 
                                    pterm -> pterm -> Prop :=
  | p_lab_redex : forall t s, Red t s -> p_lab_contextual_closure Red t s
  | p_lab_app : forall t t' u u', p_lab_contextual_closure Red t t' -> 
                              p_lab_contextual_closure Red u u' ->
	  		      p_lab_contextual_closure Red (pterm_app t u) (pterm_app t' u')
  | p_lab_abs_in : forall t t' L, (forall x, x \notin L -> 
                              p_lab_contextual_closure Red (t^x) (t'^x)) -> 
                              p_lab_contextual_closure Red (pterm_abs t) (pterm_abs t')
  | p_lab_subst : forall t t' u u' L, (forall x, x \notin L -> 
                                   p_lab_contextual_closure Red (t^x) (t'^x)) -> 
                                   p_lab_contextual_closure Red u u' -> 
	                           p_lab_contextual_closure Red (t[u]) (t'[u'])
  | p_lab_subst' : forall t t' u u' L, (forall x, x \notin L -> 
                                   p_lab_contextual_closure Red (t^x) (t'^x)) -> 
                                   u =e u' -> 
	                           p_lab_contextual_closure Red (t[[u]]) (t'[[u']])
. 
*)

Hint Constructors contextual_closure.

(** Given a relation Red, constructs its transitive closure *)
Inductive trans_closure (Red : pterm -> pterm -> Prop) : pterm -> pterm -> Prop :=
  | one_step_reduction : forall t u, Red t u -> trans_closure Red t u
  | transitive_reduction : forall t u v, Red t u -> trans_closure Red u v -> trans_closure Red t v
.

(** Given a relation Red, constructs its reflexive closure *)
Inductive star_closure (Red : pterm -> pterm -> Prop) : pterm -> pterm -> Prop :=
  | reflexive_reduction : forall t, star_closure Red t t
  | star_trans_reduction : forall t u, trans_closure Red t u -> star_closure Red t u 
.


(* ********************************************************************** *)
(** Properties of relations *)

Definition red_regular (R : pterm -> pterm -> Prop) :=
  forall t t', R t t' -> term t /\ term t'.

Definition red_regular' (R : pterm -> pterm -> Prop) :=
  forall t t', R t t' -> (term t <-> term t').

Definition red_refl (R : pterm -> pterm -> Prop) :=
  forall t, term t -> R t t.

Definition red_in (R : pterm -> pterm -> Prop) :=
  forall t x u u', term t -> R u u' ->
  R ([x ~> u]t) ([x ~> u']t).
 
Definition red_all (R : pterm -> pterm -> Prop) :=
  forall x t t', R t t' -> 
  forall u u', R u u' -> 
  R ([x~>u]t) ([x~>u']t').

Definition red_out (R : pterm -> pterm -> Prop) :=
  forall x u t t', term u -> R t t' -> 
  R ([x~>u]t) ([x~>u]t').

Definition red_out' (R : pterm -> pterm -> Prop) :=
  forall x y t t', R t t' -> 
  R ([x~>pterm_fvar y]t) ([x~>pterm_fvar y]t').

Definition red_rename (R : pterm -> pterm -> Prop) :=
  forall x t t' y,
  x \notin (fv t) -> x \notin (fv t') ->
  R (t ^ x) (t' ^ x) -> 
  R (t ^ y) (t' ^ y).

Definition red_rename' (R : pterm -> pterm -> Prop) :=
  forall x t t' y,
  x \notin (fv t) -> x \notin (fv t') ->
  y \notin (fv t) -> y \notin (fv t') ->
  R (t ^ x) (t' ^ x) -> 
  R (t ^ y) (t' ^ y).

Definition red_swap (R : pterm -> pterm -> Prop) :=
  forall x t t' y,
  R t t' ->
  R ([(x,y)]t) ([(x,y)]t').

Definition red_through (R : pterm -> pterm -> Prop) :=
  forall x t1 t2 u1 u2, 
  x \notin (fv t1) -> x \notin (fv u1) ->
  R (t1 ^ x) (u1 ^ x) -> R t2 u2 ->
  R (t1 ^^ t2) (u1 ^^ u2).

Definition red_not_fv (R: pterm -> pterm -> Prop) :=
  forall x t t', R t t' ->
  x \notin (fv t) -> x \notin (fv t'). 

Definition red_fv (R: pterm -> pterm -> Prop) :=
  forall x t t', R t t' ->
  x \in (fv t') -> x \in (fv t). 

Definition L_red_regular (R : pterm -> pterm -> Prop) :=
  forall t t', R t t' -> Lterm t /\ Lterm t'.

Definition L_red_regular' (R : pterm -> pterm -> Prop) :=
  forall t t', R t t' -> (Lterm t <-> Lterm t').

Definition L_red_refl (R : pterm -> pterm -> Prop) :=
  forall t, Lterm t -> R t t.

Definition L_red_in (R : pterm -> pterm -> Prop) :=
  forall t x u u', Lterm t -> R u u' ->
  R ([x ~> u]t) ([x ~> u']t).

Definition L_red_out (R : pterm -> pterm -> Prop) :=
  forall x u t t', Lterm u -> R t t' -> 
  R ([x~>u]t) ([x~>u]t').

(** maybe realocate  begin *)
(** Reduction on lists **)

Definition R_list (R : pterm -> pterm -> Prop) (l : list pterm) (l' : list pterm) := 
exists t, exists t', exists l0, exists l1, l = (l0 ++ t :: l1) /\ l' = (l0 ++ t' :: l1) /\ R t t'.

Lemma R_list_h: forall (R : pterm -> pterm -> Prop) a b lt, 
                R a b -> R_list R (a :: lt) (b :: lt).   
Proof.
 intros. unfold R_list. exists a. exists b. exists (nil (A := pterm)). exists lt.
 simpl. split; trivial; split; trivial.
Qed.

Lemma R_list_t: forall (R : pterm -> pterm -> Prop) a lt lt', 
                (R_list R lt lt') -> R_list R (a :: lt) (a :: lt').
Proof.
 unfold R_list. intros.
 case H; clear H. intros b H.
 case H; clear H. intros b' H.
 case H; clear H. intros l H.
 case H; clear H. intros l' H.
 destruct H. destruct H0. 
 rewrite H. rewrite H0.
 exists b. exists b'. 
 exists (a :: l). exists l'. simpl.
 split; trivial. split; trivial.
Qed.

Lemma term_mult_app : forall t lu, term (t // lu) <-> term t /\ (term %% lu).
Proof.
 intros t lu. induction lu; simpl; split; 
 intro H;  try apply H; try split; trivial.
 apply term_distribute_over_application in H. 
 apply IHlu. apply H.
 apply term_distribute_over_application in H.
 split. apply H. apply IHlu. apply H.
 apply term_distribute_over_application. split.
 apply IHlu. split; apply H. apply H.
Qed.

Lemma Lterm_mult_app : forall t lu, Lterm (t // lu) <-> Lterm t /\ (Lterm %% lu).
Proof.
 intros t lu. induction lu; simpl; split; 
 intro H;  try apply H; try split; trivial.
 inversion H. apply IHlu; trivial.
 inversion H. split; trivial. apply IHlu; trivial.
 destruct H. destruct H0. apply Lterm_app; trivial.
 apply IHlu; split; trivial.
Qed.


Lemma ctx_red_t_mult_app : forall R t lu lu', term t -> term %% lu -> R_list (contextual_closure R) lu lu' -> (contextual_closure R) (t // lu) (t // lu').
Proof.
 intros R t lu lu' Tt Tlu H. unfold R_list in H. 
 case H; clear H; intros t0 H.
 case H; clear H; intros t1 H.
 case H; clear H; intros l0 H.
 case H; clear H; intros l1 H.
 destruct H. destruct H0. 
 rewrite H. rewrite H0. rewrite H in Tlu. 
 clear H H0. induction l0; simpl. destruct l1; simpl. 
 apply app_right; trivial.
 apply app_right; trivial. 
 simpl in Tlu. rewrite term_distribute_over_application.
 rewrite term_mult_app. destruct Tlu. destruct H0.
 split; trivial. split; trivial.
 simpl in Tlu. destruct Tlu. 
 apply app_left; trivial.
 apply IHl0; trivial. 
Qed.



 