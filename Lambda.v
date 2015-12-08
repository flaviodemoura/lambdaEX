(*******************************************************************************************
* Formalization of lambda						                   *	
*									                   *
* Brian Aydemir & Arthur Chargu\u00e9raud, July 2007                             	   *
* Fl\u00e1vio L. C. de Moura & Daniel L. Ventura, 2012                                     *
* Fl\u00e1vio L. C. de Moura & Daniel L. Ventura & Washington R. Segundo, 2013       *
********************************************************************************************)

Set Implicit Arguments.
Require Import Metatheory LambdaES_Defs LambdaES_Infra LambdaES_FV.
Require Import Rewriting_Defs Rewriting_Lib.
Require Import List.

(** The beta rule of the lambda calculus. **)
Inductive rule_beta : pterm -> pterm -> Prop :=
   reg_rule_beta : forall (t u:pterm),  Lbody t -> Lterm u ->  
     rule_beta (pterm_app (pterm_abs t) u) (t^^u).

Definition Beta t u := (L_contextual_closure rule_beta) t u.
Notation "t -->Beta u" := (Beta t u) (at level 66).

Definition Beta_trs t u := trans_closure Beta t u.
Notation "t -->Beta+ u" := (Beta_trs t u) (at level 66).

Definition Beta_str t u := star_closure Beta t u.
Notation "t -->Beta* u" := (Beta_str t u) (at level 66).

(* ********************************************************************** *)
(** Properties of the  beta relation **)


Lemma L_beta_regular : L_red_regular rule_beta.
Proof. 
 intros_all. induction H. split.
 apply Lterm_app; trivial. inversion H. 
 apply Lterm_abs with (L := x); trivial.
 apply Lbody_open_term; trivial. 
Qed.

Lemma L_beta_red_out : L_red_out rule_beta.
Proof.
 intros_all. destruct H0. simpl.
 assert (Q : term u). apply Lterm_is_term; trivial.
 rewrite subst_open; trivial.
 apply reg_rule_beta; trivial.
 unfold Lbody in *|-*. case H0; clear H0.
 intros L H0. exists (L \u {{x}}).
 intros x1 H2. apply notin_union in H2. destruct H2.
 apply notin_singleton in H3. rewrite subst_open_var; trivial.
 apply subst_Lterm; trivial. apply H0; trivial. Print subst_Lterm.
 apply subst_Lterm; trivial. 
Qed.


Lemma beta_rename : red_rename rule_beta.
Proof.
 apply L_red_out_to_rename.
 apply L_beta_red_out.
Qed.

(******)

Lemma left_trans_app_Beta: forall t u v,  Lterm t  ->   
      u -->Beta+ v -> pterm_app u t -->Beta+ pterm_app v t.
Proof. 
  intros.
  apply trs_Lctx_app_left; assumption.
Qed.

Lemma left_star_app_Beta: forall t u v,  Lterm t  ->   
      u -->Beta* v -> pterm_app u t -->Beta* pterm_app v t.
Proof.
  intros; apply str_Lctx_app_left; trivial. 
Qed.
  
Lemma right_trans_app_Beta: forall t u v,  Lterm t  ->   
      u -->Beta+ v -> pterm_app t u -->Beta+ pterm_app t v.
Proof.
   intros; apply trs_Lctx_app_right; trivial. 
Qed.

Lemma right_star_app_Beta: forall t u v,  Lterm t  ->   
      u -->Beta* v -> pterm_app t u -->Beta* pterm_app t v.
Proof.
   intros; apply str_Lctx_app_right; trivial. 
Qed.

Lemma in_trans_abs_Beta: forall L u v,  (forall x, x \notin L -> (u ^ x) -->Beta+ (v ^ x)) -> 
  ((pterm_abs u) -->Beta+ (pterm_abs v)).
Proof.
 intros; apply trs_Lctx_abs_in with (L := L); trivial.
 apply L_beta_regular.
 apply L_beta_red_out.
Qed.

Lemma in_star_abs_Beta: forall L u v,  (forall x, x \notin L -> (u ^ x) -->Beta* (v ^ x)) -> 
  ((pterm_abs u) -->Beta* (pterm_abs v)).
Proof.
 intros; apply str_Lctx_abs_in with (L := L); trivial.
 apply L_beta_regular.
 apply L_beta_red_out.
Qed.


(** Inductive Characterisation of NF Beta **)

Lemma NF_ind_eq_Beta : forall t, Lterm t -> (NF_ind Beta t <-> NF Beta t).
Proof.
 intros. split. 
 intro H'. induction H'.
 induction l; simpl in *|-*.
 intros t H2. inversion H2. inversion H3.
 intros t H2. inversion H2. inversion H3.
 case eqdec_nil with (l := l). intro. rewrite H11 in H6. simpl in H6.
 generalize H6. discriminate.
 intro H11. case  m_app_eq_app with (t := (pterm_fvar x)) (lu := l); trivial.
 intros t2 H12. case H12; clear H12; intros t3 H12. 
 generalize H6. rewrite H12. discriminate.
 unfold NF in IHl. apply IHl with (t' := t'). inversion H. trivial.
 intros u' H'. apply H0. right; trivial.
 intros u' H8 Tu' t1.  apply H1; trivial. right; trivial. trivial.
 unfold NF in H1. apply H1 with (u := a) (t' := u').
 left; trivial. inversion H; trivial. trivial.
 intros t' H2. inversion H2. inversion H3. inversion H.
 unfold NF in H1. case var_fresh with (L := L \u L0 \u L1).
 intros x Fr. apply notin_union in Fr. destruct Fr. apply notin_union in H8; destruct H8.
 apply H1 with (x := x) (t' := t'0 ^x); trivial. 
 apply H7; trivial. apply H4; trivial. 
 assert (Reg : L_red_regular rule_beta). apply L_beta_regular.
 assert (Out : L_red_out rule_beta). apply L_beta_red_out.
 apply Lterm_size_induction3 with (t := t); trivial; intros.
 apply NF_ind_app; intros.
 apply H0; trivial. rewrite NF_eq_SN0 in H1|-*. apply L_SN_mult_app in H1; trivial.
 destruct H1. rewrite <- P_list_eq with (P := SN_ind 0 (L_contextual_closure rule_beta)) in H3.
 apply H3; trivial.  rewrite <- P_list_eq with (P := Lterm). intros. 
 apply H0; trivial. case eqdec_nil with (l := l); intro.
 rewrite H4 in *|-*. simpl in *|-*. unfold Lbody in H1.
 case H1; clear H1; intros L H1. apply NF_ind_abs with (L := fv t1 \u L).
 intros x Fr. apply notin_union in Fr. destruct Fr. apply H2; trivial.
 apply H1; trivial. rewrite NF_eq_SN0 in H3. apply L_SN_abs with (x := x) in H3; trivial.
 rewrite <- NF_eq_SN0 in H3. trivial. 
 apply False_ind. case not_nil_append with (l := l); trivial.
 intros t0 H5. case H5; clear H5; intros l' H5.  rewrite H5 in H3.
 rewrite <- mult_app_append in H3. unfold NF in H3. apply (H3 ((t1 ^^ t0) // l')).
 apply Lctx_red_h_mult_app. rewrite <- P_list_eq with (P := Lterm). intros.
 apply H0. rewrite H5. apply in_or_app. left; trivial.
 apply L_redex. apply reg_rule_beta; trivial. unfold body. unfold Lbody in H1.
 case H1; clear H1; intros L H1. apply H0. rewrite H5.
 apply in_or_app. right. simpl. left; trivial.
Qed.


(** Inductive Characterisation of SN Beta **)

 Inductive SN_Beta : pterm -> Prop :=


  | sn_beta_var : forall (x : var) (lu : list pterm),

                      (forall u, (In u lu) -> SN_Beta u) ->
(*-------------------------------------------------------------------------*)
                         SN_Beta ((pterm_fvar x) // lu)


  | sn_beta_abs : forall L (u : pterm),

                      (forall x, x \notin L -> SN_Beta (u ^ x))-> 
(*-------------------------------------------------------------------------*)
                             SN_Beta (pterm_abs u)

 
  | sn_beta_meta_sub : forall  (t u : pterm) (lv : list pterm),

                          SN_Beta u -> SN_Beta ((t ^^ u) // lv) ->
(*-------------------------------------------------------------------------*)
                    SN_Beta ((pterm_app (pterm_abs t)  u) // lv)
.  

Theorem SN_Beta_prop : forall t, Lterm t -> SN Beta t -> SN_Beta t.
Proof.
 intros t T. 

 intro H. case H; clear H; intros n H. 
 generalize t T H; clear T t H. induction n; intros.
 rewrite <- NF_eq_SN0 in H. rewrite <- NF_ind_eq_Beta in H; trivial.
 induction H. apply sn_beta_var; intros.
 apply H0; trivial. rewrite Lterm_mult_app in T. destruct T.
 rewrite <- P_list_eq in H3. apply H3; trivial.
 inversion T; clear T. apply sn_beta_abs with (L := L \u L0); intros.
 apply notin_union in H3. destruct H3. apply H0; trivial. apply H2; trivial.
 assert (Reg : L_red_regular rule_beta); try apply L_beta_regular.
 assert (Out : L_red_out rule_beta); try apply  L_beta_red_out.
 generalize H; clear H. apply Lterm_size_induction3 with (t := t); intros; trivial. 
 apply sn_beta_var; intros.
 assert (Q : SN_ind (S n) Beta  %% l). 
    apply L_SN_mult_app in H0; trivial. apply H0. 
    rewrite <- P_list_eq with (P := Lterm).      
    intros u' H2. apply H; trivial.  
 apply H; trivial. rewrite <- P_list_eq with (P := SN_ind (S n) Beta) in Q.
 apply Q; trivial. 
 case eqdec_nil with (l := l). 
 intro H3. rewrite H3 in *|-*. simpl in *|-*. clear H H3.
 inversion H0; clear H0.
 apply sn_beta_abs  with (L := fv t1 \u x). intros y Fr.
 apply notin_union in Fr. destruct Fr.
 apply H1; trivial. apply H; trivial. apply L_SN_abs; trivial.
 intro H3. case not_nil_append with (l := l); trivial.
 intros a Hl. case Hl; clear Hl. intros l' Hl.
 rewrite Hl in *|-*. rewrite <- mult_app_append in *|-*.
 clear H3 Hl. 
 assert (Tl : Lterm a /\ Lterm %% l').
   split. apply H. apply in_or_app. right. 
   simpl; left; trivial.
   apply P_list_eq with (P := Lterm).
   intros u Hu. apply H. apply in_or_app. left.
   trivial.  
 destruct Tl. apply sn_beta_meta_sub. apply H.
 apply in_or_app. simpl. right. left; trivial.
 apply L_SN_mult_app in H2; trivial. destruct H2. apply L_SN_app in H2; trivial.
 destruct H2; trivial.
 inversion H0. apply Lterm_abs with (L := x); intros. 
 apply H6; trivial.  apply Lterm_app. inversion H0. apply Lterm_abs with (L := x); intros. 
 apply H5; trivial. trivial. apply IHn. rewrite  Lterm_mult_app. split; trivial.
 apply Lbody_open_term; trivial.
 apply SN_one_step with (t := pterm_app (pterm_abs t1) a // l'); trivial.
 apply Lctx_red_h_mult_app; trivial. apply L_redex. apply reg_rule_beta.
 unfold Lbody in H0. case H0; clear H0; intros L H0. exists L. intros.
 apply H0; trivial. trivial.
Qed.

