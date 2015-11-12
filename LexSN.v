(********************************************************************************
* Formalization of lambda ex						        *		
*									        *
* Fl\u00e1vio L. C. de Moura & Daniel L. Ventura, & Washington R. Segundo, 2013	*
*********************************************************************************)

Set Implicit Arguments.
Require Import Metatheory LambdaES_Defs LambdaES_Infra LambdaES_FV.
Require Import Rewriting_Defs Rewriting_Lib.
Require Import Equation_C Lambda Lambda_Ex.
Require Import Basic_Prop_lex.
(*Require Import IE_Property.*)


(** Full Composition **)

Lemma full_comp: forall t u, body t -> term u ->  
                t[u] -->ex+ (t ^^ u). 
Proof.
 intros t u H0. generalize H0.
 apply body_size_induction with (t := t); simpl; trivial. 
 (* bvar *)
 intros B T.
 unfold open; simpl.
 apply one_step_reduction.
 apply ctx_to_mod_eqC.
 apply redex. apply reg_rule_var; trivial. 
 (* fvar *)
 intros x B T.
 unfold open; simpl.
 apply one_step_reduction.
 apply ctx_to_mod_eqC. 
 apply redex. apply reg_rule_gc; trivial.
 (* abs *) 
 intros t1 B Ht1 H T.
 unfold open in *|-*; simpl.
 apply transitive_reduction with 
 (u := pterm_abs ((& t1) [u])).
 apply ctx_to_mod_eqC.  
 apply redex. apply reg_rule_lamb; trivial.
 apply in_trans_abs_ex with (L := (fv t1)). 
 intros x Fr. unfold open; simpl.
 replace ({0 ~> pterm_fvar x}u) with u. 
 rewrite subst_com  with (i := 0) (j := 1) (u := pterm_fvar x) (v := u) (t := t1); trivial.
 rewrite open_bswap; trivial.
 apply Ht1 with (t2 := & t1) (x := x); trivial.
 unfold bswap; rewrite fv_bswap_rec with (n := 0); trivial.
 rewrite size_bswap_rec with (n := 0); trivial.
 rewrite body_eq_body'; apply lc_at_open; trivial. apply lc_at_bswap; try omega; trivial.
 rewrite body_eq_body'; apply lc_at_open; trivial. apply lc_at_bswap; try omega; trivial.
 apply open_rec_term  with (k := 0) (t := u) (u := pterm_fvar x); trivial.
 (* app *) 
 intros t1 t2 B1 B2 IHt1 IHt2 H T.
 apply body_distribute_over_application in H.
 case H; clear H; intros Ht1 Ht2.
 apply transitive_reduction with (u := pterm_app (t1[u]) (t2[u])).
 apply ctx_to_mod_eqC. apply redex. apply reg_rule_app; trivial.
 apply transitive_closure_composition with (u := pterm_app ({0 ~> u}t1) (t2[u])).
 apply left_trans_app_ex. 
 apply body_to_subs; trivial. apply IHt1; trivial. unfold open; simpl.
 apply right_trans_app_ex. 
 apply body_open_term; trivial. apply IHt2; trivial.
 (* sub *) 
 intros t1 t2 B1 B2 IHt2 IHt1 H T.
 unfold open in *|-*. simpl.
 case var_fresh with (L := fv t2). 
 intros y Fr. case fv_in_or_notin with (t := t2 ^ y) (x := y).
   (* y \in fv (t2 ^ t) *)
   intro Hy.
   apply transitive_reduction with (u := (& t1)[u][ t2[ u ] ]).
   apply ctx_to_mod_eqC. apply redex.
   apply reg_rule_comp; trivial. intro T'.
   apply term_eq_term' in T'. unfold term' in T'. 
   generalize T'; clear T'. 
   apply not_body_term_fvar with (x := y); trivial.
   rewrite body_eq_body' in B2. unfold body' in B2. trivial.
   apply transitive_closure_composition with (u := (& t1 [u]) [{0 ~> u}t2]).
   apply right_trans_subst_ex. 
   rewrite body_eq_body'. unfold body'.
   simpl. apply term_is_a_body in T.
   rewrite body_eq_body' in H. unfold body' in H.
   simpl in H. split. unfold bswap.
   apply lc_at_bswap; try omega. apply H.
   rewrite <- body_eq_body'; trivial.
   apply IHt2; trivial.
   apply left_trans_subst_ex with (L:= fv (& t1)).
   apply body_open_term; trivial.
   intros x Fr'. unfold open. simpl.
   replace ({0 ~> pterm_fvar x}u) with u.
   rewrite subst_com with (i := 0) (j := 1) (u := pterm_fvar x) (v := u) (t := t1); trivial.
   rewrite open_bswap; trivial.
   rewrite body_eq_body' in H. unfold body' in H. simpl in H.
   apply IHt1 with (t2 := & t1) (x := x); trivial.
   rewrite size_bswap_rec with (n := 0); trivial.
   unfold bswap. rewrite body_eq_body'. unfold body'.
   apply lc_at_open; trivial. apply lc_at_bswap; try omega; trivial.
   unfold bswap. rewrite body_eq_body'. unfold body'.
   apply lc_at_open; trivial. apply lc_at_bswap; try omega; trivial.
   apply open_rec_term  with (k := 0) (t := u) (u := pterm_fvar x); trivial.
   (* y \notin fv (t2 ^ t) *)
   intro Hy. assert (T' : term t2).
   rewrite term_eq_term'. unfold term'. 
   apply body_term_fvar with (x := y); trivial.
   rewrite body_eq_body' in B2. unfold body' in B2. trivial.
   replace ({0 ~> u}t2) with t2. 
   (**)
   rewrite eqC_redex; trivial.
   (**)
   apply left_trans_subst_ex with (L:= fv (& t1)); trivial. 
   intros x Fr'. unfold open. simpl.
   replace ({0 ~> pterm_fvar x}u) with u.
   rewrite subst_com with (i := 0) (j := 1) (u := pterm_fvar x) (v := u) (t := t1); trivial.
   rewrite open_bswap; trivial.
   rewrite body_eq_body' in H. unfold body' in H. simpl in H.
   apply IHt1 with (t2 := & t1) (x := x); trivial.
   rewrite size_bswap_rec with (n := 0); trivial.
   unfold bswap. rewrite body_eq_body'. unfold body'.
   apply lc_at_open; trivial. apply lc_at_bswap; try omega; trivial.
   unfold bswap. rewrite body_eq_body'. unfold body'.
   apply lc_at_open; trivial. apply lc_at_bswap; try omega; trivial.
   apply open_rec_term  with (k := 0) (t := u) (u := pterm_fvar x); trivial.
   apply open_rec_term with (k := 0) (t := t2) (u := u); trivial.
Qed.


(** Simulating One-Step Beta-Reduction **)

Lemma sim_beta_reduction : forall t t', t -->Beta t' -> t -->lex* t'.
Proof.
 intros t t' H. induction H.
 destruct H. apply star_trans_reduction.
 apply transitive_reduction with (u := t[u]).
 apply ctx_to_mod_eqC.
 apply redex. apply B_lx. apply reg_rule_b; trivial.
 apply Lbody_is_body; trivial. apply Lterm_is_term; trivial.
 apply trs_ex_to_lex.
 apply full_comp; trivial. 
 apply Lbody_is_body; trivial. apply Lterm_is_term; trivial.
 apply left_star_app_lex; trivial. apply Lterm_is_term; trivial.
 apply right_star_app_lex; trivial. apply Lterm_is_term; trivial.
 apply in_star_abs_lex with (L := L); trivial.
Qed.


(** Perpetuality **)

Inductive many_step : pterm -> pterm -> Prop :=

  | p_var : forall (x : var) (t t' : pterm) (lu lv : list pterm), 

               ((NF lex) %% lu) -> many_step t t' -> 
(*-------------------------------------------------------------------------*)
    many_step ((pterm_app ((pterm_fvar x) // lu) t) // lv) ((pterm_app ((pterm_fvar x) // lu) t') // lv)  

 
  | p_abs : forall L (t t' : pterm),

            (forall x, x \notin L ->  many_step (t ^ x) (t' ^ x)) ->
(*-------------------------------------------------------------------------*)
                    many_step (pterm_abs t) (pterm_abs t')  


  | p_B : forall  (t u : pterm) (lu : list pterm),
(*-------------------------------------------------------------------------*)
           many_step ((pterm_app (pterm_abs t) u) // lu) (t[u] // lu) 


  | p_subst1 : forall (t u : pterm) (lu : list pterm),

                              SN lex u ->
(*-------------------------------------------------------------------------*)
                 many_step (t[u] // lu) ((t ^^ u) // lu) 


  | p_subst2 : forall  (t u u' : pterm) (lu : list pterm),

                   (~ SN lex u) -> many_step u u' ->
(*-------------------------------------------------------------------------*)
                 many_step (t[u] // lu) (t[u'] // lu) .


Notation "t ~> t'" := (many_step t t') (at level 66).


Lemma perp_proposition : forall t t', term t -> (t ~> t') -> (t -->lex+ t').
Proof.
 intros t t' T H. generalize T. clear T. induction H; simpl; intro T.
 apply term_mult_app in T. destruct T. 
 apply term_distribute_over_application in H1. destruct H1.
 apply left_trans_m_app_lex; trivial.
 apply right_trans_app_lex; trivial. 
 apply IHmany_step; trivial.
 apply in_trans_abs_lex with (L := L \u (fv t)).
 intros x Fr. apply notin_union in Fr. destruct Fr. apply H0; trivial.
 apply body_to_term; trivial. apply term_abs_to_body; trivial.
 apply term_mult_app in T. destruct T.
 apply term_distribute_over_application in H. destruct H.
 apply left_trans_m_app_lex; trivial.
 apply one_step_reduction. apply ctx_to_mod_eqC. apply redex. apply B_lx.
 apply reg_rule_b; trivial. apply term_abs_to_body; trivial.
 apply term_mult_app in T. destruct T. apply subs_to_body in H0. destruct H0.
 apply left_trans_m_app_lex; trivial. 
 apply trs_ex_to_lex. apply full_comp; trivial.
 apply term_mult_app in T. destruct T. apply subs_to_body in H1. destruct H1.
 apply left_trans_m_app_lex; trivial.
 apply right_trans_subst_lex; trivial. 
 apply IHmany_step; trivial.
Qed.


(** The determinism of the many step strategy **)

Lemma det_many_step : forall t u v, term t -> ((t ~> u) /\ (t ~> v) -> u = v).
Proof.
 intros t u v T H. destruct H. generalize v H0; clear v H0.
 induction H; intros.   

 inversion H1. 
 assert (T' : term (pterm_app (pterm_fvar x0 // lu0) t0 // lv0)).
  rewrite H2. trivial.
 apply term_mult_app in T. apply term_mult_app in T'.
 destruct T. destruct T'. inversion H6. inversion H8.
 apply term_mult_app in H12. apply term_mult_app in H16.
 clear t1 t2 t3 t4 H1 H5 H6 H8 H10 H11 H14 H15.
 destruct H12. destruct H16. clear H1 H6.
 rewrite mult_app_append' in H2. rewrite mult_app_append' in H2.
 apply mult_app_var_inj in H2. destruct H2. rewrite H1.
 rewrite mult_app_append'. rewrite mult_app_append'. 
 fequals. clear x x0 v H1. generalize H0 H4. intros H0' H4'. 
 apply perp_proposition in H0'; trivial.
 apply perp_proposition in H4'; trivial.
 apply P_eq_app_list with (P := NF lex) in H2; trivial.
 destruct H2. destruct H2. rewrite H1. rewrite H6.
 rewrite IHmany_step with (v := t'0); trivial. rewrite <- H2; trivial.
 intro. unfold NF in H1. destruct H4'; apply H1 with (t' := u); trivial.
 intro. unfold NF in H1. destruct H0'; apply H1 with (t' := u); trivial.

 rewrite mult_app_append' in H2. apply False_ind. 
 replace (pterm_abs t0) with (pterm_abs t0 // nil) in H2.
 symmetry in H2. generalize H2.
 apply mult_app_diff_var_abs. simpl; trivial.
 rewrite mult_app_append in H3. rewrite mult_app_append' in H3.
 symmetry in H3. apply False_ind. generalize H3.
 apply mult_app_diff_var_abs. 
 rewrite mult_app_append' in H2. symmetry in H2. apply False_ind.
 generalize H2. apply mult_app_diff_var_sub.
 rewrite mult_app_append' in H2. symmetry in H2. apply False_ind.
 generalize H2. apply mult_app_diff_var_sub. 

 inversion H1. 
 rewrite mult_app_append' in H2. apply False_ind. 
 replace (pterm_abs t) with (pterm_abs t // nil) in H2.
 generalize H2. apply mult_app_diff_var_abs. simpl; trivial.
 pick_fresh z. apply notin_union in Fr. destruct Fr.
 apply notin_union in H5. destruct H5.
 apply notin_union in H5. destruct H5.
 apply notin_union in H5. destruct H5.
 apply notin_union in H5. destruct H5. 
 apply notin_union in H5. destruct H5.
 assert (Q :  t' ^ z = t'0 ^ z). apply H0; trivial. 
 apply body_to_term; trivial. apply term_abs_to_body; trivial. 
 apply H3; trivial.  apply open_var_inj with (x := z) in Q; trivial.
 rewrite Q; trivial. rewrite mult_app_append in H3.  
 replace (pterm_abs t) with (pterm_abs t // nil) in H3.
 apply mult_app_abs_inj in H3. destruct H3. destruct lu; simpl in H4;
 inversion H4. simpl; trivial. 
 replace (pterm_abs t) with (pterm_abs t // nil) in H2. apply False_ind.
 symmetry in H2. generalize H2. apply mult_app_diff_abs_sub. simpl; trivial.
 replace (pterm_abs t) with (pterm_abs t // nil) in H2. apply False_ind.
 symmetry in H2. generalize H2. apply mult_app_diff_abs_sub. simpl; trivial.

 inversion H0. 
 rewrite mult_app_append' in H. rewrite mult_app_append in H.
 apply False_ind. generalize H. apply mult_app_diff_var_abs.  
 rewrite mult_app_append in H. replace (pterm_abs t0) with (pterm_abs t0 // nil) in H.  
 apply mult_app_abs_inj in H. destruct H. destruct lu.
 simpl in H3. inversion H3. simpl in H3. inversion H3. simpl. trivial.
 rewrite mult_app_append in H1. rewrite mult_app_append in H1.
 apply mult_app_abs_inj in H1. destruct H1. apply app_inj_tail in H1.
 destruct H1. rewrite H. rewrite H1. rewrite H3. trivial.
 rewrite mult_app_append in H. symmetry in H. apply False_ind. 
 generalize H. apply mult_app_diff_abs_sub.
 rewrite mult_app_append in H. symmetry in H. apply False_ind. 
 generalize H. apply mult_app_diff_abs_sub.

 inversion H0. 
 rewrite mult_app_append' in H1. apply False_ind. 
 generalize H1. apply mult_app_diff_var_sub.
 replace (pterm_abs t0) with (pterm_abs t0 // nil) in H1. 
 apply False_ind. generalize H1. apply mult_app_diff_abs_sub. simpl. trivial.
 rewrite mult_app_append in H2. apply False_ind. 
 generalize H2. apply mult_app_diff_abs_sub.
 apply mult_app_sub_inj in H1. destruct H1. destruct H4. 
 rewrite H1. rewrite H4. rewrite H5. trivial.
 apply mult_app_sub_inj in H1. destruct H1. destruct H5. 
 rewrite H5 in H2. contradiction.

 inversion H1. 
 rewrite mult_app_append' in H2. apply False_ind.
 generalize H2. apply mult_app_diff_var_sub.
 replace (pterm_abs t0) with (pterm_abs t0 // nil) in H2. apply False_ind.
 generalize H2. apply mult_app_diff_abs_sub. simpl; trivial.
 rewrite mult_app_append in H3. apply False_ind.
 generalize H3. apply mult_app_diff_abs_sub.
 apply mult_app_sub_inj in H2. destruct H2. destruct H5. 
 rewrite H5 in H3. contradiction.
 apply mult_app_sub_inj in H2. destruct H2. destruct H6.
 rewrite H2. rewrite H7. rewrite IHmany_step with (v := u'0); trivial.
 apply term_mult_app in T. destruct T. inversion H8; trivial.
 rewrite <- H6; trivial.
Qed.


Theorem perpetuality : forall t t', term t -> (t ~> t') -> SN lex t' -> SN lex t.
Proof.
 intros t t' T H. induction H.

 (* p-var *) 
 apply term_mult_app in T. destruct T.
 apply term_distribute_over_application in H1. destruct H1.
 apply term_mult_app in H1. destruct H1. clear H1. intro H1.
 assert (Q : SN lex t).
  apply IHmany_step; trivial. case H1; clear H1. intros n H1.
  exists n. generalize H1; clear H1.
  generalize t'. clear H0 H3 IHmany_step t t'. induction n.
  intros t' H3. apply NF_to_SN0. unfold NF.
  intros t0 H1. apply SN0_to_NF in H3. unfold NF in H3.
  apply H3 with (t'0 := (pterm_app (pterm_fvar x // lu) t0 // lv)).
  apply left_m_app_lex; trivial. apply right_app_lex; trivial.
  apply term_mult_app; split; trivial.
  intros t' H'. apply SN_intro. intros t'' H''. exists n; split; try omega.
  apply IHn. inversion H'. case (H0 (pterm_app (pterm_fvar x // lu) t'' // lv)).
  apply left_m_app_lex; trivial. apply right_app_lex; trivial.
  apply term_mult_app; split; trivial. intros k Hk. destruct Hk.
  apply WSN with (k := k); try omega; trivial.
 clear IHmany_step.
 assert (Q' : SN lex %% lv).
  apply perp_proposition in H0; trivial.
  assert (Q'' : term t').
   apply transitive_star_derivation' in H0.
   case H0; clear H0. intro H0. apply ctx_sys_Bex_regular in H0. apply H0.
   intro H0. case H0; clear H0. intros u H0. destruct H0. case H5; clear H5.
   intros u' H5. destruct H5. apply ctx_sys_Bex_regular in H6. apply H6. 
  case H1; clear H1; intros n H1. rewrite SN_list. exists n.
  apply eqC_SN_app_list in H1. apply H1. apply sys_Bx_regular.
  apply term_distribute_over_application. split; trivial. rewrite term_mult_app.
  split; trivial. trivial.
 clear H0 H1. replace (pterm_app (pterm_fvar x // lu) t // lv) with ((pterm_fvar x) // (lv ++ t :: lu)).
 apply SN_mult_app_var. clear H Q Q' t'. induction lv; simpl. 
 split; trivial. simpl in H2. destruct H2. split; trivial. apply IHlv; trivial. induction lv; simpl.
 split; trivial. rewrite SN_list. exists 0. rewrite <- NF_eq_SN0_list; trivial. simpl in Q'. destruct Q'.
 split; trivial. simpl in H2. destruct H2. apply IHlv; trivial. induction lv; simpl; trivial.
 simpl in H2. simpl in Q'. destruct H2. destruct Q'. rewrite IHlv; trivial.

 (* p_abs *)
 intro H'. 
 assert (Q : red_regular sys_Bx); try apply sys_Bx_regular.
 assert (Q' : red_out sys_Bx); try apply sys_Bx_red_out.
 case var_fresh with (L := L \u (fv t) \u (fv t')).
 intros x Fr. apply notin_union in Fr. destruct Fr. apply notin_union in H1. destruct H1.
 apply term_abs_to_body in T. case (H0 x); trivial. apply body_to_term; trivial.
 unfold SN in H'. case H'; clear H'; intros n H'. 
 apply eqC_SN_abs with (x := x) in H'; trivial. exists n. apply H'; trivial.
 intros n H4. exists n. apply lex_SN_abs with (L := {{x}} \u (fv t)); trivial.
 intros x' Fr. apply lex_SN_ind_rename with (x := x); trivial.

 (* p_B *)
 intro H. case H; clear H. intros n H. exists (S n).
 rewrite term_mult_app in T. destruct T. rewrite term_distribute_over_application in H0.
 destruct H0. apply term_abs_to_body in H0. 
 generalize t u lu H0 H1 H2 H. clear t u lu H0 H1 H2 H. induction n; simpl.
 intros t u lu H H0 H1 H2. apply SN_intro. intros t' H'. exists 0; split; try omega; trivial.
 apply lex_mult_app_B in H'. generalize H2. intro H''. rewrite <- NF_eq_SN0 in H2.
 case H'; clear H'; intro H'. rewrite H'. trivial.
 case H'; clear H'; intro H'; case H'; clear H'.
 intros L H'. case H'; clear H'; intros t0 H'. destruct H'.
 apply False_ind. apply (H2 ((t0 [u]) // lu)).
 apply red_h_mult_app; trivial. apply left_subst_lex with (L := L); trivial.
 intro H'; case H'; clear H'; intros u' H'. destruct H'.
 apply False_ind. apply (H2 ((t [u']) // lu)).
 apply red_h_mult_app; trivial. apply right_subst_lex; trivial.
 intro H'; case H'; clear H'; intros lv' H'. destruct H'.
 apply False_ind. apply (H2 ((t [u]) // lv')). 
 apply red_t_mult_app; trivial. apply body_to_subs; trivial.
 intros t u lu H H0 H1 H2. apply SN_intro. intros t' H'. exists (S n); split; try omega.
 generalize H2. intro H3. destruct H3. apply lex_mult_app_B in H'.
 case H'; clear H'; intro H'. rewrite H'. trivial.
 case H'; clear H'; intro H'; case H'; clear H'.
 intros L H'. case H'; clear H'; intros t0 H'. destruct H'.
 rewrite H4. apply IHn; trivial. case var_fresh with (L := fv t0 \u L).
 intros x Fr.  apply notin_union in Fr. destruct Fr. 
 assert (Q : t ^ x -->lex t0 ^ x). apply (H5 x); trivial.
 apply ctx_sys_Bex_regular in Q. destruct Q. rewrite term_eq_term' in H9.
 rewrite body_eq_body'. unfold term' in H9. unfold body'. unfold open in H9.
 rewrite lc_at_open with (u := pterm_fvar x); trivial.
 case (H3 ((t0 [u]) // lu)); clear H3. apply red_h_mult_app; trivial.
 apply left_subst_lex with (L := L); trivial. intros k H6.
 destruct H6. apply WSN with (k := k); try omega; trivial.
 intro H'; case H'; clear H'; intros u' H'. destruct H'.
 rewrite H4. apply IHn; trivial. 
 apply ctx_sys_Bex_regular in H5. apply H5. case (H3 ((t [u']) // lu)).
 apply red_h_mult_app; trivial. apply right_subst_lex; trivial.
 intros k H6. destruct H6. apply WSN with (k := k); try omega; trivial.
 intro H'; case H'; clear H'; intros lv' H'. destruct H'.
 rewrite H4. apply IHn; trivial. apply lex_R_list_regular in H5; apply H5; trivial.
 case (H3 ((t [u]) // lv')).
 apply red_t_mult_app; trivial. apply body_to_subs; trivial.
 intros k H6. destruct H6. apply WSN with (k := k); try omega; trivial.

 (* p_subst1 *)
 rewrite term_mult_app in T. destruct T. apply subs_to_body in H0. destruct H0.
 apply IE_property; trivial.

 (* p_subst2 *) 
 intro H1. rewrite term_mult_app in T. destruct T. apply subs_to_body in H2. destruct H2.
 case H1; clear H1; intros n H1.
 assert (Tu' : term u').
  apply perp_proposition in H0; trivial. 
  apply transitive_star_derivation' in H0. case H0; clear H0.
  intro H5. apply ctx_sys_Bex_regular in H5. apply H5.
  intro H5; case H5; clear H5; intros u0 H5. destruct H5. 
  case H5; clear H5; intros u1 H5. destruct H5.
  apply ctx_sys_Bex_regular in H6. apply H6. 
 apply eqC_SN_app_list in H1; trivial. destruct H1.
 assert (Q : SN_ind n (red_ctx_mod_eqC sys_Bx) u').
  case var_fresh with (L := (fv t)). intros x Fr.
  case (eqC_SN_sub x n sys_Bx t u'); trivial.
  apply sys_Bx_regular. apply sys_Bx_red_out. 
 assert (Q' : SN lex u).
  apply IHmany_step; trivial. exists n. apply Q.
 contradiction. apply sys_Bx_regular. apply body_to_subs; trivial.
Qed.

(** Inductive Characterisation of NF lex **)

Lemma NF_ind_eq_lex : forall t, term t -> (NF_ind lex t <-> NF lex t).
Proof.
 split; intros. induction H0. 
 apply NF_mult_app_var. apply P_list_eq. 
 intros. apply H1; trivial. apply term_mult_app in H.
 destruct H. apply P_list_eq with (P := term) (l := l); trivial.
 unfold NF. intros. intro H2. apply lex_abs in H2.
 case H2; clear H2. intros L' H2. case H2; clear H2. intros t0 H2.
 destruct H2. case var_fresh with (L := L \u L' \u (fv t)).
 intros z Fr. apply notin_union in Fr. destruct Fr.
 apply notin_union in H4. destruct H4.
 unfold NF in H1. apply (H1 z) with (t' := t0 ^ z); trivial.
 apply body_to_term; trivial. apply term_abs_to_body; trivial.
 apply H3; trivial. 
 Definition P (t : pterm) := NF lex t -> NF_ind lex t.
 assert (Q : term t ->  P t).
  clear H H0. 
(**)
  apply term_size_induction3; unfold P; intros.
(**)
  apply NF_ind_app. intros. apply H; trivial. 
  assert (H' : term %% l).
    apply P_list_eq with (P := term) (l := l).
    intros. apply H; trivial.
  clear H.
  induction l. simpl in H1. contradiction. 
  simpl in H1. destruct H1. simpl in H0.
  rewrite <- H. clear H. intros a' H. 
  apply (H0 (pterm_app (pterm_fvar x // l) a')).
  apply right_app_lex; trivial. 
  simpl in H'. destruct H'. apply term_mult_app.
  split; trivial. simpl in *|-*.
  destruct H'. apply IHl; trivial.
  intros u' H'. apply (H0 (pterm_app u' a)).
  apply left_app_lex; trivial.
  case eqdec_nil with (l := l). intro Hl.
  rewrite Hl in *|-*; simpl in *|-*.
  apply NF_ind_abs with (L := fv t1). intros.
  apply H1; trivial. apply body_to_term; trivial.
  intros t' H'. gen_eq t2 : (close t' x).
  intro H''. replace t' with (t2 ^ x) in H'.
  apply (H2 (pterm_abs t2)).
  apply in_abs_lex with (L := (fv t1) \u (fv t2)).
  intros z Hz. apply notin_union in Hz. destruct Hz.
  apply ctx_sys_lex_red_rename with (x := x); trivial.
  rewrite H''. apply fv_close'. rewrite H''.
  rewrite open_close_var with (x := x); trivial.
  apply ctx_sys_Bex_regular in H'. apply H'.
  intro Hl. apply lex_abs_not_NF in H2; trivial.
  contradiction. apply term_mult_app. split.
  apply body_to_term_abs; trivial.
  apply P_list_eq with (P := term).
  intros; apply H; trivial. 
  apply False_ind. 
  apply lex_sub_not_NF' with (t := t1) (u := t3); trivial.
  intros t' H'. apply (H4 (t' // l)). apply left_m_app_lex; trivial.
  apply P_list_eq with (P := term); intros. apply H; trivial.
  unfold P in Q. apply Q; trivial.
Qed.


(** Inductive Characterisation of SN lex **)

 Inductive ISN : pterm -> Prop :=


  | isn_var : forall (x : var) (lu : list pterm),

                     (forall u, (In u lu) -> ISN u) ->
(*-------------------------------------------------------------------------*)
                         ISN ((pterm_fvar x) // lu)


  | isn_NF : forall (u : pterm),

                                NF lex u -> 
(*-------------------------------------------------------------------------*)
                                  ISN u

 
  | isn_app : forall  (u v : pterm) (lu : list pterm),

                      ISN (u[v] // lu) ->
(*-------------------------------------------------------------------------*)
                      ISN ((pterm_app (pterm_abs u)  v) // lu)


  | isn_subs : forall  (u v : pterm) (lu : list pterm),

                  ISN ((u ^^ v) // lu) -> ISN v ->
(*-------------------------------------------------------------------------*)
                       ISN (u[v] // lu)  


  | isn_abs : forall L (u : pterm),

                       (forall x, x \notin L -> ISN (u ^ x)) -> 
(*-------------------------------------------------------------------------*)
                           ISN (pterm_abs u) .  




Lemma ISN_prop : forall t, term t -> (ISN t <-> SN lex t).
Proof.
 intros t T. split. intro H. induction H.
(* -> *)
 (* isn_var *)
 rewrite term_mult_app in T. destruct T. clear H1.
 assert (Q : SN lex %% lu).
  clear H. induction lu; simpl in *|-*; trivial.
  destruct H2. split. apply H0; trivial. left. trivial.
  apply IHlu; trivial. intros u Hu Tu.
  apply H0; trivial. right; trivial.
 apply SN_mult_app_var; trivial. 
 (* isn_NF *)
 exists 0. rewrite <- NF_eq_SN0; trivial.
 (* isn_app *)
 apply perpetuality with (t' := ((u [v]) // lu)); trivial.
 apply p_B. apply IHISN. rewrite term_mult_app in *|-*.
 destruct T. split; trivial. rewrite term_eq_term' in *|-*.
 unfold term' in *|-*. simpl in *|-*. trivial.
 (* isn_subs *)
 generalize T. intro T'. rewrite term_mult_app in T. destruct T.
 apply subs_to_body in H1. destruct H1.
 apply perpetuality with (t' := ((u ^^ v) // lu)); trivial.
 apply p_subst1; trivial. apply IHISN2; trivial. apply IHISN1; trivial.
 rewrite term_mult_app. split; trivial.
 apply body_open_term; trivial.
 (* isn_abs *)
 apply term_abs_to_body in T.
 case var_fresh with (L := L \u fv u). intros x Fr.
 apply notin_union in Fr. destruct Fr.
 case (H0 x); trivial. apply body_to_term; trivial. 
 intros n H3. exists n. apply lex_SN_abs with (L := {{x}} \u (fv u)).
 intros x' Fr. apply lex_SN_ind_rename with (x := x); trivial.
(* <- *)
 intro H. unfold SN in H. case H; clear H; intros n H.
 generalize t T H; clear T t H. induction n; intros.
 apply isn_NF. apply SN0_to_NF. trivial.
 generalize H; clear H.  
 assert (Reg : red_regular sys_Bx).
  apply  sys_Bx_regular.
 assert (Out : red_out sys_Bx).
  apply  sys_Bx_red_out.
 apply term_size_induction3 with (t := t); intros; trivial.
 (* var *)
 apply isn_var; intros.
 assert (Q : SN_ind (S n) lex  %% l). 
    apply eqC_SN_app_list in H0; trivial. apply H0.
    rewrite <- P_list_eq with (P := term).      
    intros u' H2. apply H; trivial.  
 apply H; trivial. rewrite <- P_list_eq with (P := SN_ind (S n) lex) in Q.
 apply Q; trivial. 
 (* abs *)
 case eqdec_nil with (l := l). 
 intro H3. rewrite H3 in *|-*. simpl in *|-*. clear H H3.
 apply isn_abs with (L := fv t1). intros x Fr.
 apply H1; trivial. apply body_to_term; trivial.
 apply eqC_SN_abs; trivial.
 intro H3. case not_nil_append with (l := l); trivial.
 intros a Hl. case Hl; clear Hl. intros l' Hl.
 rewrite Hl in *|-*. rewrite <- mult_app_append in *|-*.
 clear H3 Hl. 
 assert (Tl : term a /\ term %% l').
   split. apply H. apply in_or_app. right. 
   simpl; left; trivial.
   apply P_list_eq with (P := term).
   intros u Hu. apply H. apply in_or_app. left.
   trivial. 
 clear H H1. destruct Tl.
 apply isn_app. apply IHn.
 rewrite term_mult_app. split; trivial.
 apply body_to_subs; trivial.
 apply SN_one_step with (t := pterm_app (pterm_abs t1) a // l'); trivial.
 apply left_m_app_lex; trivial. apply ctx_to_mod_eqC. apply redex.  
 apply B_lx. apply reg_rule_b; trivial.
 (* subs *)
 assert (Tl : term %% l).
   apply P_list_eq with (P := term).
   intros u Hu. apply H; trivial. 
 apply isn_subs.
 apply IHn. apply term_mult_app. split; trivial.
 apply body_open_term; trivial.
 case SN_trs with (n := S n) (R := lex) (t := (t1 [t3]) // l) (u := (t1 ^^ t3) // l); trivial.
 apply left_trans_m_app_lex; trivial.
 apply trs_ex_to_lex. apply full_comp; trivial.
 intros k Hk. destruct Hk. apply WSN with (k := k); try omega; trivial.
 apply eqC_SN_app_list in H4; trivial. destruct H4.
 case var_fresh with (L := (fv t1)). intros x Fr. 
 apply eqC_SN_sub with (x := x) in H4; trivial.
 destruct H4.  apply H1; trivial.
 apply body_to_subs; trivial.
Qed.


(** Finally, the PSN of lex-calculus **)

Theorem PSN : forall t, Lterm t -> SN Beta t -> SN lex t.
Proof.
 intros t T H. 
 rewrite <- ISN_prop. apply SN_Beta_prop in H; trivial.
 induction H; trivial.
 apply isn_var. intros u Hu. rewrite Lterm_mult_app in T.
 destruct T. apply H0; trivial. clear H1 H H0.
 induction lu; simpl in *|-*. contradiction. 
 destruct H2. case Hu. intro H1. rewrite <- H1; trivial. 
 intro H1. apply IHlu; trivial.
 inversion T; clear T.
 apply isn_abs with (L := L \u L0 \u fv u). intros x Fr.
 apply notin_union in Fr. destruct Fr.
 apply notin_union in H3. destruct H3.
 apply H0; trivial. apply H2; trivial.
 apply isn_app; trivial. 
 rewrite Lterm_mult_app in T. destruct T.
 inversion H1; clear H1.
 inversion H5; clear H5.
 apply isn_subs; trivial. 
 apply IHSN_Beta2. rewrite Lterm_mult_app. split; trivial.
 apply Lbody_open_term; trivial.
 unfold Lbody. exists L. apply H7; trivial.
 apply IHSN_Beta1; trivial.
 apply Lterm_is_term; trivial.
Qed.






