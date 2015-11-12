(********************************************************************************
* Formalization of lambda ex						        *		
*									        *
* Fl\u00e1vio L. C. de Moura & Daniel L. Ventura, & Washington R. Segundo, 2013	*
*********************************************************************************)

Set Implicit Arguments.
Require Import Metatheory LambdaES_Defs LambdaES_Infra LambdaES_FV.
Require Import Rewriting_Defs Rewriting_Lib.
Require Import Equation_C Lambda Lambda_Ex.

(** Basic properties **) 

Lemma basic_prop1 : forall t t', ((t -->ex t') \/ (t -->lex t')) -> (fv t' << fv t).
Proof.
 intros t t' H x; destruct H. 
 assert (Q : red_fv ex).
  apply red_fv_mod_eqC.
  apply sys_x_fv.
 unfold red_fv in Q. 
 apply Q; trivial.
 assert (Q : red_fv lex).
  apply red_fv_mod_eqC.
  apply sys_Bx_fv.
 unfold red_fv in Q. 
 apply Q; trivial.
Qed.

Lemma ex_basic_prop2 : forall t t' u, t -->ex t' -> body u -> 
                        ((u ^^ t) -->ex* (u ^^ t')).
Proof.
 intros t t' u H B; unfold open.
 apply body_size_induction with (t := u); 
 simpl; trivial. apply star_trans_reduction.
 apply one_step_reduction; trivial.
 intro x. apply reflexive_reduction.
 intros t1 B1 H1. apply in_star_abs_ex with (L := (fv t1)).
 intros x Fr. unfold open.
 apply ctx_sys_ex_regular in H. destruct H.
 replace ({0 ~> pterm_fvar x}({1 ~> t}t1)) with
 ({0 ~> t}({1 ~> pterm_fvar x}(& t1))).
 replace ({0 ~> pterm_fvar x}({1 ~> t'}t1)) with
 ({0 ~> t'}({1 ~> pterm_fvar x}(& t1))).
 apply H1 with (t2 := & t1). 
 unfold bswap. rewrite fv_bswap_rec; trivial.
 rewrite (size_bswap_rec 0). reflexivity.
 rewrite body_eq_body'. apply lc_at_open; trivial.
 apply lc_at_bswap; try omega; trivial.
 rewrite subst_com; trivial. rewrite open_bswap; trivial.
 rewrite bswap_rec_id. reflexivity.
 rewrite subst_com; trivial. rewrite open_bswap; trivial.
 rewrite bswap_rec_id. reflexivity.
 intros t1 t2 B1 B2 Ht1 Ht2. 
 apply ctx_sys_ex_regular in H. destruct H.
 apply star_closure_composition with 
 (u := pterm_app ({0 ~> t'}t1) ({0 ~> t}t2)).
 apply left_star_app_ex; trivial. 
 apply body_open_term; trivial.
 apply right_star_app_ex; trivial. 
 apply body_open_term; trivial.
 intros t1 t3 B1 B3 Ht3 Ht1. 
 apply ctx_sys_ex_regular in H. destruct H.
 apply star_closure_composition with 
 (u := ({1 ~> t'}t1 [{0 ~> t}t3])).
 apply left_star_subst_ex with (L := (fv t1)).
 apply body_open_term; trivial.
 intros x Fr. unfold open.
 replace ({0 ~> pterm_fvar x}({1 ~> t}t1)) with
 ({0 ~> t}({1 ~> pterm_fvar x}(& t1))).
 replace ({0 ~> pterm_fvar x}({1 ~> t'}t1)) with
 ({0 ~> t'}({1 ~> pterm_fvar x}(& t1))).
 apply Ht1 with (t2 := & t1). 
 unfold bswap. rewrite fv_bswap_rec; trivial.
 rewrite (size_bswap_rec 0). reflexivity.
 rewrite body_eq_body'. apply lc_at_open; trivial.
 apply lc_at_bswap; try omega; trivial.
 rewrite subst_com; trivial. rewrite open_bswap; trivial.
 rewrite bswap_rec_id. reflexivity.
 rewrite subst_com; trivial. rewrite open_bswap; trivial.
 rewrite bswap_rec_id. reflexivity.
 apply right_star_subst_ex; trivial. rewrite body_eq_body'. 
 apply lc_at_open; trivial.
Qed.
 
 
Lemma lex_basic_prop2 : forall t t' u, t -->lex t' -> body u -> 
                        ((u ^^ t) -->lex* (u ^^ t')).
Proof.
 intros t t' u H B; unfold open.
 apply body_size_induction with (t := u); 
 simpl; trivial. apply star_trans_reduction.
 apply one_step_reduction; trivial.
 intro x. apply reflexive_reduction.
 intros t1 B1 H1. apply in_star_abs_lex with (L := (fv t1)).
 intros x Fr. unfold open.
 apply ctx_sys_Bex_regular in H. destruct H.
 replace ({0 ~> pterm_fvar x}({1 ~> t}t1)) with
 ({0 ~> t}({1 ~> pterm_fvar x}(& t1))).
 replace ({0 ~> pterm_fvar x}({1 ~> t'}t1)) with
 ({0 ~> t'}({1 ~> pterm_fvar x}(& t1))).
 apply H1 with (t2 := & t1). 
 unfold bswap. rewrite fv_bswap_rec; trivial.
 rewrite (size_bswap_rec 0). reflexivity.
 rewrite body_eq_body'. apply lc_at_open; trivial.
 apply lc_at_bswap; try omega; trivial.
 rewrite subst_com; trivial. rewrite open_bswap; trivial.
 rewrite bswap_rec_id. reflexivity.
 rewrite subst_com; trivial. rewrite open_bswap; trivial.
 rewrite bswap_rec_id. reflexivity.
 intros t1 t2 B1 B2 Ht1 Ht2. 
 apply ctx_sys_Bex_regular in H. destruct H.
 apply star_closure_composition with 
 (u := pterm_app ({0 ~> t'}t1) ({0 ~> t}t2)).
 apply left_star_app_lex; trivial. 
 apply body_open_term; trivial.
 apply right_star_app_lex; trivial. 
 apply body_open_term; trivial.
 intros t1 t3 B1 B3 Ht3 Ht1. 
 apply ctx_sys_Bex_regular in H. destruct H.
 apply star_closure_composition with 
 (u := ({1 ~> t'}t1 [{0 ~> t}t3])).
 apply left_star_subst_lex with (L := (fv t1)).
 apply body_open_term; trivial.
 intros x Fr. unfold open.
 replace ({0 ~> pterm_fvar x}({1 ~> t}t1)) with
 ({0 ~> t}({1 ~> pterm_fvar x}(& t1))).
 replace ({0 ~> pterm_fvar x}({1 ~> t'}t1)) with
 ({0 ~> t'}({1 ~> pterm_fvar x}(& t1))).
 apply Ht1 with (t2 := & t1). 
 unfold bswap. rewrite fv_bswap_rec; trivial.
 rewrite (size_bswap_rec 0). reflexivity.
 rewrite body_eq_body'. apply lc_at_open; trivial.
 apply lc_at_bswap; try omega; trivial.
 rewrite subst_com; trivial. rewrite open_bswap; trivial.
 rewrite bswap_rec_id. reflexivity.
 rewrite subst_com; trivial. rewrite open_bswap; trivial.
 rewrite bswap_rec_id. reflexivity.
 apply right_star_subst_lex; trivial. rewrite body_eq_body'. 
 apply lc_at_open; trivial.
Qed.

Lemma ex_basic_prop3 : forall t t' u L, term u -> 
                       (forall x, x \notin L -> (t ^ x) -->ex (t' ^ x)) ->    
                       ((t ^^ u) -->ex (t' ^^ u)).
Proof.
 intros t t' u L T H. 
 case var_fresh with (L := L \u (fv t) \u (fv t')).
 intros x Fr. apply notin_union in Fr. destruct Fr.
 apply notin_union in H0. destruct H0.
 case (H x); trivial; clear H.
 intros t0 H. case H; clear H; intros t1 H. 
 destruct H. destruct H3. 
 exists ((close t0 x) ^^ u) ((close t1 x) ^^ u). split.
 apply ctx_sys_x_regular in H3.
 apply eqC_open_var with (x := x); trivial. 
 apply fv_close'. rewrite H.
 rewrite <- (open_close_var x). reflexivity. apply H3. split. 
 clear H H1 H2 H4 t t'.
 gen_eq t : (close t0 x).  gen_eq t' : (close t1 x).
 intros H1 H2. 
 replace t0 with (t ^ x) in H3. replace t1 with (t' ^ x) in H3.
 rewrite subst_intro with (x := x).
 rewrite subst_intro with (x := x) (t := t').
 apply ctx_sys_x_red_out; trivial.  
 rewrite H1; apply fv_close'. rewrite H2; apply fv_close'.
 rewrite H1. rewrite open_close_var with (x := x); trivial.
 apply ctx_sys_x_regular in H3. apply H3. 
 rewrite H2. rewrite open_close_var with (x := x); trivial.
 apply ctx_sys_x_regular in H3. apply H3. 
 apply ctx_sys_x_regular in H3. apply eqC_sym.
 apply eqC_open_var with (x := x); trivial. 
 apply fv_close'. rewrite <- H4.
 rewrite <- (open_close_var x). reflexivity. apply H3. 
Qed.



Lemma lex_basic_prop3: forall t t' u L, term u -> 
                        (forall x, x \notin L -> (t ^ x) -->lex (t' ^ x)) -> 
                        ((t ^^ u) -->lex (t' ^^ u)).
Proof.
 intros t t' u L T H. 
 case var_fresh with (L := L \u (fv t) \u (fv t')).
 intros x Fr. apply notin_union in Fr. destruct Fr.
 apply notin_union in H0. destruct H0.
 case (H x); trivial; clear H.
 intros t0 H. case H; clear H; intros t1 H. 
 destruct H. destruct H3. 
 exists ((close t0 x) ^^ u) ((close t1 x) ^^ u). split.
 apply ctx_sys_Bx_regular in H3.
 apply eqC_open_var with (x := x); trivial. 
 apply fv_close'. rewrite H.
 rewrite <- (open_close_var x). reflexivity. apply H3. split. 
 clear H H1 H2 H4 t t'.
 gen_eq t : (close t0 x).  gen_eq t' : (close t1 x).
 intros H1 H2. 
 replace t0 with (t ^ x) in H3. replace t1 with (t' ^ x) in H3.
 rewrite subst_intro with (x := x).
 rewrite subst_intro with (x := x) (t := t').
 apply ctx_sys_Bx_red_out; trivial.  
 rewrite H1; apply fv_close'. rewrite H2; apply fv_close'.
 rewrite H1. rewrite open_close_var with (x := x); trivial.
 apply ctx_sys_Bx_regular in H3. apply H3. 
 rewrite H2. rewrite open_close_var with (x := x); trivial.
 apply ctx_sys_Bx_regular in H3. apply H3. 
 apply ctx_sys_Bx_regular in H3. apply eqC_sym.
 apply eqC_open_var with (x := x); trivial. 
 apply fv_close'. rewrite <- H4.
 rewrite <- (open_close_var x). reflexivity. apply H3. 
Qed.

Lemma ex_basic_prop4 : forall x t u, SN ex (t ^^ u) -> 
                                     term u -> (x \notin fv t) -> 
                                     SN ex (t ^ x).
Proof.
 intros x t u H0 T H1. unfold SN in H0. case H0; clear H0.
 intros n H0. exists n. generalize t H1 H0. clear H0 H1 t.
 induction n. intros. apply NF_to_SN0. apply SN0_to_NF in H0. unfold NF in *|-*.
 intros t' H2. gen_eq t0 : (close t' x). intro H3. replace t' with (t0 ^ x) in H2.
 assert (Q: (t ^^ u) -->ex (t0 ^^ u)).
   apply ex_basic_prop3 with (L := (fv t) \u (fv t0)); trivial.
   intros z H4. apply notin_union in H4. destruct H4.
   apply ctx_sys_ex_red_rename with (x := x); trivial.
   rewrite H3. apply fv_close'.
 assert (Q': ~ (t ^^ u) -->ex (t0 ^^ u)).
   apply H0.
 contradiction. rewrite H3. rewrite open_close_var with (x := x).
 reflexivity. apply  ctx_sys_ex_regular in H2. apply H2.
 intros. destruct H0. apply SN_intro. intros. exists n. split; try omega.
 gen_eq t0 : (close t' x). intro H2.
 replace t' with (t0 ^ x). replace t' with (t0 ^ x) in H0.
 apply IHn; trivial. rewrite H2. apply fv_close'. case (H (t0 ^^ u)); trivial.
 apply ex_basic_prop3 with (L := (fv t) \u (fv t0)); trivial.
 intros z H3. apply notin_union in H3. 
 apply ctx_sys_ex_red_rename with (x := x); trivial.
 rewrite H2. apply fv_close'. intros k H3. apply WSN with (k := k); try omega.
 apply H3. rewrite H2. rewrite open_close_var with (x := x); trivial.
 apply ctx_sys_ex_regular in H0. apply H0. rewrite H2.
 rewrite open_close_var with (x := x); trivial.
 apply ctx_sys_ex_regular in H0. apply H0.
Qed.

Lemma lex_basic_prop4 : forall x t u, SN lex (t ^^ u) -> 
                                      term  u -> (x \notin fv t) -> 
                                      SN lex (t ^ x).
Proof.
 intros x t u H0 T H1. unfold SN in H0. case H0; clear H0.
 intros n H0. exists n. generalize t H1 H0. clear H0 H1 t.
 induction n. intros. apply NF_to_SN0. apply SN0_to_NF in H0. unfold NF in *|-*.
 intros t' H2. gen_eq t0 : (close t' x). intro H3. replace t' with (t0 ^ x) in H2.
 assert (Q: (t ^^ u) -->lex (t0 ^^ u)).
   apply lex_basic_prop3 with (L := (fv t) \u (fv t0)); trivial.
   intros z H4. apply notin_union in H4. destruct H4.
   apply ctx_sys_lex_red_rename with (x := x); trivial.
   rewrite H3. apply fv_close'.
 assert (Q': ~ (t ^^ u) -->lex (t0 ^^ u)).
   apply H0.
 contradiction. rewrite H3. rewrite open_close_var with (x := x).
 reflexivity. apply  ctx_sys_Bex_regular in H2. apply H2.
 intros. destruct H0. apply SN_intro. intros. exists n. split; try omega.
 gen_eq t0 : (close t' x). intro H2.
 replace t' with (t0 ^ x). replace t' with (t0 ^ x) in H0.
 apply IHn; trivial. rewrite H2. apply fv_close'. case (H (t0 ^^ u)); trivial.
 apply lex_basic_prop3 with (L := (fv t) \u (fv t0)); trivial.
 intros z H3. apply notin_union in H3. 
 apply ctx_sys_lex_red_rename with (x := x); trivial.
 rewrite H2. apply fv_close'. intros k H3. apply WSN with (k := k); try omega.
 apply H3. rewrite H2. rewrite open_close_var with (x := x); trivial.
 apply ctx_sys_Bex_regular in H0. apply H0. rewrite H2.
 rewrite open_close_var with (x := x); trivial.
 apply ctx_sys_Bex_regular in H0. apply H0.
Qed.
