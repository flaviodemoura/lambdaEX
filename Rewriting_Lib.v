(***************************************************************************
* Formalization of lambda j						   *		
*									   *
* General rewriting lemmas		                                   * 
*									   *
* 			                                                   *
***************************************************************************)

Require Import Metatheory.
Require Import LambdaES_Defs.
Require Import LambdaES_Infra.
Require Import LambdaES_FV.
Require Import Rewriting_Defs.

(** Given a reduction, the composition of two star closure is still a star closure *)

Lemma star_transitive_closure:
    forall (Red: pterm -> pterm -> Prop) (t u v : pterm), 
     Red t u -> star_closure Red u v -> star_closure Red t v.
Proof. 
 intros Red t u v H0 H1.
 induction H1. 
   apply star_trans_reduction.
   apply one_step_reduction.
   assumption.
   apply star_trans_reduction.
   apply transitive_reduction with (u := t0); trivial.
Qed.

Lemma transitive_closure_composition : 
    forall Red t u v, trans_closure Red t u -> trans_closure Red u v -> trans_closure Red t v.
Proof.
  intros.
  induction H.
    apply transitive_reduction with (u := u); trivial.
    apply transitive_reduction with (u := u) ; auto.
Qed.

Lemma star_transitive_closure_composition_1 :
    forall Red t u v, trans_closure Red t u -> star_closure Red u v -> star_closure Red t v.
Proof.
  intros.
  induction H0. 
    apply star_trans_reduction; trivial.
    apply star_trans_reduction.
    apply transitive_closure_composition with (u := t0); trivial.
Qed.
  
Lemma star_transitive_closure_composition_2 :
    forall Red t u v, star_closure Red t u -> trans_closure Red u v -> star_closure Red t v.
Proof.
  intros.
  induction H.
    apply star_trans_reduction; trivial.
    apply star_trans_reduction.
    apply transitive_closure_composition with (u := u); trivial.
Qed.
    


Lemma star_closure_composition:
    forall Red t u v, star_closure Red t u -> star_closure Red u v -> star_closure Red t v.
Proof.
  intros.
  induction H.
  assumption.
  apply star_transitive_closure_composition_1 with (u := u); assumption.
Qed.

Lemma transitive_star_derivation: 
    forall (Red : pterm -> pterm -> Prop) (t v: pterm), 
    trans_closure Red t v -> exists u, Red t u /\  star_closure Red u v.
Proof.
  intros.
  case H. intros t' u' H0.
  exists u'. split; trivial.
  apply reflexive_reduction.
  intros t' u' v' H0 H1. exists u'.
  split; trivial.
  apply star_trans_reduction; trivial.
Qed.

Lemma transitive_star_derivation': 
    forall (Red : pterm -> pterm -> Prop) (t v: pterm), 
    trans_closure Red t v <-> (Red t v \/ (exists u, Red t u /\  (exists u', star_closure Red u u' /\ Red u' v))).
Proof.
 intros. split. intros. destruct H.
 left; trivial. right. exists u. split; trivial. 
 clear H. induction H0. exists t0. split; trivial.
 apply reflexive_reduction. destruct IHtrans_closure.
 exists x. split. apply star_transitive_closure with (u := u); trivial.
 apply H1. apply H1. intros. case H. intro.
 apply one_step_reduction; trivial. intro.
 destruct H0. destruct H0. destruct H1. destruct H1. destruct H1.
 apply transitive_reduction with (u := t0); trivial.
 apply one_step_reduction; trivial.
 apply transitive_reduction with (u := t0); trivial. 
 apply transitive_closure_composition with (u := u); trivial.
 apply one_step_reduction; trivial.
Qed.

Lemma star_transitive_derivation: forall (Red : pterm -> pterm -> Prop) (t u: pterm), 
      star_closure Red t u <-> (t = u \/ trans_closure Red t u).
Proof.
 intros. split. intro. destruct H.
 left. reflexivity. right; trivial.
 intro. case H. 
 clear H. intro H. rewrite H. apply reflexive_reduction.
 clear H. intro H. apply star_trans_reduction; trivial.
Qed.

Lemma contextual_R1_R2: forall (R1 R2: pterm -> pterm -> Prop), 
                           (forall t t', R1 t t' -> R2 t t') -> 
                           (forall t t', contextual_closure R1 t t' -> contextual_closure R2 t t').
Proof.
 intros R1 R2 H t t' H'. induction H'.
 apply redex. apply H; trivial.
 apply app_left; trivial.
 apply app_right; trivial.
 apply abs_in with (L := L); trivial.
 apply subst_left with (L := L); trivial.
 apply subst_right; trivial.
Qed.

Lemma trans_R1_R2 : forall (R1 R2: pterm -> pterm -> Prop), 
                           (forall t t', R1 t t' -> R2 t t') -> 
                           (forall t t', trans_closure R1 t t' -> trans_closure R2 t t').
Proof.
 intros R1 R2 H t t' H'. induction H'.
 apply one_step_reduction. apply H; trivial.
 apply transitive_reduction with (u := u); trivial.
 apply H; trivial.
Qed.

Lemma star_R1_R2: forall (R1 R2: pterm -> pterm -> Prop), 
                           (forall t t', R1 t t' -> R2 t t') -> 
                           (forall t t', star_closure R1 t t' -> star_closure R2 t t').
Proof.
 intros R1 R2 H t t' H'. induction H'.
 apply reflexive_reduction.
 apply star_trans_reduction.
 apply trans_R1_R2 with (R1 := R1); trivial.
Qed.


Lemma ctx_red_h_mult_app : forall R t t' lu, term %% lu -> (contextual_closure R) t t' -> (contextual_closure R) (t // lu) (t' // lu).
Proof.
 intros R t t' lu Tlu H. induction lu; simpl in *|-*; trivial.
 destruct Tlu. apply app_left; trivial.
 apply IHlu; trivial.
Qed.


Lemma Lctx_red_h_mult_app : forall R t t' lu, Lterm %% lu -> (L_contextual_closure R) t t' -> (L_contextual_closure R) (t // lu) (t' // lu).
Proof.
 intros R t t' lu Tlu H. induction lu; simpl in *|-*; trivial.
 destruct Tlu. apply L_app_left; trivial.
 apply IHlu; trivial.
Qed. 

Lemma Lctx_red_t_mult_app : forall R t lu lu', Lterm t -> Lterm %% lu -> R_list (L_contextual_closure R) lu lu' -> (L_contextual_closure R) (t // lu) (t // lu').
Proof.
 intros R t lu lu' Tt Tlu H. unfold R_list in H.
 case H; clear H; intros t0 H.
 case H; clear H; intros t1 H.
 case H; clear H; intros l0 H.
 case H; clear H; intros l1 H.
 destruct H. destruct H0. 
 rewrite H. rewrite H0. rewrite H in Tlu. 
 clear H H0. induction l0; simpl. destruct l1; simpl. 
 apply L_app_right; trivial.
 apply L_app_right; trivial. 
 simpl in Tlu. apply Lterm_app. rewrite Lterm_mult_app. 
 destruct Tlu. destruct H0.
 split; trivial. apply Tlu.
 simpl in Tlu. destruct Tlu. 
 apply L_app_left; trivial.
 apply IHl0; trivial. 
Qed.


(* ********************************************************************** *)
(** Some relations between the properties of relations *)

Lemma red_all_to_out : forall (R : pterm -> pterm -> Prop), 
  red_all R -> red_refl R -> red_out R. 
Proof.
  intros_all. auto*.
Qed.

Lemma red_out_to_out' : forall (R : pterm -> pterm -> Prop),
  red_out R -> red_out' R. 
Proof.
 intros_all. apply H; trivial.
Qed.

Lemma red_out'_to_rename : forall (R : pterm -> pterm -> Prop),
  red_out' R -> red_rename R. 
Proof.
  intros_all.
  rewrite* (@subst_intro x t). 
  rewrite* (@subst_intro x t').
Qed.

Lemma red_out_to_rename : forall (R : pterm -> pterm -> Prop),
  red_out R -> red_rename R.
Proof.
  intros. apply red_out'_to_rename. 
  apply red_out_to_out'; trivial.
Qed.

Lemma L_red_out_to_rename : forall (R : pterm -> pterm -> Prop),
  L_red_out R -> red_rename R. 
Proof.
  intros_all.
  rewrite* (@subst_intro x t). 
  rewrite* (@subst_intro x t').
Qed.


Lemma red_all_to_through : forall (R : pterm -> pterm -> Prop),
  red_regular R -> red_all R -> red_through R. 
Proof.
  intros_all. lets: (H _ _ H4).
  rewrite* (@subst_intro x t1). 
  rewrite* (@subst_intro x u1).
Qed.

Lemma red_out_to_swap : forall (R : pterm -> pterm -> Prop),
  red_out R -> red_swap R. 
Proof.
  intros_all. pick_fresh z.
  apply notin_union in Fr; destruct Fr.
  apply notin_union in H1; destruct H1.
  apply notin_union in H1; destruct H1.
  apply notin_singleton in H1.
  apply notin_singleton in H4.
  repeat rewrite <- swap_eq_subst with (z := z); trivial.
  repeat apply H; trivial.
Qed. 

Lemma red_rename_to_rename' : forall (R : pterm -> pterm -> Prop),
  red_rename R -> red_rename' R. Print red_rename'.
Proof.
 intros_all. apply H with (x := x); trivial.
Qed.

Lemma red_swap_to_rename' : forall (R : pterm -> pterm -> Prop),
  red_swap R -> red_rename' R.
Proof.
  intros_all. unfold red_swap in H.
  case (x == y); intro H'. rewrite <- H'; trivial.
  apply (H x (t ^ x) (t' ^ x) y) in H4. unfold open in *|-*.
  rewrite open_swap_comm in H4.  rewrite open_swap_comm in H4.
  simpl in H4. case (x == y); case (x == x) in H4; intros; try contradiction. clear e n. 
  rewrite swap_fresh in H4; trivial. rewrite swap_fresh in H4; trivial.  
  apply False_ind. apply n; trivial.
Qed.

Lemma red_out'_to_swap : forall (R : pterm -> pterm -> Prop),
  red_out' R -> red_swap R.
Proof. 
  intros_all. pick_fresh z.
  apply notin_union in Fr; destruct Fr.
  apply notin_union in H1; destruct H1.
  apply notin_union in H1; destruct H1.
  apply notin_singleton in H1.
  apply notin_singleton in H4.
  repeat rewrite <- swap_eq_subst with (z := z); trivial.
  repeat apply H; trivial.
Qed. 

Lemma red_regular_ctx: forall (R : pterm -> pterm -> Prop),
  red_regular R -> red_regular (contextual_closure R).
 Proof.
  intros_all. induction H0.
  apply H; trivial. 
  case IHcontextual_closure; clear IHcontextual_closure.
  intros H2 H3. split; 
  apply term_distribute_over_application; split ; trivial.
  case IHcontextual_closure; clear IHcontextual_closure.
  intros H2 H3. split; 
  apply term_distribute_over_application; split ; trivial.
  split; apply body_to_term_abs; unfold body; exists L;
  intros; apply H1; trivial.
  split; apply body_to_subs; trivial; unfold body; exists L;
  intros; apply H2; trivial.
  split; apply body_to_subs; trivial; apply IHcontextual_closure.
Qed.


Lemma red_regular_Lctx : forall (R : pterm -> pterm -> Prop),
  L_red_regular R -> L_red_regular (L_contextual_closure R).
Proof.
  intros_all. induction H0.
  apply H; trivial. 
  destruct IHL_contextual_closure.
  split; apply Lterm_app; trivial. split; apply Lterm_app; trivial.
  apply IHL_contextual_closure. apply IHL_contextual_closure.
  split; apply Lterm_abs with (L := L); apply H1; trivial.
Qed.


Lemma red_regular'_pctx : forall (R : pterm -> pterm -> Prop),
  red_regular' R -> red_regular' (p_contextual_closure R).
Proof.
  intros_all. induction H0.
  apply H; trivial. 
  split. intro H1.
  apply term_distribute_over_application.
  apply term_distribute_over_application in H1. 
  destruct H1. split.
  apply IHp_contextual_closure1; trivial. 
  apply IHp_contextual_closure2; trivial. 
  intro H1.
  apply term_distribute_over_application.
  apply term_distribute_over_application in H1. 
  destruct H1. split.
  apply IHp_contextual_closure1; trivial. 
  apply IHp_contextual_closure2; trivial. 
  split. intro H2. 
  apply body_to_term_abs. apply term_abs_to_body in H2.
  unfold body. exists (L \u (fv t)). intros x Fr.
  apply notin_union in Fr. destruct Fr. apply (H1 x); trivial.
  apply body_to_term; trivial.
  intro H2. 
  apply body_to_term_abs. apply term_abs_to_body in H2.
  unfold body. exists (L \u (fv t')). intros x Fr.
  apply notin_union in Fr. destruct Fr. apply (H1 x); trivial.
  apply body_to_term; trivial.
  split. intro H3. apply subs_to_body in H3. destruct H3.
  apply body_to_subs. unfold body. exists (L \u (fv t)). intros x Fr.
  apply notin_union in Fr. destruct Fr. apply (H1 x); trivial.
  apply body_to_term; trivial. apply IHp_contextual_closure; trivial.
  intro H3. apply subs_to_body in H3. destruct H3.
  apply body_to_subs. unfold body. exists (L \u (fv t')). intros x Fr.
  apply notin_union in Fr. destruct Fr. apply (H1 x); trivial.
  apply body_to_term; trivial. apply IHp_contextual_closure; trivial.
Qed.


Lemma red_regular_trs : forall (R : pterm -> pterm -> Prop),
  red_regular R -> red_regular (trans_closure R).
Proof.
 intros_all. induction H0.
 apply H; trivial. 
 apply H in H0. split; 
 [apply H0 | apply IHtrans_closure].
Qed. 

Lemma red_regular'_trs : forall (R : pterm -> pterm -> Prop),
  red_regular' R -> red_regular' (trans_closure R).
Proof.
 intros_all. induction H0.
 apply H; trivial. 
 apply H in H0. split.
 intro. apply IHtrans_closure. apply H0. trivial.
 intro. apply H0. apply IHtrans_closure. trivial.
Qed. 

Lemma red_out_ctx : forall (R : pterm -> pterm -> Prop),
  red_out R -> red_out (contextual_closure R).
Proof.
 intros_all. induction H1.
 apply redex. apply H; trivial.
 simpl. apply app_left; trivial.
 apply term'_to_term.
 unfold term'. apply lc_at_subst;
 apply term_to_term'; trivial.
 simpl. apply app_right; trivial.
 apply term'_to_term.
 unfold term'. apply lc_at_subst;
 apply term_to_term'; trivial.
 simpl. apply abs_in with (L := L \u {{x}}). 
 intros x0 Fr. apply notin_union in Fr. case Fr. 
 clear Fr. intros H3 H4.
 apply notin_singleton in H4.
 rewrite subst_open_var; trivial.
 rewrite subst_open_var; trivial.
 apply H2; trivial.
 simpl. apply subst_left with (L := L \u {{x}}). 
 apply term'_to_term.
 unfold term'. apply lc_at_subst;
 apply term_to_term'; trivial.
 intros x0 Fr. apply notin_union in Fr. case Fr. 
 clear Fr. intros H4 H5.
 apply notin_singleton in H5.
 rewrite subst_open_var; trivial.
 rewrite subst_open_var; trivial.
 apply H3; trivial.
 simpl. apply subst_right; trivial.
 apply body'_to_body.
 unfold body'. apply lc_at_subst.
 apply body_to_body'; trivial.
 apply term_to_term' in H0. unfold term' in H0.
 apply lc_at_weaken_ind with (k1 := 0); trivial; omega.
Qed.

Lemma red_out_pctx : forall (R : pterm -> pterm -> Prop),
  red_out R -> red_out (p_contextual_closure R).
Proof.
 intros_all. induction H1; simpl.
 apply p_redex. apply H; trivial.
 apply p_app; trivial.
 apply p_abs_in with (L := L \u {{x}}). 
 intros x0 Fr. apply notin_union in Fr. destruct Fr. 
 apply notin_singleton in H4.
 rewrite subst_open_var; trivial.
 rewrite subst_open_var; trivial.
 apply H2; trivial.
 apply p_subst with (L := L \u {{x}}); trivial.
 intros x0 Fr. apply notin_union in Fr. destruct Fr. 
 apply notin_singleton in H5.
 rewrite subst_open_var; trivial.
 rewrite subst_open_var; trivial.
 apply H2; trivial.
Qed.


Lemma red_out_Lctx : forall (R : pterm -> pterm -> Prop),
  L_red_out R -> L_red_out (L_contextual_closure R).
Proof.
 intros_all. induction H1.
 apply L_redex. apply H; trivial.
 simpl. apply L_app_left; trivial.
 apply subst_Lterm; trivial.
 simpl. apply L_app_right; trivial.
 apply subst_Lterm; trivial.
 simpl. apply L_abs_in with (L := L \u {{x}}). 
 intros x0 Fr. apply notin_union in Fr. destruct Fr. 
 apply notin_singleton in H4.
 assert (Q: term u). apply Lterm_is_term; trivial.
 rewrite subst_open_var; trivial.
 rewrite subst_open_var; trivial.
 apply H2; trivial.

Qed.

Lemma red_out_trs : forall (R : pterm -> pterm -> Prop),
  red_out R -> red_out (trans_closure R).
Proof.
 intros_all. induction H1.
 apply one_step_reduction. apply H; trivial.
 apply transitive_reduction with (u := [x ~> u]u0); trivial.
 apply H; trivial.
Qed.
 
Lemma red_not_fv_ctx : forall (R : pterm -> pterm -> Prop),
  red_not_fv R -> red_not_fv (contextual_closure R).
Proof.
 intros R H. unfold red_not_fv in *|-*.
 intros x t t' H'. induction H'.
 apply H; trivial. 
 simpl. intro H1.
 apply notin_union. apply notin_union in H1.
 split. apply IHH'. apply H1. apply H1.
 simpl. intro H1.
 apply notin_union. apply notin_union in H1.
 split. apply H1. apply IHH'. apply H1.
 simpl. intro H2. case var_fresh with (L := {{x}} \u L).
 intros z Fr. apply notin_union in Fr. case Fr; clear Fr.
 intros H3 H4. apply notin_singleton in H3.
 apply fv_notin_open with (z := z); auto. apply H1; trivial.
 apply fv_notin_open; auto.
 simpl. intro H3.
 apply notin_union. apply notin_union in H3.
 split. case var_fresh with (L := {{x}} \u L).
 intros z Fr. apply notin_union in Fr. case Fr; clear Fr.
 intros H4 H5. apply notin_singleton in H4.
 apply fv_notin_open with (z := z); auto. apply H2; trivial.
 apply fv_notin_open; auto. apply H3. apply H3.
 simpl. intro H1.
 apply notin_union. apply notin_union in H1.
 split. apply H1. apply IHH'. apply H1.
Qed.

Lemma red_fv_ctx : forall (R : pterm -> pterm -> Prop),
  red_fv R -> red_fv (contextual_closure R).
Proof.
 intros R H. unfold red_not_fv in *|-*.
 intros x t t' H'. induction H'; simpl.
 apply H; trivial. intro H1.
 apply in_union. apply in_union in H1.
 case H1; clear H1; intro H1. 
 left. apply IHH'; trivial. right; trivial. intro H1.
 apply in_union. apply in_union in H1.
 case H1; clear H1; intro H1.
 left; trivial. right; apply IHH'; trivial. intro H2.
 case var_fresh with (L := {{x}} \u L). intros z Fr.
 apply notin_union in Fr. case Fr; clear Fr; intros H3 H4.
 apply notin_singleton in H3. apply fv_open_in_neq with (y := z); auto.
 apply H1; trivial. apply fv_open_in_neq with (y := z); auto.
 intro H3. apply in_union. apply in_union in H3.
 case H3; clear H3; intro H3. left.
 case var_fresh with (L := {{x}} \u L). intros z Fr.
 apply notin_union in Fr. case Fr; clear Fr; intros H4 H5.
 apply notin_singleton in H4. apply fv_open_in_neq with (y := z); auto.
 apply H2; trivial. apply fv_open_in_neq with (y := z); auto. right; trivial.
 intro H1. apply in_union. apply in_union in H1.
 case H1; clear H1; intro H1. left; trivial. right; apply IHH'; trivial.  
Qed.

Lemma red_swap_ctx: forall (R : pterm -> pterm -> Prop),
  red_swap R -> red_swap (contextual_closure R).
Proof.
 intros R H. unfold red_swap in *|-*.
 intros x t t' y H'. induction H'; simpl.
 apply redex. apply H; trivial.
 apply app_left; trivial. apply swap_term; trivial.
 apply app_right; trivial. apply swap_term; trivial.
 apply abs_in with (L := L \u {{x}} \u {{y}}). intros z Hz.
 apply notin_union in Hz; destruct Hz.
 apply notin_union in H2; destruct H2.
 apply notin_singleton in H3. apply notin_singleton in H4.
 rewrite open_swap; trivial. rewrite open_swap; trivial.
 apply H1; trivial.
 apply subst_left with (L := L \u {{x}} \u {{y}}). apply swap_term; trivial.
 intros z Hz.
 apply notin_union in Hz; destruct Hz.
 apply notin_union in H3; destruct H3.
 apply notin_singleton in H4. apply notin_singleton in H5.
 rewrite open_swap; trivial. rewrite open_swap; trivial.
 apply H2; trivial.
 apply subst_right; trivial. 
 inversion H0. clear H0. exists (x0 \u {{x}} \u {{y}}). intros z Hz.
 apply notin_union in Hz; destruct Hz.
 apply notin_union in H0; destruct H0.
 apply notin_singleton in H2. apply notin_singleton in H3.
 rewrite open_swap; trivial. apply swap_term. apply H1; trivial.
Qed.
 
Lemma red_swap_trs: forall (R : pterm -> pterm -> Prop),
  red_swap R -> red_swap (trans_closure R).
Proof.
 intros R H. unfold red_swap in *|-*. intros x t t' y H'.
 induction H'. apply one_step_reduction. apply H; trivial.
 apply transitive_reduction with (u := ([(x,y)]u)); trivial.
 apply H; trivial.
Qed.

Lemma ctx_abs_in_close : forall x R L t t', red_regular R -> red_out R ->
                        contextual_closure R t t' -> x \notin L ->
                        contextual_closure R (pterm_abs (close t x)) (pterm_abs (close t' x)).
Proof.
 intros x R L t t' H0 H1 H2 Fr.
 apply abs_in with (L := L). intros z Fr'. 
 apply red_out_ctx in H1. apply red_out_to_rename in H1.
 apply H1 with (x := x). apply fv_close'. apply fv_close'.
 replace (close t x ^ x) with t. replace (close t' x ^ x) with t'; trivial.
 apply open_close_var. apply red_regular_ctx in H0. apply H0 in H2. apply H2.
 apply open_close_var. apply red_regular_ctx in H0. apply H0 in H2. apply H2.
Qed.


Lemma trs_Lctx_app_left : forall R t t' u, Lterm u ->
                       trans_closure (L_contextual_closure R) t t' ->
                       trans_closure (L_contextual_closure R) (pterm_app t u) (pterm_app t' u).
Proof.
 intros. induction H0. apply one_step_reduction.
 apply L_app_left; trivial.
 apply transitive_reduction with (u := pterm_app u0 u); trivial.
 apply L_app_left; trivial. 
Qed.

Lemma str_Lctx_app_left : forall R t t' u, Lterm u ->
                       star_closure (L_contextual_closure R) t t' ->
                       star_closure (L_contextual_closure R) (pterm_app t u) (pterm_app t' u).
Proof.
 intros. induction H0. apply reflexive_reduction. apply star_trans_reduction.
 apply trs_Lctx_app_left; trivial.
Qed.

Lemma trs_Lctx_app_right : forall R t u u', Lterm t ->
                       trans_closure (L_contextual_closure R) u u' ->
                       trans_closure (L_contextual_closure R) (pterm_app t u) (pterm_app t u').
Proof.
 intros. induction H0. apply one_step_reduction.
 apply L_app_right; trivial.
 apply transitive_reduction with (u := pterm_app t u); trivial.
 apply L_app_right; trivial. 
Qed.

Lemma str_Lctx_app_right : forall R t u u', Lterm t ->
                       star_closure (L_contextual_closure R) u u' ->
                       star_closure (L_contextual_closure R) (pterm_app t u) (pterm_app t u').
Proof.
 intros. induction H0. apply reflexive_reduction. apply star_trans_reduction.
 apply trs_Lctx_app_right; trivial.
Qed.

Lemma Lctx_abs_in_close : forall x R L t t', L_red_regular R -> L_red_out R ->
                         L_contextual_closure R t t' -> x \notin L ->
                         L_contextual_closure R (pterm_abs (close t x)) (pterm_abs (close t' x)).
Proof.
 intros x R L t t' H0 H1 H2 Fr.
 apply L_abs_in with (L := L). intros z Fr'. 
 apply red_out_Lctx in H1. apply L_red_out_to_rename in H1.
 apply H1 with (x := x). apply fv_close'. apply fv_close'.
 replace (close t x ^ x) with t. replace (close t' x ^ x) with t'; trivial.
 apply open_close_var. apply red_regular_Lctx in H0. apply H0 in H2. apply Lterm_is_term. apply H2.
 apply open_close_var. apply red_regular_Lctx in H0. apply H0 in H2. apply Lterm_is_term. apply H2.
Qed.

Lemma trs_Lctx_abs_in : forall R L t t', L_red_regular R -> L_red_out R -> 
                       (forall x, x \notin L ->  trans_closure (L_contextual_closure R) (t ^ x) (t' ^ x)) -> trans_closure (L_contextual_closure R) (pterm_abs t) (pterm_abs t').
Proof.
 intros R L t t' H0 H1 H2.  case var_fresh with (L := L \u (fv t) \u (fv t')). intros x Fr.
 apply notin_union in Fr. destruct Fr. apply notin_union in H. destruct H.
 assert (Q: trans_closure (L_contextual_closure R) (t ^ x) (t' ^ x)). apply H2; trivial. clear H2.
 gen_eq t0 : (t ^ x). gen_eq t1 : (t' ^ x). intros Ht0 Ht1.
 replace t with (close t0 x). replace t' with (close t1 x). clear Ht0 Ht1. induction Q.
 apply one_step_reduction. apply Lctx_abs_in_close with (L := L); trivial.
 apply transitive_reduction with (u := pterm_abs (close u x)); trivial.
 apply Lctx_abs_in_close with (L := L); trivial.
 rewrite Ht0. rewrite <- close_open_term; trivial. 
 rewrite Ht1. rewrite <- close_open_term; trivial.
Qed.

Lemma str_Lctx_abs_in : forall R L t t', L_red_regular R -> L_red_out R -> 
                       (forall x, x \notin L ->  star_closure (L_contextual_closure R) (t ^ x) (t' ^ x)) -> star_closure (L_contextual_closure R) (pterm_abs t) (pterm_abs t').
Proof.
 intros R L t t' H0 H1 H2.  case var_fresh with (L := L \u (fv t) \u (fv t')). intros x Fr.
 apply notin_union in Fr. destruct Fr. apply notin_union in H. destruct H.
 assert (Q: star_closure (L_contextual_closure R) (t ^ x) (t' ^ x)). apply H2; trivial. clear H2.
 gen_eq t0 : (t ^ x). gen_eq t1 : (t' ^ x). intros Ht0 Ht1.
 replace t with (close t0 x). replace t' with (close t1 x). clear Ht0 Ht1. induction Q.
 apply reflexive_reduction. apply star_trans_reduction. induction H2.
 apply one_step_reduction. apply Lctx_abs_in_close with (L := L); trivial.
 apply transitive_reduction with (u := pterm_abs (close u x)); trivial.
 apply Lctx_abs_in_close with (L := L); trivial.
 rewrite Ht0. rewrite <- close_open_term; trivial. 
 rewrite Ht1. rewrite <- close_open_term; trivial.
Qed.

Lemma pctx_abs_in_close : forall x R L t t', red_regular' R -> red_out R -> term t ->
                         p_contextual_closure R t t' -> x \notin L ->
                         p_contextual_closure R (pterm_abs (close t x)) (pterm_abs (close t' x)).
Proof.
 intros x R L t t' H0 H1 T H2 Fr.
 apply p_abs_in with (L := L). intros z Fr'. 
 apply red_out_pctx in H1. apply red_out_to_rename in H1.
 apply H1 with (x := x). apply fv_close'. apply fv_close'.
 replace (close t x ^ x) with t. replace (close t' x ^ x) with t'; trivial.
 apply open_close_var. apply red_regular'_pctx in H0. apply H0 in H2. apply H2; trivial.
 apply open_close_var; trivial. 
Qed.

Lemma trs_pctx_abs_in_close : forall x R L t t', red_regular' R -> red_out R -> term t ->
                         trans_closure (p_contextual_closure R) t t' -> x \notin L ->
                         trans_closure (p_contextual_closure R) (pterm_abs (close t x)) (pterm_abs (close t' x)).
Proof.
 intros x R L t t' H0 H1 T H Fr. induction H.
 apply one_step_reduction. apply pctx_abs_in_close with (L := L); trivial.  
  apply transitive_reduction with (u := pterm_abs (close u x)).
 apply pctx_abs_in_close with (L := L); trivial.
 apply IHtrans_closure. apply red_regular'_pctx in H0. 
 apply H0 in H. apply H; trivial.
Qed.


Lemma trs_pctx_abs_in : forall R L t t', red_regular' R -> red_out R -> body t ->
                       (forall x, x \notin L ->  trans_closure (p_contextual_closure R) (t ^ x) (t' ^ x)) ->
                       trans_closure (p_contextual_closure R) (pterm_abs t) (pterm_abs t').
Proof.
 intros R L t t' H0 H1 B H2.  case var_fresh with (L := L \u (fv t) \u (fv t')). intros x Fr.
 apply notin_union in Fr. destruct Fr. apply notin_union in H. destruct H.
 assert (Q: trans_closure (p_contextual_closure R) (t ^ x) (t' ^ x)). apply H2; trivial. clear H2.
 gen_eq t0 : (t ^ x). gen_eq t1 : (t' ^ x). intros Ht1 Ht0.
 replace t with (close t0 x). replace t' with (close t1 x).
 assert (T : term t0). rewrite Ht0. apply body_to_term; trivial.
 clear Ht0 Ht1. induction Q.
 apply one_step_reduction. apply pctx_abs_in_close with (L := L); trivial.
 apply transitive_reduction with (u := pterm_abs (close u x)); trivial.
 apply pctx_abs_in_close with (L := L); trivial. apply IHQ.
 apply red_regular'_pctx in H0. apply H0 in H2. apply H2; trivial.
 rewrite Ht1. rewrite <- close_open_term; trivial. 
 rewrite Ht0. rewrite <- close_open_term; trivial.
Qed.

Lemma str_pctx_abs_in : forall R L t t', red_regular' R -> red_out R -> body t ->
                       (forall x, x \notin L ->  star_closure (p_contextual_closure R) (t ^ x) (t' ^ x)) ->
                       star_closure (p_contextual_closure R) (pterm_abs t) (pterm_abs t').
Proof.
 intros R L t t' H0 H1 B H2.  case var_fresh with (L := L \u (fv t) \u (fv t')). intros x Fr.
 apply notin_union in Fr. destruct Fr. apply notin_union in H. destruct H.
 assert (Q: star_closure (p_contextual_closure R) (t ^ x) (t' ^ x)). apply H2; trivial. clear H2.
 gen_eq t0 : (t ^ x). gen_eq t1 : (t' ^ x). intros Ht1 Ht0.
 replace t with (close t0 x). replace t' with (close t1 x).
 assert (T : term t0). rewrite Ht0. apply body_to_term; trivial.
 clear Ht0 Ht1. induction Q.
 apply reflexive_reduction. apply star_trans_reduction. induction H2.
 apply one_step_reduction. apply pctx_abs_in_close with (L := L); trivial.
 apply transitive_reduction with (u := pterm_abs (close u x)); trivial.
 apply pctx_abs_in_close with (L := L); trivial.
 apply IHtrans_closure.
 apply red_regular'_pctx in H0. apply H0 in H2. apply H2; trivial.
 rewrite Ht1. rewrite <- close_open_term; trivial. 
 rewrite Ht0. rewrite <- close_open_term; trivial.
Qed.


Lemma ctx_subst_left_close : forall x R L t t' u, red_regular R -> red_out R -> term u ->
                         contextual_closure R t t' -> x \notin L ->
                         contextual_closure R ((close t x)[u]) ((close t' x)[u]).
Proof.
 intros x R L t t' u H0 H1 T H2 Fr.
 apply subst_left with (L := L); trivial. intros z Fr'. 
 apply red_out_ctx in H1. apply red_out_to_rename in H1.
 apply H1 with (x := x). apply fv_close'. apply fv_close'.
 replace (close t x ^ x) with t. replace (close t' x ^ x) with t'; trivial.
 apply open_close_var. apply red_regular_ctx in H0. apply H0 in H2. apply H2.
 apply open_close_var. apply red_regular_ctx in H0. apply H0 in H2. apply H2.
Qed.

Lemma trs_ctx_subst_left : forall R L t t' u, red_regular R -> red_out R -> term u ->
                       (forall x, x \notin L ->  trans_closure (contextual_closure R) (t ^ x) (t' ^ x)) ->
                       trans_closure (contextual_closure R) (t[u]) (t'[u]).
Proof.
 intros R L t t' u H0 H1 T H2.  case var_fresh with (L := L \u (fv t) \u (fv t')). intros x Fr.
 apply notin_union in Fr. destruct Fr. apply notin_union in H. destruct H.
 assert (Q: trans_closure (contextual_closure R) (t ^ x) (t' ^ x)). apply H2; trivial. clear H2.
 gen_eq t0 : (t ^ x). gen_eq t1 : (t' ^ x). intros Ht0 Ht1.
 replace t with (close t0 x). replace t' with (close t1 x). clear Ht0 Ht1. induction Q.
 apply one_step_reduction. apply ctx_subst_left_close with (L := L); trivial.
 apply transitive_reduction with (u := (close u0 x)[u]); trivial.
 apply ctx_subst_left_close with (L := L); trivial.
 rewrite Ht0. rewrite <- close_open_term; trivial. 
 rewrite Ht1. rewrite <- close_open_term; trivial.
Qed.

Lemma str_ctx_subst_left : forall R L t t' u, red_regular R -> red_out R -> term u ->
                       (forall x, x \notin L ->  star_closure (contextual_closure R) (t ^ x) (t' ^ x)) ->
                       star_closure (contextual_closure R) (t[u]) (t'[u]).
Proof.
 intros R L t t' u H0 H1 T H2.  case var_fresh with (L := L \u (fv t) \u (fv t')). intros x Fr.
 apply notin_union in Fr. destruct Fr. apply notin_union in H. destruct H.
 assert (Q: star_closure (contextual_closure R) (t ^ x) (t' ^ x)). apply H2; trivial. clear H2.
 gen_eq t0 : (t ^ x). gen_eq t1 : (t' ^ x). intros Ht1 Ht0.
 replace t with (close t0 x). replace t' with (close t1 x). clear Ht0 Ht1. destruct Q.
 apply reflexive_reduction. apply star_trans_reduction. induction H2.
 apply one_step_reduction. apply ctx_subst_left_close with (L := L); trivial.
 apply transitive_reduction with (u := (close u0 x)[u]); trivial.
 apply ctx_subst_left_close with (L := L); trivial.
 rewrite Ht1. rewrite <- close_open_term; trivial. 
 rewrite Ht0. rewrite <- close_open_term; trivial.
Qed.


Lemma pctx_subst_close : forall x R L t t' u u', red_regular' R -> red_out R -> term t -> term u ->
                         p_contextual_closure R u u' ->
                         p_contextual_closure R t t' -> x \notin L ->
                         p_contextual_closure R ((close t x)[u]) ((close t' x)[u']).
Proof.
 intros x R L t t' u u' H0 H1 Tt Tu H2 H3 Fr.
 apply p_subst with (L := L); trivial. intros z Fr'. 
 apply red_out_pctx in H1. apply red_out_to_rename in H1.
 apply H1 with (x := x). apply fv_close'. apply fv_close'.
 replace (close t x ^ x) with t. replace (close t' x ^ x) with t'; trivial.
 apply open_close_var. apply red_regular'_pctx in H0. apply H0 in H3. apply H3; trivial.
 apply open_close_var; trivial. 
Qed.

Lemma trs_pctx_subst_close : forall x R L t t' u u', 
                         red_regular' R -> red_out R -> (forall t0, R t0 t0) ->
                         term t -> term u ->
                         trans_closure (p_contextual_closure R) t t' -> 
                         trans_closure (p_contextual_closure R) u u' -> x \notin L ->
                         trans_closure (p_contextual_closure R) ((close t x)[u]) ((close t' x)[u']).
Proof.
 intros x R L t t' u u' H0 H1 H2 Tt Tu H3 H4 Fr. induction H3. induction H4.
 apply one_step_reduction. apply pctx_subst_close with (L := L); trivial.  
  apply transitive_reduction with (u := (close t x)[u]).
 apply pctx_subst_close with (L := L); trivial. apply p_redex. apply H2. 
 apply IHtrans_closure. apply red_regular'_pctx in H0. 
 apply H0 in H3. apply H3; trivial.
 apply transitive_reduction with (u := (close u0 x)[u]).
 apply pctx_subst_close with (L := L); trivial. apply p_redex. apply H2.
 apply IHtrans_closure. apply red_regular'_pctx in H0. 
 apply H0 in H. apply H; trivial.
Qed.


Lemma trs_pctx_subst : forall R L t t' u u', red_regular' R -> red_out R -> (forall t0, R t0 t0) -> 
                        body t -> term u ->
                       (forall x, x \notin L ->  trans_closure (p_contextual_closure R) (t ^ x) (t' ^ x)) -> 
                       trans_closure (p_contextual_closure R) u u' ->
                       trans_closure (p_contextual_closure R) (t[u]) (t'[u']).
Proof.
 intros R L t t' u u' H0 H1 H2 B Tu H3 H4.  case var_fresh with (L := L \u (fv t) \u (fv t')). intros x Fr.
 apply notin_union in Fr. destruct Fr. apply notin_union in H. destruct H.
 assert (Q: trans_closure (p_contextual_closure R) (t ^ x) (t' ^ x)). apply H3; trivial. clear H3.
 gen_eq t0 : (t ^ x). gen_eq t1 : (t' ^ x). intros Ht1 Ht0.
 replace t with (close t0 x). replace t' with (close t1 x).
 assert (T : term t0). rewrite Ht0. apply body_to_term; trivial.
 clear Ht0 Ht1. induction Q. induction H4.
 apply one_step_reduction. apply pctx_subst_close with (L := L); trivial.
 apply transitive_reduction with (u := (close t0 x)[u]); trivial.
 apply pctx_subst_close with (L := L); trivial. apply p_redex. apply H2. 
 apply IHtrans_closure. apply red_regular'_pctx in H0. apply H0 in H4. apply H4; trivial.
 apply transitive_reduction with (u := (close u0 x)[u]); trivial.
 apply pctx_subst_close with (L := L); trivial. apply p_redex. apply H2. 
 apply IHQ. apply red_regular'_pctx in H0. apply H0 in H3. apply H3; trivial.
 rewrite Ht1. rewrite <- close_open_term; trivial. 
 rewrite Ht0. rewrite <- close_open_term; trivial.
Qed.

Lemma str_pctx_subst : forall R L t t' u u', red_regular' R -> red_out R -> (forall t0, R t0 t0) -> 
                        body t -> term u ->
                       (forall x, x \notin L ->  star_closure (p_contextual_closure R) (t ^ x) (t' ^ x)) -> 
                       star_closure (p_contextual_closure R) u u' ->
                       star_closure (p_contextual_closure R) (t[u]) (t'[u']).
Proof.
 intros R L t t' u u' H0 H1 H2 B Tu H3 H4.  case var_fresh with (L := L \u (fv t) \u (fv t')). intros x Fr.
 apply notin_union in Fr. destruct Fr. apply notin_union in H. destruct H.
 assert (Q: star_closure (p_contextual_closure R) (t ^ x) (t' ^ x)). apply H3; trivial. clear H3.
 gen_eq t0 : (t ^ x). gen_eq t1 : (t' ^ x). intros Ht1 Ht0.
 replace t with (close t0 x). replace t' with (close t1 x).
 assert (T : term t0). rewrite Ht0. apply body_to_term; trivial.
 clear Ht0 Ht1. destruct H4. destruct Q. apply reflexive_reduction.
 apply star_trans_reduction. induction H3.
 apply one_step_reduction. apply pctx_subst_close with (L := L); trivial. apply p_redex. apply H2.
 apply transitive_reduction with (u := (close u x)[t2]); trivial.
 apply pctx_subst_close with (L := L); trivial. apply p_redex. apply H2. 
 apply IHtrans_closure. apply red_regular'_pctx in H0. apply H0 in H3. apply H3; trivial.
 destruct Q. apply star_trans_reduction. induction H3. apply one_step_reduction.
 apply pctx_subst_close with (L := L); trivial. apply p_redex. apply H2.
 apply transitive_reduction with (u := (close t0 x)[u]); trivial.
 apply pctx_subst_close with (L := L); trivial. apply p_redex. apply H2. 
 apply IHtrans_closure. apply red_regular'_pctx in H0. apply H0 in H3. apply H3; trivial.
 apply star_trans_reduction. induction H3. induction H4.
 apply one_step_reduction. apply pctx_subst_close with (L := L); trivial.
 apply transitive_reduction with (u := (close u0 x)[t1]); trivial.
 apply pctx_subst_close with (L := L); trivial. apply p_redex. apply H2. 
 apply IHtrans_closure. apply red_regular'_pctx in H0. apply H0 in H4. apply H4; trivial.
 apply transitive_reduction with (u := (close t0 x)[u]); trivial.
 apply pctx_subst_close with (L := L); trivial. apply p_redex. apply H2. 
 apply IHtrans_closure. apply red_regular'_pctx in H0. apply H0 in H3. apply H3; trivial.
 rewrite Ht1. rewrite <- close_open_term; trivial. 
 rewrite Ht0. rewrite <- close_open_term; trivial.
Qed.

(* ********************************************************************** *)
(** About SN & NF **)

Lemma NF_to_SN0 : forall R t, NF R t -> SN_ind 0 R t.
Proof.
 intros R t H.
 apply SN_intro.
 intros t' H'. unfold NF in H.
 assert (Q : ~ R t t'). apply H.
 contradiction.
Qed.

Lemma SN0_to_NF : forall R t, SN_ind 0 R t -> NF R t.
Proof.
 intros R t H. unfold NF.
 intros t' H'. inversion H.
 case H0 with (t' := t'). assumption.
 intros n H''. omega.
Qed.

Lemma NF_eq_SN0 : forall R t, NF R t <-> SN_ind 0 R t.
Proof. intros R t. split; [apply NF_to_SN0 | apply SN0_to_NF]. Qed.


Lemma WSN : forall n k R t, k <= n -> SN_ind k R t -> SN_ind n R t.
Proof.
 intros n k R t H.
 destruct H; trivial. intro H'.
 apply SN_intro. intros t' H''. destruct H'.
 case (H0 t'); trivial. intros n' H'''. exists n'.
 split; try omega. apply H'''.
Qed.

Lemma SN_one_step : forall n (R : pterm -> pterm -> Prop) t u, R t u -> SN_ind (S n) R t -> SN_ind n R u.
Proof.
 intros n R t u H H'. 
 destruct H'. case (H0 u); trivial.
 intro n'. intro H'. apply WSN with (k := n'). omega.
 apply H'.
Qed.

Lemma SN_trs : forall n R t u, trans_closure R t u -> 
                               SN_ind n R t -> (exists k, k < n /\ SN_ind k R u).
Proof.
 intros. generalize n H0; clear n H0.
 induction H; intros. destruct n. apply False_ind. apply SN0_to_NF in H0. 
 apply (H0 u); trivial. apply SN_one_step with (u := u) in H0; trivial. 
 exists n. split; try omega; trivial.
 destruct H1. case (H1 u); trivial; clear H1. intros n' H1. destruct H1.
 case IHtrans_closure with (n := n'); trivial. intros k' H3. destruct H3.
 exists k'. split; try omega; trivial.
Qed.

Lemma SN_app : forall n R t u, red_regular R ->  term t -> term u -> 
               SN_ind n (contextual_closure R) (pterm_app t u) ->
               SN_ind n (contextual_closure R) t /\ SN_ind n (contextual_closure R) u.
 Proof.
 intros n R t u Reg. 
 generalize t u; clear t u.  
 induction n.  intros. split; rewrite <- NF_eq_SN0 in *|-*; unfold NF in *|-*. 
 intros t' H'. apply (H1 (pterm_app t' u)). apply app_left; trivial.
 intros u' H'. apply (H1 (pterm_app t u')). apply app_right; trivial.
 intros t u Tt Tu H. destruct H. split. 
 apply SN_intro. intros t' H'. exists n. split; try omega. 
 apply IHn with (t := t') (u := u); trivial. apply red_regular_ctx in Reg.
 apply Reg in H'. apply H'. case (H (pterm_app t' u)). apply app_left; trivial. 
 intros k H''. apply WSN with (k := k). omega. apply H''.
 apply SN_intro. intros u' H'. exists n. split; try omega. 
 apply IHn with (t := t) (u := u'); trivial. apply red_regular_ctx in Reg.
 apply Reg in H'. apply H'. case (H (pterm_app t u')). apply app_right; trivial. 
 intros k H''. apply WSN with (k := k). omega. apply H''.
Qed. 


Lemma L_SN_app : forall n R t u, L_red_regular R ->  Lterm t -> Lterm u -> 
               SN_ind n (L_contextual_closure R) (pterm_app t u) ->
               SN_ind n (L_contextual_closure R) t /\ SN_ind n (L_contextual_closure R) u.
 Proof.
 intros n R t u Reg. 
 generalize t u; clear t u.  
 induction n.  intros. split; rewrite <- NF_eq_SN0 in *|-*; unfold NF in *|-*. 
 intros t' H'. apply (H1 (pterm_app t' u)). apply L_app_left; trivial.
 intros u' H'. apply (H1 (pterm_app t u')). apply L_app_right; trivial.
 intros t u Tt Tu H. destruct H. split. 
 apply SN_intro. intros t' H'. exists n. split; try omega. 
 apply IHn with (t := t') (u := u); trivial. apply red_regular_Lctx in Reg.
 apply Reg in H'. apply H'. case (H (pterm_app t' u)). apply L_app_left; trivial. 
 intros k H''. apply WSN with (k := k). omega. apply H''.
 apply SN_intro. intros u' H'. exists n. split; try omega. 
 apply IHn with (t := t) (u := u'); trivial. apply red_regular_Lctx in Reg.
 apply Reg in H'. apply H'. case (H (pterm_app t u')). apply L_app_right; trivial. 
 intros k H''. apply WSN with (k := k). omega. apply H''.
Qed. 


Lemma SN_abs : forall x n R t, red_regular R -> red_out R -> 
               SN_ind n (contextual_closure R) (pterm_abs t) ->
               x \notin (fv t) -> SN_ind n (contextual_closure R) (t ^ x).
Proof.
 intros x n R t Reg Out.
 generalize t; clear t.
 apply red_regular_ctx in Reg. 
 apply red_out_ctx in Out. 
 apply red_out_to_rename in Out.
 induction n. intros. 
 apply SN0_to_NF in H. 
 apply NF_to_SN0; unfold NF in *|-*.
 intros t' H'. gen_eq t0 : (close t' x). intro H1.
 replace t' with (t0 ^ x) in H'.
 assert (Q: contextual_closure R (pterm_abs t) (pterm_abs t0)).
    apply abs_in with (L := {{x}}). intros z H2. 
    apply notin_singleton in H2. apply Out with (x := x); trivial.
    rewrite H1. apply fv_close'.
 assert (Q': ~ contextual_closure R (pterm_abs t) (pterm_abs t0)).
    apply H.
 contradiction. rewrite H1. rewrite open_close_var with (x := x).
 reflexivity. apply Reg in H'. apply H'.
 intros. destruct H. apply SN_intro.
 intros. exists n. split; try omega.
 gen_eq t0 : (close t' x). intro H2.
 replace t' with (t0 ^ x). replace t' with (t0 ^ x) in H1.
 apply IHn; trivial. case (H (pterm_abs t0)); trivial.
 apply abs_in with (L := {{x}}).
 intros z H3. apply notin_singleton in H3. 
 apply Out with (x := x); trivial.
 rewrite H2. apply fv_close'.
 intros k H3. apply WSN with (k := k); try omega.
 apply H3. rewrite H2. apply fv_close'.
 rewrite H2. rewrite open_close_var with (x := x).
 reflexivity. apply Reg in H1. apply H1.
 rewrite H2. rewrite open_close_var with (x := x).
 reflexivity. apply Reg in H1. apply H1. 
Qed.


Lemma L_SN_abs : forall x n R t, L_red_regular R -> L_red_out R -> 
               SN_ind n (L_contextual_closure R) (pterm_abs t) ->
               x \notin (fv t) -> SN_ind n (L_contextual_closure R) (t ^ x).
Proof.
 intros x n R t Reg Out.
 generalize t; clear t.
 apply red_regular_Lctx in Reg. 
 apply red_out_Lctx in Out. 
 apply L_red_out_to_rename in Out.
 induction n. intros. 
 apply SN0_to_NF in H. 
 apply NF_to_SN0; unfold NF in *|-*.
 intros t' H'. gen_eq t0 : (close t' x). intro H1.
 replace t' with (t0 ^ x) in H'.
 assert (Q: L_contextual_closure R (pterm_abs t) (pterm_abs t0)).
    apply L_abs_in with (L := {{x}}). intros z H2. 
    apply notin_singleton in H2. apply Out with (x := x); trivial.
    rewrite H1. apply fv_close'.
 assert (Q': ~ L_contextual_closure R (pterm_abs t) (pterm_abs t0)).
    apply H.
 contradiction. rewrite H1. rewrite open_close_var with (x := x).
 reflexivity. apply Reg in H'. apply Lterm_is_term. apply H'.
 intros. destruct H. apply SN_intro.
 intros. exists n. split; try omega.
 gen_eq t0 : (close t' x). intro H2.
 replace t' with (t0 ^ x). replace t' with (t0 ^ x) in H1.
 apply IHn; trivial. case (H (pterm_abs t0)); trivial.
 apply L_abs_in with (L := {{x}}).
 intros z H3. apply notin_singleton in H3. 
 apply Out with (x := x); trivial.
 rewrite H2. apply fv_close'.
 intros k H3. apply WSN with (k := k); try omega.
 apply H3. rewrite H2. apply fv_close'.
 rewrite H2. rewrite open_close_var with (x := x).
 reflexivity. apply Lterm_is_term. apply Reg in H1. apply H1.
 rewrite H2. rewrite open_close_var with (x := x).
 reflexivity. apply Lterm_is_term. apply Reg in H1. apply H1. 
Qed.


Lemma SN_sub : forall x n R t u, red_regular R -> red_out R -> 
               body t -> term u -> x \notin (fv t) -> 
               SN_ind n (contextual_closure R) (t[u]) ->
               SN_ind n (contextual_closure R) (t ^ x) /\
               SN_ind n (contextual_closure R) u.
Proof.
 intros x n R t u Reg Out.
 generalize t u; clear t u.
 apply red_regular_ctx in Reg. 
 apply red_out_ctx in Out. 
 apply red_out_to_rename in Out.
 induction n. intros. 
 apply SN0_to_NF in H2. split; intros;
 apply NF_to_SN0; unfold NF in *|-*.
 intros t' H'. gen_eq t0 : (close t' x). intro H3.
 replace t' with (t0 ^ x) in H'.
 assert (Q: contextual_closure R (t[u])(t0[u])).
    apply subst_left with (L := {{x}}); trivial. intros z H4. 
    apply notin_singleton in H4. apply Out with (x := x); trivial.
    rewrite H3. apply fv_close'.
 assert (Q': ~ contextual_closure R (t[u]) (t0[u])).
    apply H2.
 contradiction. rewrite H3. rewrite open_close_var with (x := x).
 reflexivity. apply Reg in H'. apply H'.
 intros t' H'.
 assert (Q: contextual_closure R (t[u])(t[t'])).
   apply subst_right; trivial. 
 assert (Q': ~ contextual_closure R (t[u])(t[t'])).
   apply H2.
 contradiction.
 intros. destruct H2. split. intros. apply SN_intro.
 intros. exists n. split; try omega.
 gen_eq t0 : (close t' x). intro H4.
 replace t' with (t0 ^ x). replace t' with (t0 ^ x) in H3.
 assert (Q : x \notin fv t0). rewrite H4. apply fv_close'.
 apply (IHn t0 u); trivial. apply Reg in H3.
 apply body'_to_body. case H3; clear H3. intros H3 H5.
 apply term_to_term' in H5. unfold body'. unfold term' in H5.
 unfold open in H5. apply lc_at_open in H5; trivial.
 case (H2 (t0[u])); trivial.
 apply subst_left with (L := {{x}}); trivial.
 intros z H5. apply notin_singleton in H5. 
 apply Out with (x := x); trivial.
 intros k H5. apply WSN with (k := k); try omega. apply H5.
 rewrite H4. rewrite open_close_var with (x := x).
 reflexivity. apply Reg in H3. apply H3.
 rewrite H4. rewrite open_close_var with (x := x).
 reflexivity. apply Reg in H3. apply H3.
 apply SN_intro.
 intros t' H'. exists n.
 split; try omega. 
 apply IHn with (t := t) (u := t'); trivial.
 apply Reg in H'. apply H'.
 case (H2 (t[t'])).
 apply subst_right; trivial. 
 intros k H''. apply WSN with (k := k).
 omega. apply H''.
Qed.


(*** about SN and NF in lists ***)

Lemma NF_eq_SN0_list : forall R lt, NF R %% lt <-> SN_ind 0 R %% lt.
Proof.
 intros R lt. induction lt; simpl; split; trivial.
 intro H. destruct H. split. 
 apply NF_to_SN0; trivial. apply IHlt; trivial.
 intro H. destruct H. split.
 apply SN0_to_NF; trivial. apply IHlt; trivial.
Qed.

Lemma WSN_list : forall n k R lt, k <= n -> SN_ind k R %% lt -> SN_ind n R %% lt.
Proof.
 intros n k R lt H. induction lt; simpl; trivial.
 intro H'. destruct H'. split. apply WSN with (k := k); trivial.
 apply IHlt; trivial.
Qed.

Lemma SN_list : forall R lt, SN R %% lt <-> exists n, SN_ind n R %% lt.
Proof.
 intros R lt. induction lt; simpl; split; intros; trivial.
 exists 0; trivial. destruct IHlt. destruct H. case H0; clear H0; trivial.
 intros n H0. case H; clear H. intros n' H. exists (n + n').
 split. apply WSN with (k := n'); try omega; trivial.
 apply WSN_list with (k := n); try omega; trivial. split.
 case H; clear H. intros n H. destruct H. exists n; trivial.
 case H; clear H. intros n H. destruct H. apply IHlt. exists n; trivial.
Qed.

Lemma SN_mult_app : forall n R t l, red_regular R ->  term t -> term %% l -> 
               SN_ind n (contextual_closure R) (t // l) ->
               SN_ind n (contextual_closure R) t /\ SN_ind n (contextual_closure R) %% l.
Proof.
 intros n R t l Reg. generalize n t; clear n t.
 induction l; simpl. intros n t T H0 H. split; trivial.
 intros n t T H0 H. destruct H0. apply SN_app in H; trivial. destruct H.
 assert (Q : SN_ind n (contextual_closure R) t /\ SN_ind n (contextual_closure R) %% l). 
  apply IHl; trivial.
 clear IHl. destruct Q. split; trivial. split; trivial.
 rewrite term_mult_app. split; trivial. 
Qed. 


Lemma L_SN_mult_app : forall n R t l, L_red_regular R ->  Lterm t -> Lterm %% l -> 
               SN_ind n (L_contextual_closure R) (t // l) ->
               SN_ind n (L_contextual_closure R) t /\ SN_ind n (L_contextual_closure R) %% l.
Proof.
 intros n R t l Reg. generalize n t; clear n t.
 induction l; simpl. intros n t T H0 H. split; trivial.
 intros n t T H0 H. destruct H0. apply L_SN_app in H; trivial. destruct H.
 assert (Q : SN_ind n (L_contextual_closure R) t /\ SN_ind n (L_contextual_closure R) %% l). 
  apply IHl; trivial.
 clear IHl. destruct Q. split; trivial. split; trivial.
 rewrite Lterm_mult_app. split; trivial. 
Qed. 
