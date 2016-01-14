Require Import Arith Metatheory.
Require Import LibTactics LambdaES_Tac.
Require Import LambdaES_Defs LambdaES_FV LambdaES_Infra.
Require Import Rewriting_Defs Rewriting_Lib.
Require Import Morphisms.

Instance iff_eq : Equivalence iff.
Proof. 
 split; intros_all.
 split; trivial.
 split; apply H.
 split. intro H1. apply H0. apply H; trivial.
 intro H1. apply H. apply H0; trivial.
Qed.

(** =e definition: The equation c defines permutation of independent substitutions, which corresponds to forbid dangling deBruijn indexes in both u and v, i.e. u and v are terms.  *)
Inductive eqc : pterm -> pterm -> Prop := 
  | eqc_rf: forall u, eqc u u  
  | eqc_rx: forall t u v, 
    term u -> term v -> eqc (t[u][v]) ((& t)[v][u]) 
 .

Lemma eqc_sym : forall t u, eqc t u -> eqc u t.
Proof.
 intros t u H. destruct H. 
 apply eqc_rf. replace (t[u][v]) with ((& (& t))[u][v]).
 apply eqc_rx; trivial.
 unfold bswap. rewrite bswap_rec_id. trivial.
Qed.

Lemma eqc_trans: forall t u v, eqc t u -> eqc u v -> eqc t v.
Proof.
 intros t u v H1 H2.
 destruct H1. trivial. inversion H2.
 apply eqc_rx; trivial. unfold bswap.
 rewrite bswap_rec_id. apply eqc_rf. 
Qed.

Instance eqc_eq : Equivalence eqc.
Proof.
 split; intros_all.
 apply eqc_rf.
 apply eqc_sym; trivial.
 generalize H H0. apply eqc_trans.
Qed.

(***)

Definition eqC (t : pterm) (u : pterm) := trans_closure (p_contextual_closure eqc) t u.
Notation "t =e u" := (eqC t u) (at level 66). 

(** =e is an equivalence relation *)

Lemma eqC_rf : forall t, t =e t.
Proof.
 intro t. 
 apply one_step_reduction.
 apply p_redex. reflexivity.
Qed.

Lemma pctx_eqc_sym : forall t u, (p_contextual_closure eqc t u) -> p_contextual_closure eqc u t. 
Proof.
  intros t u H. induction H.
  apply p_redex. rewrite H. reflexivity.
  apply p_app; trivial.
  apply p_abs_in with (L:=L); trivial.
  apply p_subst with (L:=L); trivial.
Qed.

Lemma eqC_sym : forall t u, t =e u -> u =e t.
Proof.
 intros t u H. induction H.
 apply one_step_reduction. apply pctx_eqc_sym; trivial.
 apply transitive_closure_composition with (u := u); trivial.
 apply one_step_reduction. apply pctx_eqc_sym; trivial.
Qed.

Lemma eqC_trans : forall t u v, t =e u -> u =e v -> t =e v.
Proof.
 intros t u v H H'.
 apply transitive_closure_composition with (u := u); trivial.
Qed.

Instance eqC_eq : Equivalence eqC.
Proof.
 split; intros_all.
 apply eqC_rf.
 apply eqC_sym; trivial.
 apply eqC_trans with (u := y); trivial.
Qed.

(*** =e inversion ***)

Lemma eqc_fvar_term  : forall x t, eqc (pterm_fvar x) t -> pterm_fvar x = t.
Proof.
  intros x t H. inversion H. trivial.
Qed.

Lemma eqc_app_term :  forall t u v, eqc (pterm_app u v) t -> pterm_app u v = t.
Proof. 
   intros t u v H. 
   inversion H. trivial.
Qed.

Lemma eqc_abs_term :  forall t t', eqc (pterm_abs t) t' -> pterm_abs t = t' .
Proof. 
   intros t t' H. inversion H. trivial.
Qed.


Lemma eqc_sub_term :  forall t u t0, eqc (t[u]) t0 -> 
(t[u] = t0 \/ exists t', exists v, term u /\ term v /\ t'[v] = t /\ (& t')[u][v] = t0) .
Proof. 
   intros t u t0 H. inversion H. 
   left; trivial. right. exists t1 u0. 
   split; trivial. split; trivial. split; trivial.
Qed.

(****)

Lemma pctx_eqc_fvar_term  : forall x t, p_contextual_closure eqc (pterm_fvar x) t -> pterm_fvar x = t.
Proof.
  intros x t H. inversion H. inversion H0; trivial.
Qed.

Lemma pctx_eqc_app_term :  forall t u v, p_contextual_closure eqc (pterm_app u v) t ->
                           exists u', exists v', pterm_app u' v' = t /\ p_contextual_closure eqc u' u /\ p_contextual_closure eqc v' v.
Proof. 
   intros t u v H. inversion H.
   exists u v. split; trivial. inversion H0; trivial.
   split; apply p_redex; reflexivity.
   exists t' u'. split; trivial. 
   split; apply pctx_eqc_sym; trivial.
Qed.

Lemma pctx_eqc_abs_term :  forall t t', p_contextual_closure eqc (pterm_abs t) t' ->
                       exists u, exists L, pterm_abs u = t' /\ (forall x, x \notin L -> p_contextual_closure eqc (u ^ x) (t ^ x)).
Proof. 
   intros t t' H. inversion H. 
   exists t {}. split; trivial. inversion H0; trivial.
   intros x H'. apply p_redex. reflexivity.
   exists t'0 L. split; trivial. intros. 
   apply pctx_eqc_sym. apply H1. trivial.
Qed.

(**)

Lemma pctx_eqc_sub_term :  forall t u t0, p_contextual_closure eqc (t[u]) t0 -> exists t', exists u', t'[u'] = t0 .
Proof. 
   intros t u t0 H. inversion H. inversion H0.
   exists t u; trivial. 
   exists (& t2 [u]) u0; trivial.
   exists t' u'; trivial.
Qed.

(**)

(****)

Lemma eqC_fvar_term  : forall x t, pterm_fvar x =e t -> pterm_fvar x = t.
Proof.
  intros x t H. gen_eq t0 : (pterm_fvar x). induction H.
  intro H'. rewrite H' in *|-*. apply pctx_eqc_fvar_term; trivial.
  intro H'. rewrite H' in *|-*. rewrite <- IHtrans_closure.
  apply pctx_eqc_fvar_term; trivial. 
  apply pctx_eqc_fvar_term in H. rewrite H; trivial.
Qed.

Lemma eqC_app_term :  forall t u v, pterm_app u v =e t ->
                      exists u', exists v', pterm_app u' v' = t /\ u' =e u /\ v' =e v.
Proof. 
  intros t u v H. gen_eq t0 : (pterm_app u v). generalize u v. clear u v. induction H.
  intros u0 v0 H'. rewrite H' in *|-*. apply pctx_eqc_app_term in H.
  case H; clear H; intros u' H. case H; clear H; intros v' H. destruct H. destruct H0.
  exists u' v'. split; trivial. split; apply one_step_reduction; trivial.
  intros u0 v0 H'. rewrite H' in H. apply pctx_eqc_app_term in H.
  case H; clear H; intros u1 H. case H; clear H; intros v1 H. destruct H. destruct H1.
  case (IHtrans_closure u1 v1). rewrite H; trivial. intros u2 H3.
  case H3; clear H3; intros v2 H3. destruct H3. destruct H4.
  exists u2 v2. split; trivial. 
  split; try rewrite H4; try rewrite H5; apply one_step_reduction; trivial. 
Qed.

Lemma eqC_abs_term :  forall t t', pterm_abs t =e t' ->
                      exists u, exists L, pterm_abs u = t' /\ (forall x, x \notin L -> (u ^ x) =e (t ^ x)).
Proof. 
   intros t t' H. gen_eq t0 : (pterm_abs t). generalize t; clear t. induction H. 
   intros t' H'. rewrite H' in H. apply pctx_eqc_abs_term in H.
   case H; clear H; intros u0 H. case H; clear H; intros L H. destruct H.
   exists u0 L. split; trivial. intros x Fr. apply one_step_reduction. apply H0; trivial.
   intros t0 H'. rewrite H' in H. apply pctx_eqc_abs_term in H.
   case H; clear H; intros u0 H. case H; clear H; intros L H. destruct H.
   case (IHtrans_closure u0). rewrite H; trivial. intros t1 H2.
   case H2; clear H2; intros L' H2. destruct H2. exists t1 (L \u L'). 
   split; trivial. intros x Fr. apply notin_union in Fr. destruct Fr.
   rewrite (H3 x); trivial. apply one_step_reduction. apply H1; trivial.
Qed.


(***)

Lemma eqC_sub_term :  forall t u t0, t[u] =e t0 -> exists t', exists u', t'[u'] = t0 .
Proof. 
   intros t u v H. gen_eq t0 : (t [u]). generalize t u; clear t u. induction H.
   intros t' u' H'. rewrite H' in H. apply pctx_eqc_sub_term in H; trivial.
   intros t' u' H'. rewrite H' in H. apply pctx_eqc_sub_term in H.
   case H; clear H; intros t0 H. case H; clear H; intros u0 H.
   case (IHtrans_closure t0 u0). rewrite H; trivial. intros t1 H1. 
   case H1; clear H1; intros u1 H1. exists t1 u1; trivial.
Qed.



Lemma eqC_redex : forall t u v, term u -> term v -> (t[u][v]) =e ((& t)[v][u]) .
Proof.
 intros t u v Tu Tv. apply one_step_reduction. apply p_redex. apply eqc_rx; trivial.
Qed.


Definition red_ctx_mod_eqC (R: pterm -> pterm -> Prop) (t: pterm) (u : pterm) := 
           exists t', exists u', (t =e t')/\(contextual_closure R t' u')/\(u' =e u).


(* ********************************************************************** *)
(** =e Properties *)

Lemma lc_at_eqc : forall n t u, eqc t u  -> (lc_at n t <-> lc_at n u).
Proof.
 intros n t u H. destruct H; split; simpl; trivial.
 intro H1. split. split.
 unfold bswap. apply lc_at_bswap; try omega; trivial. apply H1.
 apply lc_at_weaken_ind with (k1 := 0); try omega.
 rewrite <- term_eq_term'; trivial.
 apply lc_at_weaken_ind with (k1 := 0); try omega.
 rewrite <- term_eq_term'; trivial. intro H1.
 replace t with (& & t). split. split.
 apply lc_at_bswap; try omega; trivial. apply H1.
 apply lc_at_weaken_ind with (k1 := 0); try omega.
 rewrite <- term_eq_term'; trivial. 
 apply lc_at_weaken_ind with (k1 := 0); try omega.
 rewrite <- term_eq_term'; trivial. 
 rewrite bswap_rec_id with (n := 0); reflexivity.
Qed.

Lemma lc_at_pctx_eqc : forall n t u, (p_contextual_closure eqc) t u  -> (lc_at n t <-> lc_at n u).
Proof.
 intros n t u H. generalize n; clear n.
 induction H; simpl. intro n. apply lc_at_eqc; trivial.
 split;  intro H1. destruct H1. split. 
 apply IHp_contextual_closure1; trivial.
 apply IHp_contextual_closure2; trivial.
 destruct H1. split. 
 apply IHp_contextual_closure1; trivial.
 apply IHp_contextual_closure2; trivial.
 case var_fresh with (L := L). intros x Fr. intro n.
 assert (Q : forall t, lc_at (S n) (t ^ x) <-> lc_at (S n) t).
   intro t1. apply lc_at_open'; try omega; trivial.
 split. intro H1. apply Q. apply H0; trivial. apply Q; trivial.
 intro H2. apply Q. apply H0; trivial. apply Q; trivial.
 case var_fresh with (L := L). intros x Fr. intro n.
 assert (Q : forall t, lc_at (S n) (t ^ x) <-> lc_at (S n) t).
   intro t1. apply lc_at_open'; try omega; trivial.
 split. intro H3. destruct H3. split.
 apply Q. apply H0; trivial. apply Q; trivial. 
 apply IHp_contextual_closure; trivial.
 intro H2. destruct H2. split.
 apply Q. apply H0; trivial. apply Q; trivial. 
 apply IHp_contextual_closure; trivial.
Qed. 


Lemma lc_at_eqC : forall n t t', t =e t' -> (lc_at n t <-> lc_at n t').
Proof.
 intros n t t' H. generalize n; clear n. 
 induction H. intro n. apply lc_at_pctx_eqc; trivial.
 intro n. apply (lc_at_pctx_eqc n) in H. rewrite H.
 apply IHtrans_closure.
Qed.

Lemma red_regular'_eqc : red_regular' eqc.
Proof.
   unfold red_regular'. intros t0 t1 H'. rewrite term_eq_term'. rewrite term_eq_term'.
   unfold term'. apply lc_at_eqc; trivial.
Qed.

Lemma pctx_eqc_fv : forall x t u, (p_contextual_closure eqc) t u  -> (x \in (fv t) <-> x \in (fv u)).
Proof.
 intros x t u H. induction H. induction H.
 split; trivial. simpl. split.
 intro H1. apply in_union in H1. case H1; clear H1. 
 intro H1. apply in_union in H1. case H1; clear H1. 
 intro H1. apply in_union. left. apply in_union. 
 left. unfold bswap. rewrite fv_bswap_rec; trivial.
 intro H1. apply in_union. right. trivial. 
 intro H1. apply in_union. left. apply in_union. right. trivial.  
 intro H1. apply in_union in H1. case H1; clear H1.
 intro H1. apply in_union in H1. case H1; clear H1.
 intro H1. apply in_union. left. apply in_union. 
 left. unfold bswap in H1. rewrite fv_bswap_rec in H1; trivial.
 intro H1. apply in_union. right. trivial. 
 intro H1. apply in_union. left. apply in_union. right; trivial.
 simpl. split. 
 intro H1. apply in_union in H1. case H1; clear H1.
 intro H1. apply in_union. left. apply IHp_contextual_closure1; trivial.
 intro H1. apply in_union. right; trivial. apply IHp_contextual_closure2; trivial.
 intro H1. apply in_union in H1. case H1; clear H1.
 intro H1. apply in_union. left. apply IHp_contextual_closure1; trivial.
 intro H1. apply in_union. right; trivial. apply IHp_contextual_closure2; trivial.
 simpl. pick_fresh z. apply notin_union in Fr. case Fr; clear Fr.
 intros H1 H2. apply notin_union in H1. case H1; clear H1. intros H1 H3.
 apply notin_union in H1. case H1; clear H1. intros H1 H4. 
 apply notin_singleton in H4. 
 assert (Q: (x \in fv (t ^ z) <-> x \in fv t)).
   unfold open. apply fv_open_. intro.
   apply H4. apply symmetry; trivial.
 assert (Q': (x \in fv (t' ^ z) <-> x \in fv t')).
   unfold open. apply fv_open_. intro.
   apply H4. apply symmetry; trivial.
 split. 
 intro H5. apply Q'. apply H0; trivial. apply Q; trivial.
 intro H5. apply Q.  apply H0; trivial. apply Q'; trivial.
 simpl. pick_fresh z. apply notin_union in Fr. case Fr; clear Fr.
 intros H2 H3. apply notin_union in H2. case H2; clear H2.
 intros H2 H4. apply notin_union in H2. case H2; clear H2.
 intros H2 H5. apply notin_union in H2. case H2; clear H2.
 intros H2 H6. apply notin_union in H2. case H2; clear H2.
 intros H2 H7. apply notin_singleton in H7. 
 assert (Q: (x \in fv (t ^ z) <-> x \in fv t)).
   unfold open. apply fv_open_. intro.
   apply H7. apply symmetry; trivial.
 assert (Q': (x \in fv (t' ^ z) <-> x \in fv t')).
   unfold open. apply fv_open_. intro.
   apply H7. apply symmetry; trivial.
 split. 
 intro H8. apply in_union in H8. apply in_union. case H8; clear H8; intro H8.
 left. apply Q'. apply H0; trivial. apply Q; trivial. 
 right. apply IHp_contextual_closure; trivial.
 intro H8. apply in_union in H8. apply in_union. case H8; clear H8; intro H8.
 left. apply Q. apply H0; trivial. apply Q'; trivial. 
 right. apply IHp_contextual_closure; trivial.
Qed.

Lemma eqC_fv : forall x t t', t =e t' -> ((x \in fv t) <-> (x \in fv t')).
Proof.
 intros x t t' H.  induction H.
 apply pctx_eqc_fv; trivial.
 apply (pctx_eqc_fv x) in H. rewrite H; trivial.
Qed.

Lemma red_regular_eqC : forall R, red_regular R -> 
                        red_regular (red_ctx_mod_eqC R).
Proof.
 intros R H. unfold red_regular. intros t t' H'.
 unfold red_ctx_mod_eqC in H'. case H'; clear H'; intros t0 H'.
 case H'; clear H'; intros u0 H'. 
 assert (Q : red_regular (contextual_closure R)).
   apply red_regular_ctx; trivial.
 unfold red_regular in Q. 
 assert (Q': term t0 /\ term u0).
   apply Q. apply H'.
 case H'; clear H'; intros H0 H1.
 case H1; clear H1; intros H1 H2.
 apply (lc_at_eqC 0) in H0. apply (lc_at_eqC 0) in H2.
 rewrite term_eq_term'. rewrite term_eq_term'. 
 rewrite term_eq_term' in Q'. rewrite term_eq_term' in Q'.
 unfold term'. split; [apply H0; apply Q' | apply H2; apply Q'].
Qed.

Lemma red_out_eqc : red_out eqc.
Proof.
 intros x t t' u T H. destruct H; simpl. apply eqc_rf.
 rewrite (subst_bswap_rec 0). apply eqc_rx.
 apply subst_term; trivial.
 apply subst_term; trivial. 
 rewrite <- term_eq_term'; trivial.
Qed.

Lemma red_out_pctx_eqc : red_out (p_contextual_closure eqc).
Proof.
 apply red_out_pctx. apply red_out_eqc.
Qed.


Lemma red_out_pctx_eqc' : forall x t u u', term t -> term u -> 
                        p_contextual_closure eqc u u' -> 
                        p_contextual_closure eqc ([x ~> u]t) ([x ~> u']t).
Proof.
 intros x t u u' Tt Tu H.
 apply term_size_induction with (t := t); trivial; simpl.
 intro z. case (z == x). intro; trivial. intro. apply p_redex. apply eqc_rf.
 intros t1 B Ht1. apply p_abs_in with (L := {{x}} \u (fv t1)).
 intros z Fr. apply notin_union in Fr. destruct Fr.
 apply notin_singleton in H0. 
 rewrite subst_open_var; trivial.
 rewrite subst_open_var; trivial.
 apply Ht1; trivial. apply body_to_term; trivial.
 apply (lc_at_pctx_eqc 0) in H. 
 rewrite <- term_eq_term' in H.
 rewrite <- term_eq_term' in H. apply H; trivial.
 intros t1 t2 Tt1 Ht1 Tt2 Ht2. apply p_app; trivial.
 intros t1 t2 Tt2 Ht2 B Ht1. 
 apply p_subst with (L := {{x}} \u (fv t1)); trivial.
 intros z Fr. apply notin_union in Fr. destruct Fr.
 apply notin_singleton in H0. 
 rewrite subst_open_var; trivial.
 rewrite subst_open_var; trivial.
 apply Ht1; trivial. apply body_to_term; trivial.
 apply (lc_at_pctx_eqc 0) in H. 
 rewrite <- term_eq_term' in H.
 rewrite <- term_eq_term' in H. 
 apply H; trivial.
Qed.


Lemma red_out_eqC : red_out eqC.
Proof.
 intros x u t' t T H. induction H.
 apply one_step_reduction. apply red_out_pctx_eqc; trivial.
 apply transitive_reduction with (u := [x ~> u]u0); trivial. 
 apply red_out_pctx_eqc; trivial.
Qed.


Lemma red_all_eqC : forall x t t' u u', term t -> term u ->
                     t =e t' -> u =e u' -> [x ~> u]t =e [x ~> u']t'.
Proof.
 intros x t t' u u' Tt Tu H0 H1. 
 apply transitive_closure_composition with (u := [x ~> u]t').
 clear H1 Tt. induction H0.
 apply one_step_reduction. apply red_out_pctx_eqc; trivial.
 apply transitive_reduction with (u := ([x ~> u]u0)); trivial.
 apply red_out_pctx_eqc; trivial. 
 assert (term t').
  apply (lc_at_eqC 0) in H0.
  rewrite <- term_eq_term' in H0.
  rewrite <- term_eq_term' in H0.
  apply H0; trivial.
 clear H0 Tt. induction H1.
 apply one_step_reduction. apply red_out_pctx_eqc'; trivial.
 apply transitive_reduction with (u := ([x ~> u]t')); trivial.
 apply red_out_pctx_eqc'; trivial.
 apply IHtrans_closure. 
 apply (lc_at_pctx_eqc 0) in H0.
 rewrite <- term_eq_term' in H0.
 rewrite <- term_eq_term' in H0.
 apply H0; trivial.
Qed. 

Lemma red_rename_pctx_eqc : red_rename (p_contextual_closure eqc).
Proof.
 intros_all.
 rewrite* (@subst_intro x t). 
 rewrite* (@subst_intro x t').
 apply red_out_pctx_eqc; trivial.
Qed.

Lemma red_rename_eqC : red_rename eqC.
Proof.
 intros_all.
 rewrite* (@subst_intro x t). 
 rewrite* (@subst_intro x t').
 apply red_out_eqC; trivial.
Qed.

                
Lemma red_out_mod_eqC : forall R, red_regular R -> red_out R ->
                    red_out (red_ctx_mod_eqC R).
Proof.
 intros R H1 H2. unfold red_out. intros x t t' u T H3.
 unfold red_ctx_mod_eqC in *|-*.
 case H3; clear H3; intros t0 H3.
 case H3; clear H3; intros u0 H3.
 case H3; clear H3; intros H3 H4. 
 case H4; clear H4; intros H4 H5.
 assert (Q: red_regular (contextual_closure R)).
   apply red_regular_ctx; trivial.
 assert (Q': red_out (contextual_closure R)).
   apply red_out_ctx; trivial.
 exists ([x ~> t]t0) ([x ~> t]u0). split.
 apply red_out_eqC; try reflexivity; trivial.
 split. apply Q'; trivial.
 apply red_out_eqC; try reflexivity; trivial.
Qed.


Lemma red_not_fv_mod_eqC : forall R, red_not_fv R -> red_not_fv (red_ctx_mod_eqC R).
Proof.
 intros. apply red_not_fv_ctx in H. 
 unfold red_not_fv in *|-*. intros. 
 unfold red_ctx_mod_eqC in H0.
 case H0; clear H0; intros t0 H0.
 case H0; clear H0; intros t1 H0.
 case H0; clear H0; intros H2 H3.
 case H3; clear H3; intros H3 H4.
 apply (H x) in H3.
 apply (eqC_fv x) in H4. intro H5.
 assert (Q : x \in fv t1).
           apply H4; trivial.
 contradiction.
 apply (eqC_fv x) in H2.
 intro H5. assert (Q : x \in fv t).
           apply H2; trivial.
 contradiction.
Qed.

Lemma red_fv_mod_eqC : forall R, red_fv R -> red_fv (red_ctx_mod_eqC R).
Proof.  
 intros. apply red_fv_ctx in H. 
 unfold red_fv in *|-*. intros.
 unfold red_ctx_mod_eqC in H0.
 case H0; clear H0; intros t0 H0.
 case H0; clear H0; intros t1 H0.
 case H0; clear H0; intros H2 H3.
 case H3; clear H3; intros H3 H4.
 apply (eqC_fv x) in H2. apply H2.
 apply H with (t' := t1); trivial.
 apply (eqC_fv x) in H4. 
 apply H4; trivial.
Qed.


Lemma pctx_eqc_open : forall n t t' u, term u -> p_contextual_closure eqc t t' -> 
                     p_contextual_closure eqc ({n ~> u}t) ({n ~> u}t').
Proof.
  intros n t t' u Tu H. generalize n; clear n.  
  induction H. destruct H. intro n. apply p_redex. apply eqc_rf.
  intro n. unfold open. simpl. 
  replace ({S (S n) ~> u}(& t)) with (& ({S (S n) ~> u}t)).
  replace ({S n ~> u}v) with v. replace ({n ~> u}v) with v.
  replace ({S n ~> u}u0) with u0. replace ({n ~> u}u0) with u0.
  apply p_redex. apply eqc_rx; trivial. 
  rewrite open_lc_at; trivial. 
  apply lc_at_weaken_ind with (k1 := 0); try omega.
  rewrite <- term_eq_term'; trivial.
  rewrite open_lc_at; trivial. 
  apply lc_at_weaken_ind with (k1 := 0); try omega.
  rewrite <- term_eq_term'; trivial.
  rewrite open_lc_at; trivial. 
  apply lc_at_weaken_ind with (k1 := 0); try omega.
  rewrite <- term_eq_term'; trivial.
  rewrite open_lc_at; trivial. 
  apply lc_at_weaken_ind with (k1 := 0); try omega.
  rewrite <- term_eq_term'; trivial.
  unfold bswap. rewrite <- bswap_open_rec; try omega; trivial.
  apply lc_at_weaken_ind with (k1 := 0); try omega.
  rewrite <- term_eq_term'; trivial.
  simpl; intro n. apply p_app; trivial.
  simpl; intro n. apply p_abs_in with (L := (fv u) \u L).
  intros x H2. apply notin_union in H2. case H2; clear H2.
  intros H2 H3. unfold open in *|-*. 
  replace ({0 ~> pterm_fvar x}({S n ~> u}t))
  with ({S n ~> u}({0 ~> pterm_fvar x}t)).
  replace ({0 ~> pterm_fvar x}({S n ~> u}t'))
  with ({S n ~> u}({0 ~> pterm_fvar x}t')).
  apply H0; trivial.
  rewrite subst_com; trivial. omega.
  rewrite subst_com; trivial. omega.
  simpl; intro n. apply p_subst with (L := (fv u) \u L); trivial.
  intros x H2. apply notin_union in H2. case H2; clear H2.
  intros H2 H3. unfold open in *|-*. 
  replace ({0 ~> pterm_fvar x}({S n ~> u}t))
  with ({S n ~> u}({0 ~> pterm_fvar x}t)).
  replace ({0 ~> pterm_fvar x}({S n ~> u}t'))
  with ({S n ~> u}({0 ~> pterm_fvar x}t')).
  apply H0; trivial.
  rewrite subst_com; trivial. omega.
  rewrite subst_com; trivial. omega. 
Qed. 


Lemma eqC_open : forall n t t' u, term u -> t =e t'-> (open_rec n u t) =e (open_rec n u t').
Proof.
 intros n t t' u Tu H. induction H. 
 apply one_step_reduction. apply pctx_eqc_open; trivial.
 apply transitive_reduction with (u := ({n ~> u}u0)); trivial.
 apply pctx_eqc_open; trivial.
Qed.

Lemma eqC_open_var : forall (x:var) t1 t2 u, x \notin (fv t1) -> 
	x \notin (fv t2) -> term u -> (t1 ^ x =e t2 ^ x) -> ((t1^^u) =e (t2^^u)).
Proof.
  intros x t1 t2 u H1 H2 T H3.
  assert (Q : subst x u (t1 ^ x) =e subst x u (t2 ^ x)).
   apply red_out_eqC; trivial. 
  rewrite subst_intro with (x := x); trivial.
  rewrite subst_intro with (x := x) (t := t2); trivial.
Qed.

(* ********************************************************************** *)
(** =e Rewriting *)

Instance rw_eqC_red : forall R, Proper (eqC ==> eqC ==> iff) (red_ctx_mod_eqC R).
Proof.
 intros_all. split. intro H1.
 unfold red_ctx_mod_eqC in *|-*.
 destruct H1. destruct H1. destruct H1. destruct H2.
 exists x1. exists x2. split. 
 rewrite <- H; trivial. split; trivial.
 rewrite <- H0; trivial. intro H1.
 unfold red_ctx_mod_eqC in *|-*.
 destruct H1. destruct H1. destruct H1. destruct H2.
 exists x1. exists x2. split. 
 rewrite <- H1; trivial. split; trivial.
 rewrite H3. rewrite H0. 
 reflexivity.
Qed.

Instance rw_eqC_trs : forall R, Proper (eqC ==> eqC ==> iff) (trans_closure (red_ctx_mod_eqC R)).
Proof.
 intros_all. split. intro H'.
 apply transitive_star_derivation'.
 apply transitive_star_derivation' in H'.
 case H'. clear H'. intro H1. left.
 rewrite <- H. rewrite <- H0; trivial.
 clear H'. intro H1. right. destruct H1.
 destruct H1. destruct H2. destruct H2.
 exists x1. split. rewrite <- H; trivial.
 exists x2. split; trivial. rewrite <- H0; trivial.
 intro H'.
 apply transitive_star_derivation'.
 apply transitive_star_derivation' in H'.
 case H'. clear H'. intro H1. left.
 rewrite H. rewrite H0; trivial.
 clear H'. intro H1. right. destruct H1.
 destruct H1. destruct H2. destruct H2.
 exists x1. split. rewrite H; trivial.
 exists x2. split; trivial. rewrite H0; trivial.
Qed.

Instance rw_eqC_lc_at : forall n, Proper (eqC ==> iff) (lc_at n).
Proof.
 intros_all. apply lc_at_eqC; trivial.
Qed.

Instance rw_eqC_body : Proper (eqC ==> iff) body.
Proof.
 intros_all. rewrite body_eq_body'. rewrite body_eq_body'.
 unfold body'. rewrite H. reflexivity.
Qed.

Instance rw_eqC_term : Proper (eqC ==> iff) term.
Proof.
 intros_all. rewrite term_eq_term'. rewrite term_eq_term'.
 unfold term'. rewrite H. reflexivity.
Qed.

Instance rw_eqC_fv : Proper (eqC ==> VarSet.Equal) fv.
Proof.
 intros_all. apply eqC_fv; trivial.
Qed.

Instance rw_eqC_app : Proper (eqC ++> eqC ++> eqC) pterm_app.
Proof. 
 intros_all. apply transitive_closure_composition with (u:=pterm_app y x0).
 clear H0. induction H. apply one_step_reduction. apply p_app; trivial.
 apply p_redex. apply eqc_rf. apply transitive_reduction with (u:=pterm_app u x0); trivial.
 apply p_app; trivial. apply p_redex. apply eqc_rf.
 clear H. induction H0. apply one_step_reduction. apply p_app; trivial.
 apply p_redex. apply eqc_rf. apply transitive_reduction with (u:=pterm_app y u); trivial.
 apply p_app; trivial. apply p_redex. apply eqc_rf.
Qed.

Instance rw_eqC_subst_right : forall t, Proper (eqC ++> eqC) (pterm_sub t).
Proof.
 intros_all. induction H.
 apply one_step_reduction. apply p_subst with (L := {}); trivial. intros.
 apply p_redex. apply eqc_rf.
 apply transitive_reduction with (u:= t[u]); trivial.
 apply p_subst with (L := {}); trivial. intros.
 apply p_redex. apply eqc_rf.
Qed.

Instance SN_ind_mod_eqC : forall n R, Proper (eqC ==> iff) (SN_ind n (red_ctx_mod_eqC R)).
Proof.
 intros_all. split. intro H'.
 apply SN_intro. intros z H''. inversion H'.
 case (H0 z). rewrite H; trivial. intros k H1. destruct H1.
 exists k; split; try omega; trivial. intro H'.
 apply SN_intro. intros z H''. inversion H'.
 case (H0 z). rewrite <- H; trivial. intros k H1. destruct H1.
 exists k; split; try omega; trivial.
Qed.

Instance NF_mod_eqC : forall R, Proper (eqC ==> iff) (NF (red_ctx_mod_eqC R)).
Proof.
 intros_all. split; intro H'.
 intros t0 H0. rewrite <- H in H0.
 apply (H' t0); trivial. 
 intros t0 H0. rewrite H in H0.
 apply (H' t0); trivial. 
Qed.


(* ********************************************************************** *)

Lemma ctx_to_mod_eqC : forall R t t', contextual_closure R t t' -> red_ctx_mod_eqC R t t'.
Proof.
 intros R t t' H. 
 exists t t'. split.
 reflexivity. split; trivial.
 reflexivity.
Qed.

Lemma eqC_abs_in_close : forall x L t t', 
                              term t -> eqC t t' -> x \notin L ->
                              eqC (pterm_abs (close t x)) (pterm_abs (close t' x)).
Proof.
 intros x L t t' B H Fr. 
 apply trs_pctx_abs_in_close with (L := L); trivial.
 apply red_regular'_eqc. apply red_out_eqc.
Qed.

Lemma eqC_subst_left_close : forall x L t t' u,  term t -> term u ->
                              eqC t t' -> x \notin L ->
                              eqC ((close t x)[u]) ((close t' x)[u]).
Proof.
 intros x L t t' u Tt Tu H Fr. 
 apply trs_pctx_subst_close with (L := L); trivial.
 apply red_regular'_eqc. apply red_out_eqc.
 intros. apply eqc_rf. apply one_step_reduction. apply p_redex. apply eqc_rf.
Qed.

Lemma eqC_abs_in : forall L t t', body t -> 
                              (forall x, x \notin L -> eqC (t^x) (t'^x)) ->
                              eqC (pterm_abs t) (pterm_abs t').
Proof.
 intros L t t' B H. 
 apply trs_pctx_abs_in with (L := L); trivial.
 apply red_regular'_eqc. apply red_out_eqc.
Qed.

Lemma eqC_subst_left : forall L t t' u, body t ->  term u ->
                              (forall x, x \notin L -> eqC (t^x) (t'^x)) ->
                              eqC (t[u]) (t'[u]).
Proof.
 intros L t t' u B T H. 
 apply trs_pctx_subst with (L := L); trivial.
 apply red_regular'_eqc. apply red_out_eqc.
 intros. apply eqc_rf. apply one_step_reduction. apply p_redex. apply eqc_rf.
Qed.

Lemma mod_eqC_app_left : forall R t t' u, term u -> red_ctx_mod_eqC R t t' -> 
                         red_ctx_mod_eqC R (pterm_app t u) (pterm_app t' u).
Proof. 
 intros R t t' u T H.
 case H; clear H; intros t0 H. case H; clear H; intros t1 H.
 destruct H. destruct H0. 
 exists (pterm_app t0 u) (pterm_app t1 u). split. 
 rewrite H. reflexivity. split.
 apply app_left; trivial.
 rewrite H1. reflexivity.
Qed.

Lemma trs_mod_eqC_app_left : forall R t t' u, term u -> trans_closure (red_ctx_mod_eqC R) t t' -> 
                         trans_closure (red_ctx_mod_eqC R) (pterm_app t u) (pterm_app t' u).
Proof. 
 intros R t t' u T H. induction H.
 apply one_step_reduction. apply  mod_eqC_app_left; trivial.
 apply transitive_reduction with (u := pterm_app u0 u); trivial.
 apply  mod_eqC_app_left; trivial.
Qed.

Lemma str_mod_eqC_app_left : forall R t t' u, term u -> star_closure (red_ctx_mod_eqC R) t t' -> 
                         star_closure (red_ctx_mod_eqC R) (pterm_app t u) (pterm_app t' u).
Proof. 
 intros R t t' u T H. induction H.
 apply reflexive_reduction. apply  star_trans_reduction.
 apply trs_mod_eqC_app_left; trivial.
Qed.


Lemma mod_eqC_app_right : forall R t t' u, term u -> red_ctx_mod_eqC R t t' -> 
                         red_ctx_mod_eqC R (pterm_app u t) (pterm_app u t').
Proof. 
 intros R t t' u T H.
 case H; clear H; intros t0 H. case H; clear H; intros t1 H.
 destruct H. destruct H0. 
 exists (pterm_app u t0) (pterm_app u t1). split. 
 rewrite H. reflexivity. split.
 apply app_right; trivial.
 rewrite H1. reflexivity.
Qed.

Lemma trs_mod_eqC_app_right : forall R t u u', term t -> trans_closure (red_ctx_mod_eqC R) u u' -> 
                         trans_closure (red_ctx_mod_eqC R) (pterm_app t u) (pterm_app t u').
Proof. 
 intros R t u u' T H. induction H.
 apply one_step_reduction. apply  mod_eqC_app_right; trivial.
 apply transitive_reduction with (u := pterm_app t u); trivial.
 apply  mod_eqC_app_right; trivial.
Qed.

Lemma str_mod_eqC_app_right : forall R t u u', term t -> star_closure (red_ctx_mod_eqC R) u u' -> 
                         star_closure (red_ctx_mod_eqC R) (pterm_app t u) (pterm_app t u').
Proof. 
 intros R t u u' T H. induction H.
 apply reflexive_reduction. apply  star_trans_reduction.
 apply trs_mod_eqC_app_right; trivial.
Qed.


Lemma mod_eqC_subst_right : forall R t u u', body t -> red_ctx_mod_eqC R u u' -> 
                         red_ctx_mod_eqC R (pterm_sub t u) (pterm_sub t u').
Proof. 
 intros R t u u' B H.
 case H; clear H; intros u0 H. case H; clear H; intros u1 H.
 destruct H. destruct H0. 
 exists (t[u0]) (t[u1]). split. 
 rewrite H. reflexivity. split.
 apply subst_right; trivial.
 rewrite H1. reflexivity.
Qed.

Lemma trs_mod_eqC_subst_right : forall R t u u', body t -> trans_closure (red_ctx_mod_eqC R) u u' -> 
                         trans_closure (red_ctx_mod_eqC R) (t[u]) (t[u']).
Proof. 
 intros R t u u' T H. induction H.
 apply one_step_reduction. apply  mod_eqC_subst_right; trivial.
 apply transitive_reduction with (u := t[u]); trivial.
 apply  mod_eqC_subst_right; trivial.
Qed.

Lemma str_mod_eqC_subst_right : forall R t u u', body t -> star_closure (red_ctx_mod_eqC R) u u' -> 
                         star_closure (red_ctx_mod_eqC R) (t[u]) (t[u']).
Proof. 
 intros R t u u' T H. induction H.
 apply reflexive_reduction. apply  star_trans_reduction.
 apply trs_mod_eqC_subst_right; trivial.
Qed.

Lemma mod_eqC_abs_in_close : forall x R L t t', red_regular R -> red_out R -> 
                              red_ctx_mod_eqC R t t' -> x \notin L ->
                              red_ctx_mod_eqC R (pterm_abs (close t x)) (pterm_abs (close t' x)).
Proof.
 intros x R L t t' Reg Out H Fr.
 case H; clear H; intros t0 H. case H; clear H; intros t1 H.
 destruct H. destruct H0.
 exists (pterm_abs (close t0 x)) (pterm_abs (close t1 x)). split.
 apply eqC_abs_in_close with (L := L); trivial. rewrite H.
 apply red_regular_ctx in Reg. apply Reg in H0. apply H0. split.
 apply ctx_abs_in_close with (L := L); trivial.
 apply eqC_abs_in_close with (L := L); trivial. 
 apply red_regular_ctx in Reg. apply Reg in H0. apply H0.
Qed.

Lemma mod_eqC_abs_in : forall R L t t', red_regular R -> red_out R -> 
                      (forall x, x \notin L -> red_ctx_mod_eqC R (t ^ x) (t' ^ x)) ->
                       red_ctx_mod_eqC R (pterm_abs t) (pterm_abs t').
Proof. 
 intros R L t t' Reg Out H.  case var_fresh with (L := L \u (fv t) \u (fv t')). intros x Fr.
 apply notin_union in Fr. destruct Fr. apply notin_union in H0. destruct H0.
 assert (Q: red_ctx_mod_eqC R (t ^ x) (t' ^ x)). apply H; trivial. clear H.
 gen_eq t2 : (t ^ x). gen_eq t3 : (t' ^ x). intros Ht2 Ht3.
 replace t with (close t2 x). replace t' with (close t3 x). clear Ht2 Ht3. 
 apply mod_eqC_abs_in_close with (L := L); trivial.
 rewrite Ht2. rewrite <- close_open_term; trivial. 
 rewrite Ht3. rewrite <- close_open_term; trivial.
Qed.


Lemma trs_mod_eqC_abs_in : forall R L t t', red_regular R -> red_out R -> 
                      (forall x, x \notin L -> trans_closure (red_ctx_mod_eqC R) (t ^ x) (t' ^ x)) ->
                       trans_closure (red_ctx_mod_eqC R) (pterm_abs t) (pterm_abs t').
Proof.
 intros R L t t' H0 H1 H2.  case var_fresh with (L := L \u (fv t) \u (fv t')). intros x Fr.
 apply notin_union in Fr. destruct Fr. apply notin_union in H. destruct H.
 assert (Q: trans_closure (red_ctx_mod_eqC R) (t ^ x) (t' ^ x)). apply H2; trivial. clear H2.
 gen_eq t0 : (t ^ x). gen_eq t1 : (t' ^ x). intros Ht1 Ht0.
 replace t with (close t0 x). replace t' with (close t1 x).
 clear Ht0 Ht1. induction Q.
 apply one_step_reduction. apply mod_eqC_abs_in_close with (L := L); trivial.
 apply transitive_reduction with (u := pterm_abs (close u x)); trivial.
 apply mod_eqC_abs_in_close with (L := L); trivial. 
 rewrite Ht1. rewrite <- close_open_term; trivial. 
 rewrite Ht0. rewrite <- close_open_term; trivial.
Qed.

Lemma str_mod_eqC_abs_in : forall R L t t', red_regular R -> red_out R -> 
                      (forall x, x \notin L -> star_closure (red_ctx_mod_eqC R) (t ^ x) (t' ^ x)) ->
                       star_closure (red_ctx_mod_eqC R) (pterm_abs t) (pterm_abs t').
Proof.
 intros R L t t' H0 H1 H2.  case var_fresh with (L := L \u (fv t) \u (fv t')). intros x Fr.
 apply notin_union in Fr. destruct Fr. apply notin_union in H. destruct H.
 assert (Q: star_closure (red_ctx_mod_eqC R) (t ^ x) (t' ^ x)). apply H2; trivial. clear H2.
 gen_eq t0 : (t ^ x). gen_eq t1 : (t' ^ x). intros Ht1 Ht0.
 replace t with (close t0 x). replace t' with (close t1 x).
 clear Ht0 Ht1. destruct Q. apply reflexive_reduction.  
 apply star_trans_reduction. induction H2.
 apply one_step_reduction. apply mod_eqC_abs_in_close with (L := L); trivial.
 apply transitive_reduction with (u := pterm_abs (close u x)); trivial.
 apply mod_eqC_abs_in_close with (L := L); trivial. 
 rewrite Ht1. rewrite <- close_open_term; trivial. 
 rewrite Ht0. rewrite <- close_open_term; trivial.
Qed.


Lemma mod_eqC_subst_left_close : forall x R L t t' u, red_regular R -> red_out R -> 
                              term u ->
                              red_ctx_mod_eqC R t t' -> x \notin L ->
                              red_ctx_mod_eqC R ((close t x)[u]) ((close t' x)[u]).
Proof.
 intros x R L t t' u Reg Out T H Fr.
 case H; clear H; intros t0 H. case H; clear H; intros t1 H.
 destruct H. destruct H0.
 exists ((close t0 x)[u]) ((close t1 x)[u]). split.
 apply eqC_subst_left_close with (L := L); trivial. rewrite H.
 apply red_regular_ctx in Reg. apply Reg in H0. apply H0. split.
 apply ctx_subst_left_close with (L := L); trivial.
 apply eqC_subst_left_close with (L := L); trivial. 
 apply red_regular_ctx in Reg. apply Reg in H0. apply H0.
Qed.

Lemma mod_eqC_subst_left : forall R L t t' u, red_regular R -> red_out R -> term u ->
                      (forall x, x \notin L -> red_ctx_mod_eqC R (t ^ x) (t' ^ x)) ->
                       red_ctx_mod_eqC R (t[u]) (t'[u]).
Proof. 
 intros R L t t' u Reg Out T H.  case var_fresh with (L := L \u (fv t) \u (fv t')). intros x Fr.
 apply notin_union in Fr. destruct Fr. apply notin_union in H0. destruct H0.
 assert (Q: red_ctx_mod_eqC R (t ^ x) (t' ^ x)). apply H; trivial. clear H.
 gen_eq t2 : (t ^ x). gen_eq t3 : (t' ^ x). intros Ht2 Ht3.
 replace t with (close t2 x). replace t' with (close t3 x). clear Ht2 Ht3. 
 apply mod_eqC_subst_left_close with (L := L); trivial.
 rewrite Ht2. rewrite <- close_open_term; trivial. 
 rewrite Ht3. rewrite <- close_open_term; trivial.
Qed.


Lemma trs_mod_eqC_subst_left : forall R L t t' u, red_regular R -> red_out R -> term u ->
                              (forall x, x \notin L -> trans_closure (red_ctx_mod_eqC R) (t ^ x) (t' ^ x)) ->
                              trans_closure (red_ctx_mod_eqC R) (t[u]) (t'[u]).
Proof.
 intros R L t t' u H0 H1 T H2.  case var_fresh with (L := L \u (fv t) \u (fv t')). intros x Fr.
 apply notin_union in Fr. destruct Fr. apply notin_union in H. destruct H.
 assert (Q: trans_closure (red_ctx_mod_eqC R) (t ^ x) (t' ^ x)). apply H2; trivial. clear H2.
 gen_eq t0 : (t ^ x). gen_eq t1 : (t' ^ x). intros Ht1 Ht0.
 replace t with (close t0 x). replace t' with (close t1 x).
 clear Ht0 Ht1. induction Q.
 apply one_step_reduction. apply mod_eqC_subst_left_close with (L := L); trivial.
 apply transitive_reduction with (u := (close u0 x)[u]); trivial.
 apply mod_eqC_subst_left_close with (L := L); trivial. 
 rewrite Ht1. rewrite <- close_open_term; trivial. 
 rewrite Ht0. rewrite <- close_open_term; trivial.
Qed.


Lemma str_mod_eqC_subst_left : forall R L t t' u, red_regular R -> red_out R -> term u ->
                      (forall x, x \notin L -> star_closure (red_ctx_mod_eqC R) (t ^ x) (t' ^ x)) ->
                       star_closure (red_ctx_mod_eqC R) (t[u]) (t'[u]).
Proof.
 intros R L t t' u H0 H1 T H2.  case var_fresh with (L := L \u (fv t) \u (fv t')). intros x Fr.
 apply notin_union in Fr. destruct Fr. apply notin_union in H. destruct H.
 assert (Q: star_closure (red_ctx_mod_eqC R) (t ^ x) (t' ^ x)). apply H2; trivial. clear H2.
 gen_eq t0 : (t ^ x). gen_eq t1 : (t' ^ x). intros Ht1 Ht0.
 replace t with (close t0 x). replace t' with (close t1 x).
 clear Ht0 Ht1. destruct Q. apply reflexive_reduction.  
 apply star_trans_reduction. induction H2.
 apply one_step_reduction. apply mod_eqC_subst_left_close with (L := L); trivial.
 apply transitive_reduction with (u := (close u0 x)[u]); trivial.
 apply mod_eqC_subst_left_close with (L := L); trivial. 
 rewrite Ht1. rewrite <- close_open_term; trivial. 
 rewrite Ht0. rewrite <- close_open_term; trivial.
Qed.






(*** about NF and SN modulo =e ***)

Lemma eqC_SN_app : forall n R t u, red_regular R -> term t -> term u -> 
                   SN_ind n (red_ctx_mod_eqC R) (pterm_app t u) ->
                   SN_ind n (red_ctx_mod_eqC R) t /\ SN_ind n (red_ctx_mod_eqC R) u.
Proof.
 intros n R t u Reg. 
 generalize t u; clear t u.  
 induction n.  intros. split; rewrite <- NF_eq_SN0 in *|-*; unfold NF in *|-*. 
 intros t' H'. apply (H1 (pterm_app t' u)). apply mod_eqC_app_left; trivial.
 intros u' H'. apply (H1 (pterm_app t u')). apply mod_eqC_app_right; trivial.
 intros t u Tt Tu H. destruct H. split. 
 apply SN_intro. intros t' H'. exists n. split; try omega. 
 apply IHn with (t := t') (u := u); trivial. apply red_regular_eqC in Reg.
 apply Reg in H'. apply H'. case (H (pterm_app t' u)). apply mod_eqC_app_left; trivial. 
 intros k H''. apply WSN with (k := k). omega. apply H''.
 apply SN_intro. intros u' H'. exists n. split; try omega. 
 apply IHn with (t := t) (u := u'); trivial. apply red_regular_eqC in Reg.
 apply Reg in H'. apply H'. case (H (pterm_app t u')). apply mod_eqC_app_right; trivial. 
 intros k H''. apply WSN with (k := k). omega. apply H''.
Qed. 


Lemma eqC_SN_abs : forall x n R t, red_regular R -> red_out R -> 
               SN_ind n (red_ctx_mod_eqC R) (pterm_abs t) ->
               x \notin (fv t) -> SN_ind n (red_ctx_mod_eqC R) (t ^ x).
Proof.
 intros x n R t Reg Out.
 generalize t; clear t. 
 generalize Out. intro Out'. apply red_out_mod_eqC in Out; trivial. 
 generalize Reg. intro Reg'. apply red_regular_eqC in Reg. 
 apply red_out_to_rename in Out.
 induction n. intros. 
 apply SN0_to_NF in H. 
 apply NF_to_SN0; unfold NF in *|-*.
 intros t' H'. gen_eq t0 : (close t' x). intro H1.
 replace t' with (t0 ^ x) in H'.
 assert (Q: red_ctx_mod_eqC R (pterm_abs t) (pterm_abs t0)).
    apply mod_eqC_abs_in with (L := {{x}}); trivial. intros z H2. 
    apply notin_singleton in H2. apply Out with (x := x); trivial.
    rewrite H1. apply fv_close'.
 apply False_ind. apply (H (pterm_abs t0)); trivial.
 rewrite H1. rewrite open_close_var with (x := x).
 reflexivity. apply Reg in H'. apply H'.
 intros. destruct H. apply SN_intro.
 intros. exists n. split; try omega.
 gen_eq t0 : (close t' x). intro H2.
 replace t' with (t0 ^ x). replace t' with (t0 ^ x) in H1.
 apply IHn; trivial. case (H (pterm_abs t0)); trivial.
 apply  mod_eqC_abs_in with (L := {{x}}); trivial.
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


Lemma eqC_SN_sub : forall x n R t u, red_regular R -> red_out R -> 
               body t -> term u -> x \notin (fv t) -> 
               SN_ind n (red_ctx_mod_eqC R) (t[u]) ->
               SN_ind n (red_ctx_mod_eqC R) (t ^ x) /\
               SN_ind n (red_ctx_mod_eqC R) u.
Proof.
 intros x n R t u Reg Out B T.
 generalize t u B T; clear t u B T. 
 generalize Out. intro Out'. apply red_out_mod_eqC in Out; trivial. 
 generalize Reg. intro Reg'. apply red_regular_eqC in Reg. 
 apply red_out_to_rename in Out.
 induction n. intros. rewrite <- NF_eq_SN0 in *|-*; unfold NF in *|-*.
 split. intros t' H'. gen_eq t0 : (close t' x). intro H1.
 replace t' with (t0 ^ x) in H'.
 assert (Q: red_ctx_mod_eqC R (t[u]) (t0[u])).
    apply mod_eqC_subst_left with (L := {{x}}); trivial. intros z H2. 
    apply notin_singleton in H2. apply Out with (x := x); trivial.
    rewrite H1. apply fv_close'.
 apply (H0 (t0[u])); trivial.
 rewrite H1. rewrite open_close_var with (x := x).
 reflexivity. apply Reg in H'. apply H'.
 rewrite <- NF_eq_SN0 in *|-*; unfold NF in *|-*. intros u' H'.
 apply (H0 (t[u'])). apply mod_eqC_subst_right; trivial.
 intros. split. destruct H0. apply SN_intro.
 intros. exists n. split; try omega.
 gen_eq t0 : (close t' x). intro H2.
 replace t' with (t0 ^ x). replace t' with (t0 ^ x) in H1.
 apply IHn with (u := u); trivial.
 rewrite body_eq_body'. unfold body'.
 apply Reg in H1. destruct H1.
 rewrite term_eq_term' in H3. unfold term' in H3. unfold open in H3.
 rewrite lc_at_open with (u := pterm_fvar x); trivial.
 rewrite H2. apply fv_close'. case (H0 (t0[u])); trivial.
 apply mod_eqC_subst_left with (L := {{x}}); trivial.
 intros z H3. apply notin_singleton in H3. 
 apply Out with (x := x); trivial.
 rewrite H2. apply fv_close'. intros k H3. destruct H3.
 apply WSN with (k := k); try omega; trivial.
 rewrite H2. rewrite open_close_var with (x := x).
 reflexivity. apply Reg in H1. apply H1.
 rewrite H2. rewrite open_close_var with (x := x).
 reflexivity. apply Reg in H1. apply H1. 
 apply SN_intro. intros u' H'. exists n; split; try omega.
 apply (IHn t u'); trivial. apply Reg in H'. apply H'. 
 destruct H0. case (H0 (t[u'])). apply mod_eqC_subst_right; trivial.
 intros k H1. destruct H1.
 apply WSN with (k := k); try omega; trivial.
Qed.


Lemma eqC_SN_app_list : forall n R t lu, red_regular R -> term t -> term %% lu -> 
                   SN_ind n (red_ctx_mod_eqC R) (t // lu) ->
                   SN_ind n (red_ctx_mod_eqC R) t /\ SN_ind n (red_ctx_mod_eqC R) %% lu.
Proof.
 intros n R t lu Reg. generalize n t; clear n t.
 induction lu; simpl. intros n t T H0 H. split; trivial.
 intros n t T H0 H. destruct H0. apply eqC_SN_app in H; trivial. destruct H.
 assert (Q : SN_ind n (red_ctx_mod_eqC R) t /\ SN_ind n (red_ctx_mod_eqC R) %% lu). 
  apply IHlu; trivial.
 clear IHlu. destruct Q. split; trivial. split; trivial.
 rewrite term_mult_app. split; trivial. 
Qed. 

Lemma red_h_mult_app : forall R t t' lu, term %% lu -> (red_ctx_mod_eqC R) t t' -> (red_ctx_mod_eqC R) (t // lu) (t' // lu).
Proof.
 intros R t t' lu Tlu H. induction lu; simpl in *|-*; trivial.
 destruct Tlu. apply mod_eqC_app_left; trivial.
 apply IHlu; trivial.
Qed. 

Lemma red_t_mult_app : forall R t lu lu', term t -> term %% lu -> R_list (red_ctx_mod_eqC R) lu lu' -> (red_ctx_mod_eqC R) (t // lu) (t // lu').
Proof.
 intros R t lu lu' Tt Tlu H. unfold R_list in H.
 case H; clear H; intros t0 H.
 case H; clear H; intros t1 H.
 case H; clear H; intros l0 H.
 case H; clear H; intros l1 H.
 destruct H. destruct H0. 
 rewrite H. rewrite H0. rewrite H in Tlu. 
 clear H H0. induction l0; simpl. destruct l1; simpl. 
 apply mod_eqC_app_right; trivial.
 apply mod_eqC_app_right; trivial. 
 simpl in Tlu. rewrite term_distribute_over_application.
 rewrite term_mult_app. destruct Tlu. destruct H0.
 split; trivial. split; trivial.
 simpl in Tlu. destruct Tlu. 
 apply mod_eqC_app_left; trivial.
 apply IHl0; trivial. 
Qed.

(**** eqC and eqC' equivalence ***)

Inductive eqC'  : pterm -> pterm -> Prop := 
  | eqC'_refl: forall u, eqC' u u  
  | eqC'_trans: forall t u v, eqC' t u -> eqC' u v -> eqC' t v 
  | eqC'_redex: forall t u v, 
    term u -> term v -> eqC' (t[u][v]) ((& t)[v][u]) 
  | eqC'_app : forall t t' u u', eqC' t t' -> eqC' u u' ->  
    eqC' (pterm_app t u) (pterm_app t' u')  
  | eqC'_abs : forall t t' L,  
   (forall x, x \notin L -> eqC' (t ^ x) (t' ^ x)) -> 
    eqC' (pterm_abs t) (pterm_abs t') 
  | eqC'_sub : forall t t' u u' L,   
   (forall x, x \notin L -> eqC' (t ^ x) (t' ^ x)) -> eqC' u u' ->  
    eqC' (t[u]) (t'[u'])
. 

 Notation "t =e' u" := (eqC' t u) (at level 66). 

 Lemma eqC'_sym : forall t u, t =e' u -> u =e' t. 
 Proof. 
  intros t u H.  
  induction H. 
  apply eqC'_refl. 
  apply eqC'_trans with (u := u); trivial. 
  replace (t[u]) with ((& (& t))[u]). apply eqC'_redex; trivial. 
  unfold bswap. rewrite bswap_rec_id. reflexivity. 
  apply eqC'_app; trivial. 
  apply eqC'_abs with (L := L); trivial. 
  apply eqC'_sub with (L := L); trivial. 
 Qed. 

 Instance eqC'_eq : Equivalence eqC'. 
 Proof.  
   split.  
   unfold Reflexive. apply eqC'_refl. 
   unfold Symmetric. apply eqC'_sym. 
   unfold Transitive. apply eqC'_trans. 
 Qed. 

Lemma term_eqC' : forall t t', t =e' t' -> (term t <-> term t').
Proof.
 intros t t' H. induction H.
 split; trivial. split. intro.
 apply IHeqC'2. apply IHeqC'1; trivial. intro.
 apply IHeqC'1. apply IHeqC'2; trivial. split.
 intro H'. apply body_to_subs; trivial.
 apply body'_to_body. apply term_to_term' in H'.
 unfold body'. unfold term' in H'. simpl in *|-*.
 split. apply lc_at_bswap. omega. apply H'.
 apply lc_at_weaken_ind with (k1 := 0); try omega.
 apply H'. intro H'. apply body_to_subs; trivial.
 apply body'_to_body. apply term_to_term' in H'.
 unfold body'. unfold term' in H'. simpl in *|-*.
 split. replace t with (& (& t)).
 apply lc_at_bswap. omega. apply H'. apply bswap_rec_id.
 apply lc_at_weaken_ind with (k1 := 0); try omega.
 apply H'. split. intro H'.
 apply term_distribute_over_application.
 apply term_distribute_over_application in H'.
 split. apply IHeqC'1; apply H'. apply IHeqC'2; apply H'.
 intro H'. apply term_distribute_over_application.
 apply term_distribute_over_application in H'.
 split. apply IHeqC'1; apply H'. apply IHeqC'2; apply H'.
 split. intro H'. apply body_to_term_abs.
 apply term_abs_to_body in H'. unfold body in *|-*.
 case H'. clear H'. intros L' H'. exists (L \u L').
 intros x H''. apply notin_union in H''. apply H0.
 apply H''. apply H'. apply H''.
 intro H'. apply body_to_term_abs.
 apply term_abs_to_body in H'. unfold body in *|-*.
 case H'. clear H'. intros L' H'. exists (L \u L').
 intros x H''. apply notin_union in H''. apply H0.
 apply H''. apply H'. apply H''. split. intro H'.
 generalize H'. intro H''. apply term_sub_to_body in H'.
 apply term_sub_to_term in H''. apply body_to_subs.
 unfold body in *|-*. case H'. clear H'. intros L' H'.
 exists (L \u L'). intros x H'''. apply notin_union in H'''.
 apply H0. apply H'''. apply H'. apply H'''. apply IHeqC'; trivial.
 intro H'. generalize H'. intro H''. apply term_sub_to_body in H'.
 apply term_sub_to_term in H''. apply body_to_subs.
 unfold body in *|-*. case H'. clear H'. intros L' H'.
 exists (L \u L'). intros x H'''. apply notin_union in H'''.
 apply H0. apply H'''. apply H'. apply H'''. apply IHeqC'; trivial.
Qed.

Instance rw_eqC'_term : Proper (eqC' ==> iff) term.
Proof.
 intros_all. apply term_eqC'; assumption.
Qed.

Lemma eqC_eq_eqC': forall t t', term t -> (t =e t' <-> t =e' t').
Proof. 
 intros t t' T. split.
 assert (Q : forall u v, term u -> p_contextual_closure eqc u v -> u =e' v).
   clear T t t'. intros t t' T H. induction H. destruct H.
   reflexivity. rewrite eqC'_redex; trivial. reflexivity.
   apply term_distribute_over_application in T. destruct T.
   apply eqC'_app. 
   apply IHp_contextual_closure1; trivial.
   apply IHp_contextual_closure2; trivial.
   apply eqC'_abs with (L := L). intros. apply H0; trivial.
   apply body_open_term; trivial. apply term_abs_to_body; trivial.
   apply subs_to_body in T; destruct T.
   apply eqC'_sub with (L := L). intros. apply H0; trivial.
   apply body_open_term; trivial. apply IHp_contextual_closure; trivial.
 intro H. induction H. apply Q; trivial.
 apply eqC'_trans with (u := u). apply Q; trivial. 
 apply IHtrans_closure. apply (lc_at_pctx_eqc 0) in H.
 rewrite term_eq_term'. apply H. rewrite <- term_eq_term'; trivial.
 intro H. induction H. reflexivity. 
 apply transitive_closure_composition with (u := u).
 apply IHeqC'1; trivial. apply IHeqC'2. rewrite <- H; trivial.
 rewrite eqC_redex; trivial. reflexivity.
 apply term_distribute_over_application in T. destruct T.
 rewrite IHeqC'1; trivial. rewrite IHeqC'2; trivial. reflexivity.
 apply eqC_abs_in with (L := L). apply term_abs_to_body; trivial.
 intros x H1. apply H0; trivial. apply body_open_term; trivial. 
 apply term_abs_to_body; trivial. apply subs_to_body in T; destruct T.
 rewrite IHeqC'; trivial. apply eqC_subst_left with (L := L); trivial. 
 rewrite <- H1; trivial. intros x H4. apply H0; trivial.
 apply body_open_term; trivial.
Qed.


(* ********************************************************************** *)
(** =e' Rewriting *)

Lemma eqC'_fv : forall x t t', 
     (eqC' t t') -> ((x \in fv t) <-> (x \in fv t')).
Proof.
 intros x t t' H. induction H.
 split; trivial.
 split. 
 intro H'. apply IHeqC'2. apply IHeqC'1; trivial.
 intro H'. apply IHeqC'1. apply IHeqC'2; trivial.
 simpl. split.
 intro H2. apply in_union in H2. case H2; clear H2. 
 intro H2. apply in_union in H2. case H2; clear H2. 
 intro H2. apply in_union. left. apply in_union. 
 left. unfold bswap. rewrite fv_bswap_rec; trivial.
 intro H2. apply in_union. right; trivial.
 intro H2. apply in_union. left. apply in_union. right; trivial.
 intro H2. apply in_union in H2. case H2; clear H2.
 intro H2. apply in_union in H2. case H2; clear H2.
 intro H2. apply in_union. left. apply in_union. 
 left. unfold bswap in H2. rewrite fv_bswap_rec in H2; trivial.
 intro H2. apply in_union. right; trivial.
 intro H2. apply in_union. left; apply in_union. right; trivial.
 simpl. split. 
 intro H1. apply in_union in H1. case H1; clear H1.
 intro H1. apply in_union. left. apply IHeqC'1; trivial.
 intro H1. apply in_union. right; trivial. apply IHeqC'2; trivial.
 intro H1. apply in_union in H1. case H1; clear H1.
 intro H1. apply in_union. left. apply IHeqC'1; trivial.
 intro H1. apply in_union. right; trivial. apply IHeqC'2; trivial.
 simpl. pick_fresh z. apply notin_union in Fr. case Fr; clear Fr.
 intros H1 H2. apply notin_union in H1. case H1; clear H1. intros H1 H3.
 apply notin_union in H1. case H1; clear H1. intros H1 H4. 
 apply notin_singleton in H4. 
 assert (Q: (x \in fv (t ^ z) <-> x \in fv t)).
   unfold open. apply fv_open_. intro.
   apply H4. apply symmetry; trivial.
 assert (Q': (x \in fv (t' ^ z) <-> x \in fv t')).
   unfold open. apply fv_open_. intro.
   apply H4. apply symmetry; trivial.
 split. 
 intro H5. apply Q'. apply H0; trivial. apply Q; trivial.
 intro H5. apply Q. apply H0; trivial. apply Q'; trivial.
 simpl. pick_fresh z. apply notin_union in Fr. case Fr; clear Fr.
 intros H2 H3. apply notin_union in H2. case H2; clear H2. intros H2 H4.
 apply notin_union in H2. case H2; clear H2. intros H2 H5. 
 apply notin_union in H2. case H2; clear H2. intros H2 H6.
 apply notin_union in H2. case H2; clear H2. intros H2 H7.
 apply notin_singleton in H7. 
 assert (Q: (x \in fv (t ^ z) <-> x \in fv t)).
   unfold open. apply fv_open_. intro.
   apply H7. apply symmetry; trivial.
 assert (Q': (x \in fv (t' ^ z) <-> x \in fv t')).
   unfold open. apply fv_open_. intro.
   apply H7. apply symmetry; trivial.
 split.
 intro H8. apply in_union in H8. case H8; clear H8.
 intro H8. apply in_union. left. 
 apply Q'. apply H0; trivial. apply Q; trivial. 
 intro H8. apply in_union. right; trivial. apply IHeqC'; trivial.
 intro H8. apply in_union in H8. case H8; clear H8.
 intro H8. apply in_union. left. 
 apply Q. apply H0; trivial. apply Q'; trivial. 
 intro H8. apply in_union. right; trivial. apply IHeqC'; trivial.
Qed.

Instance rw_eqC'_fv : Proper (eqC' ==> VarSet.Equal) fv.
Proof.
 intros_all. apply eqC'_fv; trivial.
Qed.

Definition Cofinite_q (L : VarSet.t) (R : pterm -> pterm -> Prop) (t t' : pterm)  :=
 forall x, x \notin L -> R (t ^ x) (t' ^ x) .

Definition term_R (R : pterm -> pterm -> Prop) (t t' : pterm) :=
  term t /\ R t t'.

Instance rw_eqC'_app : Proper (eqC' ++> eqC' ++> eqC') pterm_app.
Proof. 
 intros_all.
 apply eqC'_app; trivial.
Qed.

Lemma eq_app_l: forall t t' u, t =e t' -> pterm_app t u =e pterm_app t' u.
Proof.
  intros t t' u eq.
  rewrite eq.
  reflexivity.
Qed.

Lemma eq_app_r: forall t u u', u =e u' -> pterm_app t u =e pterm_app t u'.
Proof.
  intros t t' u eq.
  rewrite eq.
  reflexivity.
Qed.

Instance rw_eqC'_abs : forall L, Proper (Cofinite_q L eqC' ++> eqC') pterm_abs.
Proof. 
 intros_all. unfold Cofinite_q in H.
 apply eqC'_abs with (L := L); trivial.
Qed.

Instance rw_eqC'_sub : forall L, Proper (Cofinite_q L eqC' ++> eqC' ++> eqC') pterm_sub.
Proof.
 intros_all. unfold Cofinite_q in H.
 apply eqC'_sub with (L := L); trivial.
Qed.

Lemma eqC'_open : forall n t t' u, term u ->
t =e' t'-> (open_rec n u t) =e' (open_rec n u t').
Proof.
 intros n t t' u H. 
 intro H'. generalize n; clear n.
 induction H'. reflexivity.
 intro n. rewrite IHH'1; trivial. 
 intro n. unfold open. simpl.
 rewrite open_lc_at with (t := u0).
 rewrite open_lc_at with (t := u0).
 rewrite open_lc_at with (t := v).
 rewrite open_lc_at with (t := v).
 replace ({S (S n) ~> u}(& t)) with (& ({S (S n) ~> u}t)). 
 apply eqC'_redex; trivial.
 apply bswap_open_rec. omega.
 apply term_to_term'; trivial.
 apply lc_at_weaken_ind with (k1 := 0); 
 try omega. apply term_to_term'; trivial.
 apply lc_at_weaken_ind with (k1 := 0); 
 try omega. apply term_to_term'; trivial.
 apply lc_at_weaken_ind with (k1 := 0); 
 try omega. apply term_to_term'; trivial.
 apply lc_at_weaken_ind with (k1 := 0); 
 try omega. apply term_to_term'; trivial.
 simpl; intro n. rewrite IHH'1; rewrite IHH'2.
 reflexivity.
 simpl; intro n. apply eqC'_abs with (L := (fv u) \u L).
 intros x H2. apply notin_union in H2. case H2; clear H2.
 intros H2 H3. unfold open in *|-*. 
 replace ({0 ~> pterm_fvar x}({S n ~> u}t))
 with ({S n ~> u}({0 ~> pterm_fvar x}t)).
 replace ({0 ~> pterm_fvar x}({S n ~> u}t'))
 with ({S n ~> u}({0 ~> pterm_fvar x}t')).
 apply H1; trivial.
 rewrite subst_com; trivial. omega.
 rewrite subst_com; trivial. omega.
 simpl; intro n. apply eqC'_sub with (L := (fv u) \u L).
 intros x H2. apply notin_union in H2. case H2; clear H2.
 intros H2 H3. unfold open in *|-*. 
 replace ({0 ~> pterm_fvar x}({S n ~> u}t))
 with ({S n ~> u}({0 ~> pterm_fvar x}t)).
 replace ({0 ~> pterm_fvar x}({S n ~> u}t'))
 with ({S n ~> u}({0 ~> pterm_fvar x}t')).
 apply H1; trivial.
 rewrite subst_com; trivial. omega.
 rewrite subst_com; trivial. omega.
 apply IHH'.
Qed.

Instance rw_eqC'_abs' : Proper (eqC' ++> eqC') pterm_abs.
Proof.
 intros_all. apply eqC'_abs with (L := {}).
 intros x' H'. apply eqC'_open; trivial.
Qed.

Instance rw_eqC'_sub' : Proper (eqC' ++> eqC' ++> eqC') pterm_sub.
Proof.
 intros_all. apply eqC'_sub with (L := {}); trivial.
 intros x' H'. apply eqC'_open; trivial. 
Qed.

Lemma eq_abs: forall t t', t =e' t' -> pterm_abs t =e' pterm_abs t'.
Proof.
  intros t t' eq.
  rewrite eq.
  reflexivity.
Qed.

Lemma eq_subs: forall t t' u, t =e' t' -> pterm_sub t u =e' pterm_sub t' u.
Proof.
  intros t t' u eq.
  rewrite eq.
  reflexivity.
Qed.



