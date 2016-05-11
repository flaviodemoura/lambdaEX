(*******************************************************************************************
* Formalization of lambda						                   *	
*									                   *
* Brian Aydemir & Arthur Chargu\u00e9raud, July 2007                             	   *
* Fl\u00e1vio L. C. de Moura & Daniel L. Ventura, 2012                                     *
* Fl\u00e1vio L. C. de Moura & Daniel L. Ventura & Washington R. Segundo, 2013       *
********************************************************************************************)

Set Implicit Arguments.
Require Import Metatheory LambdaES_Defs.
Require Import Rewriting LambdaES_Infra LambdaES_FV.
Require Import Arith List.

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
(** Properties of the  beta reduction **)

Lemma Lterm_is_term: forall t, Lterm t -> term t.
Proof.
 intros. induction H; trivial.
 apply term_distribute_over_application; split; trivial.
 apply body_to_term_abs; trivial. unfold body.
 exists L; trivial.
Qed.

Lemma Lbody_is_body: forall t, Lbody t -> body t.
Proof.
 intros. unfold body. unfold Lbody in H.
 case H; clear H; intros L H. exists L.
 intros x H'. apply Lterm_is_term.
 apply H; trivial.
Qed.

Lemma subst_Lterm : forall t z u,
  Lterm u -> Lterm t -> Lterm ([z ~> u]t).
Proof.
  induction 2; simpls*.
  case_var*. apply_fresh Lterm_abs. rewrite* subst_open_var. apply Lterm_is_term; trivial.
Qed.
Hint Resolve subst_Lterm.

Lemma Lbody_open_term : forall t u, Lbody t -> Lterm u -> Lterm (t ^^ u).
Proof.
 intros. destruct H. case var_fresh with (L := x \u (fv t)).
 intros y Fr. rewrite* (@subst_intro y).
Qed.

Lemma not_Lbody_Sn: forall n, ~(Lbody (pterm_bvar (S n))).
Proof.
  intro n.
  intro H. 
  elim H.
  intro L.
  intro H1.
  pick_fresh z.
  assert (z \notin L). auto.
  assert (Lterm (pterm_bvar (S n) ^ z)).
  apply H1.
  assumption.
  inversion H2.
Qed.

(* ********************************************************************** *)
(** Properties of reduction *)
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

Lemma L_red_out_to_rename : forall (R : pterm -> pterm -> Prop),
  L_red_out R -> red_rename R. 
Proof.
  intros_all.
  rewrite* (@subst_intro x t). 
  rewrite* (@subst_intro x t').
Qed.


Lemma beta_rename : red_rename rule_beta.
Proof.
 apply L_red_out_to_rename.
 apply L_beta_red_out.
Qed.

Lemma red_regular_Lctx : forall (R : pterm -> pterm -> Prop),
  L_red_regular R -> L_red_regular (L_contextual_closure R).
Proof. (*aqui*)
  intros_all. induction H0.
  apply H; trivial. 
  case IHL_contextual_closure.
  intros H2 H3.
  split; apply Lterm_app; trivial. split; apply Lterm_app; trivial.
  apply IHL_contextual_closure. apply IHL_contextual_closure.
  split; apply Lterm_abs with (L := L); apply H1; trivial.
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


Lemma Lbody_distribute_over_application : forall t u, Lbody (pterm_app t u) <-> Lbody t /\ Lbody u.
Proof.
  split.
    (* -> *)
    unfold body; unfold open; simpl ; intros; elim H; intros. 
    split ; exists x; intros; specialize (H0 x0); specialize (H0 H1) ;
    inversion H0 ; assumption.
    (* <- *)
    intros. unfold body in H. unfold body. destruct H.
    destruct H. destruct H0.
    exists (x \u x0). intros.
    unfold open.  simpl. constructor.
      specialize (H x1) . auto. 
      specialize (H0 x1) . auto.
Qed.


(** Reduction on lists **)

Lemma Lterm_mult_app : forall t lu, Lterm (t // lu) <-> Lterm t /\ (Lterm %% lu).
Proof.
 intros t lu. induction lu; simpl; split; 
 intro H;  try apply H; try split; trivial.
 inversion H. apply IHlu; trivial.
 inversion H. split; trivial. apply IHlu; trivial.
 destruct H. destruct H0. apply Lterm_app; trivial.
 apply IHlu; split; trivial.
Qed.

(* ********************************************************************** *)
(** Local closure for Lambda terms, recursively defined *)

Fixpoint Llc_at (k:nat) (t:pterm) {struct t} : Prop :=
  match t with 
  | pterm_bvar i    => i < k
  | pterm_fvar x    => True
  | pterm_app t1 t2 => Llc_at k t1 /\ Llc_at k t2
  | pterm_abs t1    => Llc_at (S k) t1
  | pterm_sub t1 t2 => False
  | pterm_lsub t1 t2 => False
  end.

Definition Lterm' t := Llc_at 0 t.

Definition Lbody' t := Llc_at 1 t.

(* ********************************************************************** *)
(** Equivalence of [Lterm and [Lterm'] *)

Lemma Llc_rec_open_var_rec : forall x t k,
  Llc_at k (open_rec k x t) -> Llc_at (S k) t.
Proof.
  induction t; simpl; introv H; auto*.
  case_nat; simpls~.
Qed.

Lemma Lterm_to_Lterm' : forall t,
  Lterm t -> Lterm' t.
Proof.
  introv T. induction T; unfold Lterm'; simple~.
  pick_fresh x. apply~ (@Llc_rec_open_var_rec (pterm_fvar x)). apply~ H0.
Qed.

Lemma Llc_at_open_var_rec : forall x t k,
  Llc_at (S k) t -> Llc_at k (open_rec k (pterm_fvar x) t).
Proof.
  induction t; simpl; introv H; auto*.
  case_nat; simpls~.
  unfold lt in *|-.
  apply le_lt_or_eq in H.
  case H.
  intro H1. apply lt_S_n in H1; trivial.
  intro H1. assert (n = k).
  auto. assert (k = n). auto.
  contradiction.
Qed. 

Lemma Lterm'_to_Lterm : forall t,
  Lterm' t -> Lterm t.
Proof.
  introv. unfold Lterm'.
  apply pterm_size_induction with (t := t).
  (* bvar *)
  simpl. intros. 
  assert (~ n < 0). auto with arith.
  contradiction.
  (* fvar *)
  simpl. intros.
  apply Lterm_var. 
  (* abs *)
  simpl. intros.
  apply Lterm_abs with (L := fv t1).
  intros x Fr.
  apply (H t1); trivial.
  unfold open. 
  apply Llc_at_open_var_rec; trivial.
  (* app *)
  intros t1 t2 IHt1 IHt2 H.
  simpl in H. apply Lterm_app.
  apply IHt1; apply H.
  apply IHt2; apply H.
  (* sub *)
  intros. simpl in H1. contradiction.
  (* sub' *)
  intros. simpl in H1. contradiction.
Qed.


Lemma Lterm_eq_Lterm' : forall t, Lterm t <-> Lterm' t.
Proof. intros. split. apply Lterm_to_Lterm'. apply Lterm'_to_Lterm. Qed.


(* ********************************************************************** *)
(** Equivalence of [Lbody] and [Lbody'] *)

Lemma Lbody_to_Lbody' : forall t,
  Lbody t -> Lbody' t.
Proof.
  introv [L H]. pick_fresh x. 
  applys (@Llc_rec_open_var_rec (pterm_fvar x)).
  apply Lterm_to_Lterm'. apply~ H.
Qed.

Lemma Lbody'_to_Lbody : forall t,
  Lbody' t -> Lbody t.
Proof.
  introv B. exists ({}:vars). introv F.
  apply Lterm'_to_Lterm. apply~ Llc_at_open_var_rec.
Qed.

Lemma Lbody_eq_Lbody' : forall t, Lbody t <-> Lbody' t.
Proof. intros. split. apply Lbody_to_Lbody'. apply Lbody'_to_Lbody. Qed.

(* ********************************************************************** *)
(** Weakening property of [Llc_at] *)

Lemma Llc_at_weaken_ind : forall k1 k2 t,
  Llc_at k1 t -> k1 <= k2 -> Llc_at k2 t.
Proof. introv. gen k1 k2. induction t; simpl; introv T Lt; auto*.
       omega. apply (IHt (S k1) (S k2)); trivial; try omega.
Qed. 

Lemma Llc_at_weaken : forall k t,
  Lterm' t -> Llc_at k t.
Proof. introv H. apply~ (@Llc_at_weaken_ind 0). omega. Qed.


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

(** Induction Principles *)

Lemma Lbody_size_induction :
 forall P : pterm -> Prop,
 (P (pterm_bvar 0)) ->
 (forall x, P (pterm_fvar x)) ->
 (forall t1, (Llc_at 2 t1) ->
    (forall t2 x, x \notin fv t2 -> pterm_size t2 = pterm_size t1 ->
    Lbody (open_rec 1 (pterm_fvar x) t2) -> P (open_rec 1 (pterm_fvar x) t2)) -> P (pterm_abs t1)) ->
 (forall t1 t2, Lbody t1 -> Lbody t2 -> P t1 -> P t2 -> P (pterm_app t1 t2)) ->
 (forall t, Lbody t -> P t).
Proof.
  intros P Ha Hb Hc Hd t.
  gen_eq n: (pterm_size t). gen t.
  induction n using peano_induction.
  introv Eq B. subst. destruct t. 
     (* bvar *)
     generalize B; clear B; case n.
     intro B; apply Ha.
     intros n' H'; apply not_Lbody_Sn in H'; contradiction.
     (* fvar *)
     apply Hb.
     (* app *)
     apply~ Hd; 
     apply Lbody_distribute_over_application in B.
     apply B. apply B.
     apply~ H. simpl; omega. 
     apply B. apply~ H. simpl; omega.
     apply B.
     (* abs *)
     apply* Hc.
     apply Lbody_to_Lbody' in B.
     unfold Lbody' in B. simpl in B; trivial.
     introv Fr Eq.
     apply~ H. rewrite <- pterm_size_open_var. simpl. omega.
     (* sub *)
     apply Lbody_to_Lbody' in B. unfold Lbody' in B. simpl in B.
     contradiction.
     (* sub' *)
     apply Lbody_to_Lbody' in B. unfold Lbody' in B. simpl in B.
     contradiction.
Qed.

Lemma Lterm_size_induction :
 forall P : pterm -> Prop,
 (forall x, P (pterm_fvar x)) ->
 (forall t1 t2,
    Lterm t1 -> P t1 -> Lterm t2 -> P t2 -> P (pterm_app t1 t2)) ->
 (forall t1,
    Lbody t1 ->
    (forall t2 x, x \notin fv t2 -> pterm_size t2 = pterm_size t1 ->
      Lterm (t2 ^ x) -> P (t2 ^ x)) ->
    P (pterm_abs t1)) ->
 (forall t, Lterm t -> P t).
Proof.
  intros P Ha Hb Hc t.
  gen_eq n: (pterm_size t). gen t.
  induction n using peano_induction.
  introv Eq T. subst. inverts T. 
     apply Ha.
     (* app *)
     apply~ Hb. apply~ H. simpl; omega. apply~ H. simpl; omega.
     (* abs *)
     apply* Hc.
       introv. exists L. trivial.
       introv Fr Eq T.
       apply~ H. unfold open.
      rewrite <- pterm_size_open_var. simpl. omega.
 Qed.

Lemma Lterm_size_induction2 :
 forall P : pterm -> Prop,
 (forall x l, (forall u, In u l -> (Lterm u /\ P u)) -> P ((pterm_fvar x) // l)) ->
 (forall t1 l, (forall u, In u l -> (Lterm u /\ P u)) -> Lbody t1 ->
  (forall t2 x, x \notin fv t2 -> pterm_size t2 = pterm_size t1 -> Lterm (t2 ^ x) -> P (t2 ^ x)) ->
      P ((pterm_abs t1) // l)) ->
 (forall l t, (forall u, In u l -> (Lterm u /\ P u)) -> Lterm t -> P (t // l)).
Proof.
 intros. generalize H2.  intro T. generalize l H1 H2. clear l H1 H2.
 apply Lterm_size_induction with (t := t); trivial; intros.
 apply H; trivial.
 replace (pterm_app t1 t2 // l) with (t1 // l ++ (t2 :: nil)).  
 apply H2. intros. apply in_app_iff in H7. destruct H7.
 apply H5; trivial. simpl in H7. destruct H7; try contradiction.
 rewrite <- H7. clear H7. inversion H6. split; trivial.
 assert (Q : P (t2 // nil)). 
   apply H4; simpl; trivial; intros. contradiction. 
 simpl in Q. trivial. trivial. 
 rewrite mult_app_append. trivial.
 apply H0; trivial. intros.
 assert (Q : P (t2 ^ x // nil)).
   apply H2; simpl; trivial; intros. contradiction.
 simpl in Q. trivial.
Qed.


Lemma Lterm_size_induction3 :
 forall P : pterm -> Prop,
 (forall x l, (forall u, In u l -> (Lterm u /\ P u)) -> P ((pterm_fvar x) // l)) ->
 (forall t1 l, (forall u, In u l -> (Lterm u /\ P u)) -> Lbody t1 ->
  (forall t2 x, x \notin fv t2 -> pterm_size t2 = pterm_size t1 -> Lterm (t2 ^ x) -> P (t2 ^ x)) ->
      P ((pterm_abs t1) // l)) ->
 (forall t, Lterm t -> P t).
Proof. 
 intros. replace t with (t // nil).
 apply Lterm_size_induction2; simpl; trivial.
 intros; contradiction. 
 simpl. trivial.
Qed.


Lemma Llc_at_bswap : forall n k t, S k < n -> Llc_at n t -> Llc_at n (bswap_rec k t).
Proof.
 intros n k t. 
 generalize n k; clear n k.
 induction t.
 (* bvar *)
 intros n' k H0 H1. simpl in H1.
 unfolds bswap_rec. 
 case (k === n). intro H2.
 rewrite H2. simpl. omega. intro H2.
 case (S k === n). intro H3. simpl. omega. intro H3. 
 simpl. trivial.
 (* fvar *)
 intros n k H0 H1. simpl in *|-*. trivial.
 (* app *)
 intros n k H0 H1. simpl in *|-*. destruct H1. split.
 apply IHt1; trivial. apply IHt2; trivial.
 (* abs *)
 intros n k H0 H1. simpl in *|-*.
 apply IHt; try omega; trivial.
 (* sub *)
 intros n k H0 H1. simpl in *|-*. contradiction. 
 (* sub' *)
 intros n k H0 H1. simpl in *|-*. contradiction. 
Qed.

Lemma Llc_at_open : forall n t u, Lterm u -> (Llc_at (S n) t <-> Llc_at n (open_rec n u t)).
Proof.
 intros n t u T. split.
(* -> *)
 generalize n; clear n.
 induction t.
 (* bvar *)
 intros n' H0. unfolds open_rec.
 case (n' === n). intro H1.
 rewrite H1 in H0. rewrite H1. simpl in *|-*. 
 apply Lterm_to_Lterm' in T. unfold Lterm' in T.
 apply Llc_at_weaken_ind with (k1 := 0); try omega; trivial.
 intro H1. simpl in *|-*. omega.
 (* fvar *)
 intros n H. simpl. trivial.
 (* app *)
 intros n H. simpl in *|-*.
 case H; clear H; intros Ht1 Ht2; split.
 apply (IHt1 n Ht1). 
 apply (IHt2 n Ht2).
 (* abs *)
 intros n H. simpl in *|-*.
 apply (IHt (S n) H).
 (* sub *)
 intros n H. simpl in *|-*. contradiction.
 (* sub' *)
 intros n H. simpl in *|-*. contradiction.
(* <- *)
 generalize n; clear n.
 induction t.
 (* bvar *)
 intros n' H0. simpl in H0.
 case (n' === n) in H0. simpl. omega.
 simpl in *|-*. omega.
 (* fvar *)
 simpl. trivial. 
 (* app *)
 simpl in *|-*. intros n H.
 case H; clear H; intros Ht1 Ht2; split.
 apply (IHt1 n Ht1). 
 apply (IHt2 n Ht2).
 (* abs *)
 simpl in *|-*. intros n H. 
 apply (IHt (S n) H).
 (* sub *)
 simpl in *|-*. intros n H. contradiction. 
 (* sub' *)
 simpl in *|-*. intros n H. contradiction.
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

