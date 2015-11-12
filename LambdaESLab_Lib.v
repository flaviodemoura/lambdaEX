(********************************************************************************
* Formalization of lambda ex_lab         				        *		
*									        *
* Flavio L. C. de Moura & Daniel L. Ventura, & Washington R. Segundo, 2014	*
*********************************************************************************)

Set Implicit Arguments.
Require Import Metatheory LambdaES_Defs LambdaES_Infra LambdaES_FV.
Require Import Rewriting_Defs Rewriting_Lib.
Require Import Equation_C Lambda Lambda_Ex LambdaESLab_Defs.
Require Import Basic_Prop_lex.

(* [=] equivalence *)
(*
Lemma Equal_eq : Equivalence VarSet.Equal.
Proof.
 split; intros_all.
 split; intros; trivial.
 split; intros; apply H; trivial.
 split; intros. apply H0. apply H; trivial.
 apply H. apply H0. trivial.
Qed.

Lemma rw_in : forall x, Proper (VarSet.Equal ==> iff) (VarSet.In x).
Proof.
 intros_all; apply H.
Qed.

Lemma rw_union : Proper (VarSet.Equal ++> VarSet.Equal ++> VarSet.Equal) VarSet.union.
Proof.
 intros_all; split; intros.
 apply in_union in H1; apply in_union. destruct H1.
 left. apply H; trivial. right; apply H0; trivial.
 apply in_union in H1; apply in_union. destruct H1.
 left. apply H; trivial. right; apply H0; trivial.
Qed.  

Lemma rw_subset : Proper (VarSet.Equal ==> VarSet.Equal ==> iff) VarSet.Subset.
Proof.
 intros_all. split; unfold VarSet.Subset; intros.
 apply H0. apply H1. apply H; trivial.
 apply H0. apply H1. apply H; trivial.
Qed. 
*)

(** Properties of labelled terms. *)

(*
Lemma lab_term_subset : forall (S S' : VarSet.t) (t : pterm),
                        S << S' -> lab_term S t -> lab_term S' t. 
Proof.
 intros S S' t H0 H1. generalize S' H0; clear S' H0. 
 induction H1; intros. apply lab_term_var.
 intros. apply lab_term_app; 
 [apply IHlab_term1; trivial | apply IHlab_term2; trivial]. 
 apply lab_term_abs with (L := L); intros. apply H0; trivial.
 intros y Hy. apply in_union in Hy. apply in_union.
 destruct Hy. left; apply H1; trivial. right; trivial.
 apply lab_term_sub with (L := L); 
 intros; [apply H0; trivial | apply IHlab_term]; trivial.
 intros y Hy. apply in_union in Hy. apply in_union.
 destruct Hy. left; apply H2; trivial. right; trivial.
 apply lab_term_sub' with (L := L); trivial. intros.
 apply H0; trivial. intros y Hy. apply in_union in Hy. apply in_union.
 destruct Hy. left; apply H4; trivial. right; trivial.
 apply subset_trans with (F := S); trivial.
Qed.


Lemma lab_body_subset : forall (S S' : VarSet.t) (t : pterm),
                        S << S' -> lab_body S t -> lab_body S' t. 
Proof.
 intros S S' t H0 H1. unfold lab_body in *|-*. case H1; clear H1; intros L H1.
 exists L. intros y Hy. apply lab_term_subset with (S := S \u {{y}}).
 apply subset_union_trans_l with (F := S); trivial. apply H1; trivial.
Qed.
 *)

(*
Lemma term_to_lab_term : forall S t, term t -> lab_term S t.
Proof.
 intros. induction H.
 apply lab_term_var. 
 apply lab_term_app; trivial.
 apply lab_term_abs with (L := L); intros.
 apply lab_term_subset with (S := S).
 apply subset_union_weak_l. apply H0; trivial.
 apply lab_term_sub with (L := L); trivial; intros.
 apply lab_term_subset with (S := S).
 apply subset_union_weak_l. apply H0; trivial.
Qed.
 *)


(** Every term is also a labelled term because the grammar with labels
extends the term grammar. *)

Lemma term_is_lab_term: forall t, term t -> lab_term t.
Proof.
  intros t Ht.
  apply term_size_induction.
  intro x. apply lab_term_var.
  intros t1 Hbody Hind.
  apply lab_term_abs with (L := fv t1).
  intros x Hfv.
  apply Hind. assumption. trivial.
  apply body_to_term; assumption.
  intros t1 t2 Ht1 Hlab1 Ht2 Hlab2.
  apply lab_term_app; assumption.
  intros t1 t3 Ht3 Hlab3 Hb1 Hind.
  apply lab_term_sub with (L := fv t1).
  intros x Hfvt1.
  apply Hind. assumption. trivial.
  apply body_to_term; assumption. assumption. assumption.
Qed.

Lemma lab_body_to_body : forall t, body t -> lab_body t.
Proof.
 intros. case H; clear H; intros L H; exists L.
 intros. apply term_is_lab_term. apply H; trivial.
Qed.

Lemma open_lab_term : forall t x k, lab_term t -> ({k ~> pterm_fvar x}t) = t.
Proof.
 intros t x k H. generalize k; clear k. 
 induction H; intros; simpl; trivial.
 rewrite IHlab_term1; rewrite IHlab_term2; trivial.
 case var_fresh with (L := L \u (fv t1) \u fv ({Datatypes.S k ~> pterm_fvar x}t1)). intros z Hz. 
 apply notin_union in Hz. destruct Hz. apply notin_union in H1. destruct H1.
 assert (Q : {Datatypes.S k ~> pterm_fvar x}t1 ^ z = t1 ^ z). apply H0; trivial. 
 unfold open in Q. rewrite subst_com in Q; try omega; trivial.
 apply open_var_inj in Q; trivial. rewrite Q; trivial.
 rewrite IHlab_term.
 case var_fresh with (L := L \u (fv t1) \u fv ({Datatypes.S k ~> pterm_fvar x}t1)). intros z Hz.
 apply notin_union in Hz. destruct Hz. apply notin_union in H2. destruct H2.
 assert (Q : {Datatypes.S k ~> pterm_fvar x}t1 ^ z = t1 ^ z). apply H0; trivial.
 unfold open in Q. rewrite subst_com in Q; try omega; trivial.
 apply open_var_inj in Q; trivial. rewrite Q; trivial.
 rewrite <- open_rec_term with (t := t2); trivial.
 case var_fresh with (L := L \u (fv t1) \u fv ({Datatypes.S k ~> pterm_fvar x}t1)). intros z Hz.
 apply notin_union in Hz. destruct Hz. apply notin_union in H3. destruct H3. 
 assert (Q : {Datatypes.S k ~> pterm_fvar x}t1 ^ z = t1 ^ z).
 apply H0; trivial.
 unfold open in Q. rewrite subst_com in Q; try omega; trivial.
 apply open_var_inj in Q; trivial.
 rewrite Q; trivial. 
Qed.

(** Parei aqui (Flávio) *)

(* Lemma swap_lab_term : forall x y S t, x \in S -> y \in S -> *)
(*                       lab_term S t -> lab_term S ([(x,y)]t). *)
(* Proof. *)
(*  intros x y S t Hx Hy H. induction H; simpl. *)
(*  case (x0 == x); case (x0 == y); intros; apply lab_term_var. *)
(*  apply lab_term_app; [apply IHlab_term1; trivial | apply IHlab_term2; trivial]. *)
(*  apply lab_term_abs with (L := L \u {{x}} \u {{y}}). intros z Hz.  *)
(*  apply notin_union in Hz. destruct Hz. apply notin_union in H1. destruct H1. *)
(*  apply notin_singleton in H2. apply notin_singleton in H3.  *)
(*  rewrite open_swap; trivial. apply H0; trivial; apply in_union; left; trivial. *)
(*  apply lab_term_sub with (L := L \u {{x}} \u {{y}});  *)
(*  try apply  IHlab_term; trivial; intros z Hz.  *)
(*  apply notin_union in Hz. destruct Hz. apply notin_union in H2. destruct H2. *)
(*  apply notin_singleton in H3. apply notin_singleton in H4.  *)
(*  rewrite open_swap; trivial. apply H0; trivial; apply in_union; left; trivial. *)
(*  apply lab_term_sub' with (L := L \u {{x}} \u {{y}}); trivial. intros z Hz.  *)
(*  apply notin_union in Hz. destruct Hz. apply notin_union in H4. destruct H4. *)
(*  apply notin_singleton in H5. apply notin_singleton in H6.  *)
(*  rewrite open_swap; trivial. apply H0; trivial; apply in_union; left; trivial. *)
(*  apply swap_term; trivial. apply lex_SN_swap; trivial. *)
(*  apply swap_fvar; trivial. *)
(* Qed. *)

(* Lemma swap_lab_term' : forall x y S t, x \in S -> y \in S -> *)
(*                                        x \notin fv t -> y \notin fv t -> *)
(*                                        lab_term S (t ^ x) -> lab_term S (t ^ y). *)
(* Proof. *)
(*  intros. replace (t^y) with ([(x,y)](t^x)). apply swap_lab_term; trivial. *)
(*  unfold open. rewrite open_swap_comm. rewrite swap_var_l. *)
(*  rewrite swap_fresh; trivial. *)
(* Qed. *)

(* Lemma swap_lab_body : forall x y S t, x \in S -> y \in S -> *)
(*                       lab_body S t -> lab_body S ([(x,y)]t). *)
(* Proof. *)
(*  intros. unfold lab_body in *|-*. case H1; clear H1; intros L H1. *)
(*  exists (L \u {{x}} \u {{y}}). intros z Hz. *)
(*  apply notin_union in Hz. destruct Hz. apply notin_union in H2. destruct H2. *)
(*  apply notin_singleton in H3. apply notin_singleton in H4. rewrite open_swap; trivial. *)
(*  apply swap_lab_term. apply in_union. left; trivial. apply in_union. left; trivial. *)
(*  apply H1; trivial. *)
(* Qed. *)

(* Lemma bswap_rec_open : forall x k t, bswap_rec (S k) (t ^ x) = (bswap_rec (S k) t) ^ x.  *)
(* Proof. *)
(*  intros. *)
(*  case var_fresh with (L := fv t \u {{x}}). intros y Fry. *)
(*  case var_fresh with (L := fv t \u {{x}} \u {{y}}). intros z Frz. *)
(*  apply notin_union in Fry. destruct Fry. apply notin_singleton in H0. *)
(*  apply notin_union in Frz. destruct Frz. apply notin_union in H1.  *)
(*  destruct H1. apply notin_singleton in H2. apply notin_singleton in H3. *)
(*  rewrite <- bswap_eq_openclose with (x := y) (y := z). unfold open.  *)
(*  rewrite subst_com with (i := S k) (j := 0); try omega; trivial. *)
(*  rewrite subst_com with (i := S (S k)) (j := 0) ; try omega; trivial.  *)
(*  rewrite <- openclose_com; try omega; trivial. *)
(*  rewrite <- openclose_com; try omega; trivial. *)
(*  rewrite bswap_eq_openclose with (x := y) (y := z); trivial. *)
(*  apply notin_union. split; trivial. apply notin_singleton; trivial.  *)
(*  intro; apply H0; rewrite H4; trivial. intro; apply H3; rewrite H4; trivial. *)
(*  unfold open. rewrite fv_open_; trivial. apply notin_union. *)
(*  split. unfold open. rewrite fv_open_; trivial. apply notin_singleton; trivial. *)
(* Qed. *)


(* (** Open a labeled locally closed term is the identity *) *)
(* Lemma open_rec_lab_term : forall S t u,  lab_term S t -> forall k, t = {k ~> u}t. *)
(* Proof. *)
(*   induction 1; intros; simpl; fequals*; unfolds open ; *)
(*   case var_fresh with (L := L); intros x Fr;  *)
(*   try apply* (@open_rec_term_core t1 0 (pterm_fvar x)); try omega; *)
(*   try apply H0; trivial. apply open_rec_term; trivial. *)
(* Qed.   *)

(* Lemma red_regular_lab_x : forall t t', lab_sys_x t t' -> (exists S, lab_term S t /\ lab_term S t').    *)
(* Proof. *)
(*  intros t t' H. induction H; exists S. *)
(*  inversion H. split; trivial. apply term_to_lab_term; trivial.  *)
(*  split; trivial. *)
(*  split. inversion H0. inversion H. apply lab_term_sub' with (L := L \u x); trivial.  *)
(*  intros z Fr; apply notin_union in Fr;  destruct Fr. *)
(*  unfold open. simpl. apply lab_term_app. apply H7; trivial. apply H3; trivial. *)
(*  inversion H0. inversion H. apply lab_term_app. *)
(*  apply lab_term_sub' with (L := x); trivial. apply lab_term_sub' with (L := L); trivial.  *)
(*  split; trivial.  inversion H. clear H H0 H1 t1 t2.  *)
(*  apply lab_term_abs with (L := L \u (fv t)); intros x Hx. *)
(*  apply notin_union in Hx. destruct Hx. *)
(*  assert (Q : lab_term (S \u {{x}}) (pterm_abs t ^ x)). apply H2; trivial. clear H2 H L. *)
(*  unfold open in *|-*. simpl. rewrite <- open_rec_term with (t := u); trivial. *)
(*  inversion Q. clear Q H t1. *)
(*  apply lab_term_sub' with (L := L \u (fv t)); trivial. intros y Hy. unfold open in *|-*. *)
(*  apply notin_union in Hy. destruct Hy. *)
(*  assert (Q : lab_term (S \u {{x}} \u {{y}}) ({0 ~> pterm_fvar y}({1 ~> pterm_fvar x}t))).  *)
(*    apply H1; trivial. clear H1 H L.  *)
(*  rewrite <- open_bswap; trivial. rewrite subst_com in Q; try omega; trivial. *)
(*  rewrite swap_eq_open; trivial. apply swap_lab_term; trivial. *)
(*  apply in_union. left. apply in_union. right. apply in_singleton; trivial. *)
(*  apply in_union. right. apply in_singleton; trivial. *)
(*  apply subset_trans with (F := S); trivial. *)
(*  apply subset_union_weak_l. *)
(*  split; trivial. inversion H. clear H H1 H2 t1 t2. *)
(*  apply lab_term_sub with (L := L \u (fv t)). intros x Hx. *)
(*  apply notin_union in Hx. destruct Hx. *)
(*  assert (Q : lab_term (S \u {{x}}) ((t [u]) ^ x)). apply H3; trivial. clear H3 H L. *)
(*  unfold open in *|-*. simpl in *|-*. rewrite <- open_rec_term with (t := v); trivial. *)
(*  inversion Q. clear Q H H2 t1 t2. *)
(*  apply lab_term_sub' with (L := L \u (fv t)); trivial. intros y Hy. unfold open in *|-*. *)
(*  apply notin_union in Hy. destruct Hy. *)
(*  assert (Q : lab_term (S \u {{x}} \u {{y}}) ({0 ~> pterm_fvar y}({1 ~> pterm_fvar x}t))).  *)
(*    apply H3; trivial. clear H3 H L.  *)
(*  rewrite <- open_bswap; trivial. rewrite subst_com in Q; try omega; trivial. *)
(*  rewrite swap_eq_open; trivial. apply swap_lab_term; trivial. *)
(*  apply in_union. left. apply in_union. right. apply in_singleton; trivial. *)
(*  apply in_union. right. apply in_singleton; trivial. *)
(*  apply subset_trans with (F := S); trivial. *)
(*  apply subset_union_weak_l. *)
(*  apply lab_term_sub' with (L := L); trivial; intros x Hx. *)
(*  assert (Q : lab_term (S \u {{x}}) ((t [u]) ^ x)). apply H3; trivial. clear H3. *)
(*  unfold open in Q. simpl in Q.  inversion Q; trivial. *)
(* Qed. *)

(* Lemma red_regular_lab_Bx : forall t t', lab_sys_Bx t t' -> (exists S, lab_term S t /\ lab_term S t'). *)
(* Proof. *)
(*  intros t t' H. induction H. destruct H; exists S. inversion H. *)
(*  split; [apply lab_term_app; trivial | apply lab_term_sub' with (L := x); trivial].  *)
(*  apply lab_term_abs with (L := x); trivial. apply term_to_lab_term; trivial. *)
(*  apply red_regular_lab_x; trivial. *)
(* Qed. *)

(* Lemma red_regular'_lab_eqc : forall t t', lab_eqc t t' -> (exists S, lab_term S t <-> lab_term S t'). *)
(* Proof. *)
(*  intros t t' H. induction H. exists {}. split; intros; trivial. *)
(*  exists S. split; intros. *)
(*  inversion H1. clear H1 H2 H3 t1 t2. *)
(*  apply lab_term_sub with (L := L \u (fv t)); trivial. intros x Hx. unfold open in *|-*. *)
(*  apply notin_union in Hx. destruct Hx. *)
(*  assert (Q : lab_term (S \u {{x}}) ((t [u]) ^ x)). apply H4; trivial. clear H4 H1 L. *)
(*  inversion Q. clear Q H0 H1 H3 t1 t2. simpl. rewrite <- open_rec_term with (t := v); trivial. *)
(*  apply lab_term_sub' with (L := L \u (fv t)); trivial. intros y Hy. unfold open in *|-*. *)
(*  apply notin_union in Hy. destruct Hy. *)
(*  assert (Q : lab_term (S \u {{x}} \u {{y}}) ({0 ~> pterm_fvar y}({1 ~> pterm_fvar x}t))).  *)
(*    apply H4; trivial. clear H4 H0 L.  *)
(*  rewrite <- open_bswap; trivial. rewrite subst_com in Q; try omega; trivial. *)
(*  rewrite swap_eq_open; trivial. apply swap_lab_term; trivial. *)
(*  apply in_union. left. apply in_union. right. apply in_singleton; trivial. *)
(*  apply in_union. right. apply in_singleton; trivial. *)
(*  apply subset_trans with (F := S); trivial. *)
(*  apply subset_union_weak_l.  *)
(*  inversion H1. clear H1 H2 H3 t1 t2. *)
(*  apply lab_term_sub' with (L := L \u (fv t)); trivial. intros x Hx. unfold open in *|-*. *)
(*  apply notin_union in Hx. destruct Hx. *)
(*  assert (Q : lab_term (S \u {{x}}) ((& t [[v]]) ^ x)). apply H4; trivial. clear H4 H1 L. *)
(*  unfold open in Q. simpl in Q. rewrite <- open_rec_term with (t := v) in Q; trivial. *)
(*  inversion Q. clear Q H1 H3 H5 H6 t1 t2. simpl. rewrite open_lab_term with (t := u) (S := S); trivial. *)
(*  apply lab_term_sub with (L := L \u (fv t)); trivial. intros y Hy. unfold open in *|-*. *)
(*  apply notin_union in Hy. destruct Hy. *)
(*  assert (Q : lab_term (S \u {{x}} \u {{y}}) ({0 ~> pterm_fvar y}({1 ~> pterm_fvar x}&t))).  *)
(*    apply H4; trivial. clear H4 H1 L.  *)
(*  rewrite <- open_bswap in Q; trivial. rewrite subst_com; try omega; trivial. *)
(*  rewrite swap_eq_open; trivial. apply swap_lab_term; trivial. *)
(*  apply in_union. right. apply in_singleton; trivial. *)
(*  apply in_union. left. apply in_union. right. apply in_singleton; trivial. *)
(*  apply lab_term_subset with (S := S); trivial. apply subset_union_weak_l. *)
(*  case var_fresh with (L := L). intros x Hx. *)
(*  assert (Q :  lab_term (S \u {{x}}) (({1 ~> pterm_fvar x}(& t)[[v]]))). *)
(*    unfold open in H4. simpl in H4.  *)
(*    rewrite open_rec_term with (t := v) (k := 0) (u := pterm_fvar x); trivial. *)
(*    apply H4; trivial. *)
(*  clear H4 Hx L. inversion Q; trivial. *)
(*  case var_fresh with (L := L \u fv v). intros x Hx. apply notin_union in Hx. destruct Hx. *)
(*  assert (Q :  lab_term (S \u {{x}}) (({1 ~> pterm_fvar x}(& t)[[v]]))). *)
(*    unfold open in H4. simpl in H4.  *)
(*    rewrite open_rec_term with (t := v) (k := 0) (u := pterm_fvar x); trivial. *)
(*    apply H4; trivial. *)
(*  clear H4 H1 L. inversion Q. clear Q H H0 H1 H3 H4 H5 H6 H7 u L t1 t2.    *)
(*  unfold VarSet.Subset in H8. setoid_rewrite in_union in H8. *)
(*  intros y Hy.  assert (Q : y \in S \/ y \in {{x}}). apply H8; trivial. clear H8. *)
(*  destruct Q; trivial. apply in_singleton in H. rewrite H in Hy. contradiction. *)
(*  exists {}. split; intros. *)
(*  inversion H1. clear H1 H2 H3 t1 t2. *)
(*  apply lab_term_sub' with (L := L \u (fv t)); trivial. intros x Hx. unfold open in *|-*. *)
(*  apply notin_union in Hx. destruct Hx. *)
(*  assert (Q : lab_term ({} \u {{x}}) (t [[u]] ^ x)). apply H4; trivial. clear H4 H1 L. *)
(*  unfold open in Q. simpl in Q. rewrite <- open_rec_term with (t := u) in Q; trivial. *)
(*  inversion Q. clear Q H1 H3 H5 H8 t1 t2. simpl. rewrite <- open_rec_term with (t := v); trivial. *)
(*  apply lab_term_sub' with (L := L \u (fv t)); trivial. intros y Hy. unfold open in *|-*. *)
(*  apply notin_union in Hy. destruct Hy. *)
(*  assert (Q : lab_term ({} \u {{x}} \u {{y}}) ({0 ~> pterm_fvar y}({1 ~> pterm_fvar x}t))).  *)
(*    apply H4; trivial. clear H4 H1 L.  *)
(*  rewrite <- open_bswap; trivial. rewrite subst_com in Q; try omega; trivial. *)
(*  rewrite swap_eq_open; trivial. apply swap_lab_term; trivial. *)
(*  apply in_union. left. left. trivial.  *)
(*  apply in_union. right. apply in_singleton; trivial. *)
(*  apply subset_trans with (F := {}); trivial. apply subset_union_weak_l. *)
(*  case var_fresh with (L := L). intros x Hx. *)
(*  assert (Q :  lab_term ({} \u {{x}}) (({1 ~> pterm_fvar x}t)[[u]])). *)
(*    unfold open in H4. simpl in H4.  *)
(*    rewrite open_rec_term with (t := u) (k := 0) (u := pterm_fvar x); trivial. *)
(*    apply H4; trivial. *)
(*  clear H4 Hx L. inversion Q; trivial.  *)
(*  case var_fresh with (L := L \u fv u). intros x Hx. apply notin_union in Hx. destruct Hx. *)
(*  assert (Q :  lab_term ({} \u {{x}}) (({1 ~> pterm_fvar x}t)[[u]])). *)
(*    unfold open in H4. simpl in H4.  *)
(*    rewrite open_rec_term with (t := u) (k := 0) (u := pterm_fvar x); trivial. *)
(*    apply H4; trivial. *)
(*  clear H4 H1 L. inversion Q. clear Q H H0 H1 H3 H4 H5 H6 H7 H8 H9 L t1 t2.    *)
(*  unfold VarSet.Subset in H10. setoid_rewrite in_union in H10. *)
(*  intros y Hy.  assert (Q : y \in {} \/ y \in {{x}}). apply H10; trivial. clear H10. *)
(*  destruct Q; trivial. apply in_singleton in H. rewrite H in Hy. contradiction. *)
(*  inversion H1. clear H1 H2 H3 t1 t2. *)
(*  apply lab_term_sub' with (L := L \u (fv t)); trivial. intros x Hx. unfold open in *|-*. *)
(*  apply notin_union in Hx. destruct Hx. *)
(*  assert (Q : lab_term ({} \u {{x}}) ((& t)[[v]] ^ x)). apply H4; trivial. clear H4 H1 L. *)
(*  unfold open in Q. simpl in Q. rewrite <- open_rec_term with (t := v) in Q; trivial. *)
(*  inversion Q. clear Q H1 H3 H5 H8 t1 t2. simpl. rewrite <- open_rec_term with (t := u); trivial. *)
(*  apply lab_term_sub' with (L := L \u (fv t)); trivial. intros y Hy. unfold open in *|-*. *)
(*  apply notin_union in Hy. destruct Hy. *)
(*  assert (Q : lab_term ({} \u {{x}} \u {{y}}) ({0 ~> pterm_fvar y}({1 ~> pterm_fvar x}(& t)))).  *)
(*    apply H4; trivial. clear H4 H1 L.  *)
(*  rewrite <- open_bswap in Q; trivial. rewrite subst_com; try omega; trivial. *)
(*  rewrite swap_eq_open; trivial. apply swap_lab_term; trivial. *)
(*  apply in_union. right. apply in_singleton; trivial. *)
(*  apply in_union. left. apply in_union. right. apply in_singleton; trivial. *)
(*  apply subset_trans with (F := {}); trivial. apply subset_union_weak_l. *)
(*  case var_fresh with (L := L). intros x Hx. *)
(*  assert (Q :  lab_term ({} \u {{x}}) (({1 ~> pterm_fvar x}(& t))[[v]])). *)
(*    unfold open in H4. simpl in H4.  *)
(*    rewrite open_rec_term with (t := v) (k := 0) (u := pterm_fvar x); trivial. *)
(*    apply H4; trivial. *)
(*  clear H4 Hx L. inversion Q; trivial.  *)
(*  case var_fresh with (L := L \u fv v). intros x Hx. apply notin_union in Hx. destruct Hx. *)
(*  assert (Q :  lab_term ({} \u {{x}}) (({1 ~> pterm_fvar x}(&t))[[v]])). *)
(*    unfold open in H4. simpl in H4.  *)
(*    rewrite open_rec_term with (t := v) (k := 0) (u := pterm_fvar x); trivial. *)
(*    apply H4; trivial. *)
(*  clear H4 H1 L. inversion Q. clear Q H H0 H1 H3 H4 H5 H6 H7 H8 H9 L t1 t2.    *)
(*  unfold VarSet.Subset in H10. setoid_rewrite in_union in H10. *)
(*  intros y Hy.  assert (Q : y \in {} \/ y \in {{x}}). apply H10; trivial. clear H10. *)
(*  destruct Q; trivial. apply in_singleton in H. rewrite H in Hy. contradiction. *)
(* Qed. *)

(* Lemma red_swap_Lab_sys_x : red_swap lab_sys_x. *)
(* Proof.  *)
(*  intros_all. induction H; simpl. *)
(*  (* lab_reg_rule_var *) *)
(*  apply lab_reg_rule_var with (S := S \u {{x}} \u {{y}}). *)
(*  apply lab_term_sub' with (L := {}); inversion H; clear H H0 H1 t1 t2.  *)
(*  intros z Hz. unfold open. simpl. apply lab_term_var.  *)
(*  apply swap_term; trivial. apply lex_SN_swap; trivial. *)
(*  apply fv_subset_swap; trivial. *)
(*  (* lab_reg_rule_gc *) *)
(*  apply lab_reg_rule_gc with (S := S \u {{x}} \u {{y}}); simpl. *)
(*  apply swap_lab_term.  *)
(*  apply in_union. left. apply in_union. right. apply in_singleton; trivial. *)
(*  apply in_union. right. apply in_singleton; trivial. *)
(*  apply lab_term_subset with (S := S); trivial. *)
(*  apply subset_trans with (F := S \u {{x}}); apply subset_union_weak_l. *)
(*  inversion H0. clear H0 H1 H2 t1 t2. apply lab_term_sub' with (L := L \u {{x}} \u {{y}}). *)
(*  intros z Hz. apply notin_union in Hz. destruct Hz. apply notin_union in H0. destruct H0. *)
(*  apply notin_singleton in H1. apply notin_singleton in H2. rewrite open_swap; trivial. *)
(*  apply swap_lab_term. apply in_union. left. apply in_union. left. apply in_union. right. *)
(*  apply in_singleton; trivial. *)
(*  apply in_union. left. apply in_union. right. apply in_singleton; trivial. *)
(*  apply lab_term_subset with (S := S \u {{z}}).  *)
(*  rewrite union_comm with (E := S \u {{x}} \u {{y}}) (F := {{z}}).  *)
(*  rewrite union_assoc. rewrite union_assoc. rewrite union_comm with (E := {{z}}). *)
(*  rewrite <- union_assoc. apply subset_union_weak_l. apply H3; trivial. *)
(*  apply swap_term; trivial. apply lex_SN_swap; trivial. apply swap_fvar. *)
(*  apply in_union. left. apply in_union. right. apply in_singleton; trivial. *)
(*  apply in_union. right. apply in_singleton; trivial.  *)
(*  apply subset_trans with (F := S); trivial. rewrite <- union_assoc. *)
(*  apply subset_union_weak_l. *)
(*  (* lab_reg_rule_app *) *)
(*  apply lab_reg_rule_app with (S := S \u {{x}} \u {{y}}). apply swap_lab_body. *)
(*  apply in_union. left. apply in_union. right. apply in_singleton; trivial. *)
(*  apply in_union. right. apply in_singleton; trivial. *)
(*  apply lab_body_subset with (S := S); trivial. rewrite <- union_assoc. apply subset_union_weak_l.   *)
(*  inversion H0. clear H0 H1 H2 t0 t3. *)
(*  apply lab_term_sub' with (L := L \u {{x}} \u {{y}}). intros z Hz. *)
(*  apply notin_union in Hz. destruct Hz. apply notin_union in H0. destruct H0. *)
(*  apply notin_singleton in H1. apply notin_singleton in H2. rewrite open_swap; trivial. *)
(*  apply swap_lab_term. apply in_union. left. apply in_union. left. apply in_union. right. *)
(*  apply in_singleton; trivial. *)
(*  apply in_union. left. apply in_union. right. apply in_singleton; trivial. *)
(*  apply lab_term_subset with (S := S \u {{z}}).  *)
(*  rewrite union_comm with (E := S \u {{x}} \u {{y}}) (F := {{z}}).  *)
(*  rewrite union_assoc. rewrite union_assoc. rewrite union_comm with (E := {{z}}). *)
(*  rewrite <- union_assoc. apply subset_union_weak_l. apply H3; trivial. *)
(*  apply swap_term; trivial. apply lex_SN_swap; trivial. apply swap_fvar. *)
(*  apply in_union. left. apply in_union. right. apply in_singleton; trivial. *)
(*  apply in_union. right. apply in_singleton; trivial.  *)
(*  apply subset_trans with (F := S); trivial. rewrite <- union_assoc. *)
(*  apply subset_union_weak_l. *)
(*  (* lab_reg_rule_lamb *) *)
(*  inversion H. clear H H0 H1 t1 t2. unfold bswap. rewrite bswap_swap_comm. *)
(*  apply lab_reg_rule_lamb with (S := S \u {{x}} \u {{y}}). *)
(*  apply lab_term_sub' with (L := L \u {{x}} \u {{y}}). intros z Hz. *)
(*  apply notin_union in Hz. destruct Hz. apply notin_union in H. destruct H. *)
(*  apply notin_singleton in H0. apply notin_singleton in H1. unfold open. simpl. *)
(*  assert (Q :  lab_term (S \u {{z}}) (pterm_abs t ^ z)). apply H2; trivial. *)
(*  clear H2 H L. inversion Q. clear Q H t1.  *)
(*  apply lab_term_abs with (L := L \u {{x}} \u {{y}} \u {{z}}). intros w Hw. *)
(*  apply notin_union in Hw. destruct Hw. apply notin_union in H. destruct H. *)
(*  apply notin_union in H. destruct H.  apply notin_singleton in H6.  *)
(*  apply notin_singleton in H7. apply notin_singleton in H8. unfold open.  *)
(*  rewrite <- swap_var_id with (x := x) (y := y) (z := z); trivial. *)
(*  rewrite <- swap_var_id with (x := x) (y := y) (z := w); trivial. *)
(*  rewrite <- open_swap_comm. rewrite <- open_swap_comm. apply swap_lab_term.   *)
(*  apply in_union. left. apply in_union. left.  *)
(*  apply in_union. left. apply in_union. right. apply in_singleton. trivial. *)
(*  apply in_union. left. apply in_union. left.  *)
(*  apply in_union. right. apply in_singleton. trivial. *)
(*  apply lab_term_subset with (S := S \u {{z}} \u {{w}}).  *)
(*  rewrite <- union_assoc with (E :=  S \u {{x}} \u {{y}}). *)
(*  rewrite union_comm with (F := {{z}} \u {{w}}).   *)
(*  rewrite union_assoc with (E := {{z}} \u {{w}}). *)
(*  rewrite union_assoc with (E := {{z}} \u {{w}}). *)
(*  rewrite union_comm with (F := S). rewrite union_assoc.  *)
(*  rewrite <-  union_assoc with (E :=  S \u {{z}} \u {{w}}). *)
(*  apply subset_union_weak_l. apply H2; trivial.  *)
(*  apply swap_term; trivial. apply lex_SN_swap; trivial. apply swap_fvar.  *)
(*  apply in_union. left. apply in_union. right. apply in_singleton. trivial. *)
(*  apply in_union. right. apply in_singleton. trivial. *)
(*  apply subset_trans with (F := S); trivial. rewrite <- union_assoc. *)
(*  apply subset_union_weak_l.   *)
(*  (* lab_reg_rule_comp *) *)
(*  unfold bswap. rewrite bswap_swap_comm.  *)
(*  apply lab_reg_rule_comp with (S := S \u {{x}} \u {{y}}). *)
(*  inversion H. clear H H1 H2 t1 t2. *)
(*  apply lab_term_sub' with (L := L \u {{x}} \u {{y}}). intros z Hz. *)
(*  apply notin_union in Hz. destruct Hz. apply notin_union in H. destruct H. *)
(*  apply notin_singleton in H1. apply notin_singleton in H2. unfold open. simpl. *)
(*  assert (Q :  lab_term (S \u {{z}}) ((t[u]) ^ z)). apply H3; trivial. *)
(*  clear H3 H L. inversion Q. clear Q H H3 t1 t2.  *)
(*  apply lab_term_sub with (L := L \u {{x}} \u {{y}} \u {{z}}). intros w Hw. *)
(*  apply notin_union in Hw. destruct Hw. apply notin_union in H. destruct H. *)
(*  apply notin_union in H. destruct H.  apply notin_singleton in H3.  *)
(*  apply notin_singleton in H9. apply notin_singleton in H10. unfold open.  *)
(*  rewrite <- swap_var_id with (x := x) (y := y) (z := z); trivial. *)
(*  rewrite <- swap_var_id with (x := x) (y := y) (z := w); trivial. *)
(*  rewrite <- open_swap_comm. rewrite <- open_swap_comm. apply swap_lab_term.   *)
(*  apply in_union. left. apply in_union. left.  *)
(*  apply in_union. left. apply in_union. right. apply in_singleton. trivial. *)
(*  apply in_union. left. apply in_union. left.  *)
(*  apply in_union. right. apply in_singleton. trivial. *)
(*  apply lab_term_subset with (S := S \u {{z}} \u {{w}}).  *)
(*  rewrite <- union_assoc with (E :=  S \u {{x}} \u {{y}}). *)
(*  rewrite union_comm with (F := {{z}} \u {{w}}).   *)
(*  rewrite union_assoc with (E := {{z}} \u {{w}}). *)
(*  rewrite union_assoc with (E := {{z}} \u {{w}}). *)
(*  rewrite union_comm with (F := S). rewrite union_assoc.  *)
(*  rewrite <-  union_assoc with (E :=  S \u {{z}} \u {{w}}). *)
(*  apply subset_union_weak_l. apply H7; trivial.  *)
(*  rewrite <- swap_var_id with (x := x) (y := y) (z := z); trivial. *)
(*  rewrite <- open_swap_comm. apply swap_lab_term. *)
(*  apply in_union. left. apply in_union. left. apply in_union. right. apply in_singleton. trivial. *)
(*  apply in_union. left. apply in_union. right. apply in_singleton. trivial. *)
(*  apply lab_term_subset with (S := S \u {{z}}); trivial. *)
(*  rewrite union_comm with (E := S \u {{x}} \u {{y}}) (F := {{z}}).  *)
(*  rewrite union_assoc. rewrite union_assoc. rewrite union_comm with (E := {{z}}). *)
(*  rewrite <- union_assoc. apply subset_union_weak_l. *)
(*  apply swap_term; trivial. apply lex_SN_swap; trivial. apply swap_fvar.  *)
(*  apply in_union. left. apply in_union. right. apply in_singleton. trivial. *)
(*  apply in_union. right. apply in_singleton. trivial. *)
(*  apply subset_trans with (F := S); trivial. rewrite <- union_assoc. apply subset_union_weak_l.   *)
(*  intro H'. apply H0. apply swap_term with (x := x) (y := y) in H'. *)
(*  rewrite swap_inv in H'; trivial. *)
(* Qed. *)

(* Lemma red_swap_Lab_sys_Bx : red_swap lab_sys_Bx. *)
(* Proof.  *)
(*  intros_all. destruct H; simpl. destruct H; simpl. *)
(*  apply lab_B_lx. apply lab_reg_rule_b with (S := S \u {{x}} \u {{y}}). apply swap_lab_body.  *)
(*  apply in_union. left. apply in_union. right. apply in_singleton; trivial. *)
(*  apply in_union. right. apply in_singleton; trivial.  *)
(*  apply lab_body_subset with (S := S); trivial. rewrite <- union_assoc. apply subset_union_weak_l. *)
(*  apply swap_term; trivial. apply swap_fvar.  *)
(*  apply in_union. left. apply in_union. right. apply in_singleton; trivial.  *)
(*  apply in_union. right. apply in_singleton; trivial.  *)
(*  apply subset_trans with (F := S); trivial. rewrite <- union_assoc. apply subset_union_weak_l. *)
(*  apply lex_SN_swap; trivial. *)
(*  apply lab_sys_x_lx. apply red_swap_Lab_sys_x; trivial. *)
(* Qed. *)

(* Lemma red_swap_lab_eqc : red_swap lab_eqc. *)
(* Proof.  *)
(*  intros_all. destruct H; unfold bswap; simpl; try rewrite bswap_swap_comm. *)
(*  apply lab_eqc_rf. apply lab_eqc_rx1 with (S := S \u {{x}} \u {{y}}). apply swap_lab_term.  *)
(*  apply in_union. left. apply in_union. right. apply in_singleton; trivial. *)
(*  apply in_union. right. apply in_singleton; trivial. *)
(*  apply lab_term_subset with (S := S); trivial. rewrite <- union_assoc. apply subset_union_weak_l. *)
(*  apply swap_term; trivial. *)
(*  apply lab_eqc_rx2; apply swap_term; trivial. *)
(* Qed. *)

(* Lemma ctx_lab_regular : forall R, red_lab_regular R -> red_lab_regular (lab_contextual_closure R). *)
(* Proof. *)
(*  intros_all. induction H0. apply H; trivial. *)
(*  case IHlab_contextual_closure; clear IHlab_contextual_closure; intros S' H2. *)
(*  exists (S \u S'). destruct H2. split; apply lab_term_app; trivial.  *)
(*  apply lab_term_subset with (S := S'); trivial. apply subset_union_weak_r. *)
(*  apply lab_term_subset with (S := S); trivial. apply subset_union_weak_l. *)
(*  apply lab_term_subset with (S := S'); trivial. apply subset_union_weak_r. *)
(*  apply lab_term_subset with (S := S); trivial. apply subset_union_weak_l. *)
(*  case IHlab_contextual_closure; clear IHlab_contextual_closure; intros S' H2. *)
(*  exists (S \u S'). destruct H2. split; apply lab_term_app; trivial.  *)
(*  apply lab_term_subset with (S := S); trivial. apply subset_union_weak_l. *)
(*  apply lab_term_subset with (S := S'); trivial. apply subset_union_weak_r. *)
(*  apply lab_term_subset with (S := S); trivial. apply subset_union_weak_l. *)
(*  apply lab_term_subset with (S := S'); trivial. apply subset_union_weak_r. *)
(*  pick_fresh x. apply notin_union in Fr. destruct Fr. apply notin_union in H2. destruct H2. *)
(*  assert (Q:  exist S, lab_term S (t ^ x) /\ lab_term S (t' ^ x)). apply H1; trivial. *)
(*  clear H0 H1 H2 L. case Q; clear Q. intros S Q. destruct Q. exists (S \u {{x}}). *)
(*  split; apply lab_term_abs with (L := (fv t) \u (fv t')); intros y Hy; *)
(*  apply notin_union in Hy; destruct Hy.  *)
(*  apply lab_term_subset with (S' := S \u {{x}} \u {{y}}) in H0.  *)
(*  apply swap_lab_term' with (x := x); trivial. *)
(*  apply in_union. left. apply in_union. right. apply in_singleton; trivial. *)
(*  apply in_union. right. apply in_singleton; trivial. *)
(*  rewrite <- union_assoc. apply subset_union_weak_l. *)
(*  apply lab_term_subset with (S' := S \u {{x}} \u {{y}}) in H1.  *)
(*  apply swap_lab_term' with (x := x); trivial. *)
(*  apply in_union. left. apply in_union. right. apply in_singleton; trivial. *)
(*  apply in_union. right. apply in_singleton; trivial. *)
(*  rewrite <- union_assoc. apply subset_union_weak_l. *)
(*  case var_fresh with (L := L \u (fv t) \u (fv t')). intros x Fr. *)
(*  apply notin_union in Fr. destruct Fr. apply notin_union in H3. destruct H3. *)
(*  assert (Q:  exist S, lab_term S (t ^ x) /\ lab_term S (t' ^ x)). apply H2; trivial. *)
(*  clear H1 H2 H3 L. case Q; clear Q. intros S' Q. destruct Q. exists (S' \u S \u {{x}}). *)
(*  split; apply lab_term_sub with (L := (fv t) \u (fv t')); try intros y Hy; *)
(*  try apply notin_union in Hy; try destruct Hy.  *)
(*  apply lab_term_subset with (S' := S' \u S \u {{x}} \u {{y}}) in H1.  *)
(*  apply swap_lab_term' with (x := x); trivial. *)
(*  apply in_union. left. apply in_union. right. apply in_singleton; trivial. *)
(*  apply in_union. right. apply in_singleton; trivial. *)
(*  rewrite <- union_assoc.  rewrite <- union_assoc. apply subset_union_weak_l. *)
(*  apply lab_term_subset with (S := S); trivial. rewrite union_comm with (E := S'). *)
(*  rewrite <- union_assoc. apply subset_union_weak_l. *)
(*  apply lab_term_subset with (S' := S' \u S \u {{x}} \u {{y}}) in H2.  *)
(*  apply swap_lab_term' with (x := x); trivial. *)
(*  apply in_union. left. apply in_union. right. apply in_singleton; trivial. *)
(*  apply in_union. right. apply in_singleton; trivial. *)
(*  rewrite <- union_assoc.  rewrite <- union_assoc. apply subset_union_weak_l. *)
(*  apply lab_term_subset with (S := S); trivial. rewrite union_comm with (E := S'). *)
(*  rewrite <- union_assoc. apply subset_union_weak_l. *)
(*  case IHlab_contextual_closure; clear IHlab_contextual_closure; intros S' H2. *)
(*  exists (S \u S'). destruct H2. inversion H0. clear H0. *)
(*  split; apply lab_term_sub with (L := x); try intros y Hy. *)
(*  apply lab_term_subset with (S := S \u {{y}}). rewrite <- union_assoc. *)
(*  rewrite union_comm with (E := S'). rewrite union_assoc. apply subset_union_weak_l. *)
(*  apply H4; trivial. apply lab_term_subset with (S := S'); trivial. apply subset_union_weak_r. *)
(*  apply lab_term_subset with (S := S \u {{y}}). rewrite <- union_assoc. *)
(*  rewrite union_comm with (E := S'). rewrite union_assoc. apply subset_union_weak_l. *)
(*  apply H4; trivial. apply lab_term_subset with (S := S'); trivial. apply subset_union_weak_r. *)
(*  case var_fresh with (L := L \u (fv t) \u (fv t')). intros x Fr. *)
(*  apply notin_union in Fr. destruct Fr. apply notin_union in H4. destruct H4. *)
(*  assert (Q:  exist S, lab_term S (t ^ x) /\ lab_term S (t' ^ x)). apply H3; trivial. *)
(*  clear H2 H3 H4 L. case Q; clear Q. intros S Q. destruct Q. exists (S \u (fv u) \u {{x}}). *)
(*  split; apply lab_term_sub' with (L := (fv t) \u (fv t')); trivial.  *)
(*  intros y Hy. apply notin_union in Hy. destruct Hy. *)
(*  apply lab_term_subset with (S' := S \u (fv u) \u {{x}} \u {{y}}) in H2.  *)
(*  apply swap_lab_term' with (x := x); trivial. *)
(*  apply in_union. left. apply in_union. right. apply in_singleton; trivial. *)
(*  apply in_union. right. apply in_singleton; trivial. *)
(*  rewrite <- union_assoc.  rewrite <- union_assoc. apply subset_union_weak_l. *)
(*  rewrite union_comm with (E := S). rewrite <- union_assoc. apply subset_union_weak_l. *)
(*  intros y Hy. apply notin_union in Hy. destruct Hy. *)
(*  apply lab_term_subset with (S' := S \u (fv u) \u {{x}} \u {{y}}) in H3.  *)
(*  apply swap_lab_term' with (x := x); trivial. *)
(*  apply in_union. left. apply in_union. right. apply in_singleton; trivial. *)
(*  apply in_union. right. apply in_singleton; trivial. *)
(*  rewrite <- union_assoc.  rewrite <- union_assoc. apply subset_union_weak_l. *)
(*  rewrite union_comm with (E := S). rewrite <- union_assoc. apply subset_union_weak_l. *)
(*  exists S. inversion H0. clear H0. generalize H3. intro H5. apply ctx_sys_Bex_regular in H5.  *)
(*  destruct H5. split; apply lab_term_sub' with (L := x); trivial. *)
(*  case H1; clear H1; intros n H1. inversion H1; clear H1. case (H6 u'); trivial; clear H6. *)
(*  intros k H1. exists k. apply H1. intros a H6. unfold VarSet.Subset in H2. apply H2. *)
(*  apply basic_prop1 with (t' := u'); trivial. right; trivial. *)
(* Qed. *)

(*
Lemma ctx_lab_regular' : forall R, red_lab_regular' R -> 
                                    red_lab_regular' (lab_contextual_closure R).
Proof. 
 intros R H. unfold red_lab_regular' in *|-*. intros t t' H'. induction H'.
 case (H t s); trivial.  intros S H1. exists S; trivial.
 case IHH'; clear IHH'; intros S' H1. exists (S \u S'). split.
 intro H2. inversion H2. clear H2 H3 H4 t1 t2. apply lab_term_app.
 
case IHH'2; clear IHH'2; intros S' H2. 
 exists (S \u S'). split; intro H3. inversion H3. clear H0 H3 H4 t1 t2.
 apply lab_term_app. destruct H1. apply lab_term_subset with (S := S). 

 apply lab_term_subset with (S := S). 
 apply lab_term_subset with (S := S'); try apply H2; trivial].

 skip. skip. skip. skip. 
 Admitted.
*)