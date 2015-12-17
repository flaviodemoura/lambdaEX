Set Implicit Arguments.
Require Import  Metatheory LambdaES_Defs Compare_dec LambdaES_Infra LambdaES_FV Rewriting_Defs Lambda_Ex.

Lemma fv_open_ : forall t k x y, x<>y -> (x \in fv ({k~>pterm_fvar y}t )  <-> x \in fv t).
Proof.
  induction t.
  (*SearchAbout VarSet.elt.*)
  (*Caso t: bvar n*)
  intros. simpl.
  case_nat.
  simpl. split. intro.
  apply notin_singleton_l in H.
  contradiction.
  intro.
  apply in_empty in H0. contradiction. 
  simpl; reflexivity.
  
  (*Caso t: fvar v*)
  intros. simpl. reflexivity. 
  
  (*Caso t: app t1 t2*)
  intros. simpl.
  repeat rewrite in_union.
  rewrite IHt1. rewrite IHt2.
  reflexivity. assumption. assumption.
  
  (*Caso t: abs t*)
  intros. simpl. rewrite IHt.
  reflexivity. assumption.
  
  (*Caso t: t1 [t2]*)
  intros. simpl.
  repeat rewrite in_union.
  rewrite IHt1. rewrite IHt2.
  reflexivity. assumption. assumption.
  
  (*Caso t: t1 [[t2]]*)
  intros. simpl.
  repeat rewrite in_union.
  rewrite IHt1. rewrite IHt2.
  reflexivity. assumption. assumption.
Qed.

Lemma fv_open_in_neq : forall t x y, x<>y -> (x \in fv(t^y )  <-> x \in fv t).
Proof.
  induction t.
  
  (*Caso t: bvar n*)
  intros. simpl.
  case n.
  simpl. split. intro.
  apply notin_singleton_l in H.
  contradiction.
  intro. apply in_empty in H0.
  contradiction.
  simpl. reflexivity.
  
  (*Caso t: fvar v*)
  intros. simpl. reflexivity.
  
  (*Caso t: app t1 t2*)
  intros. simpl.
  repeat rewrite in_union.
  repeat rewrite fv_open_.
  reflexivity. assumption. assumption.
  
  (*Caso t: abs t*)
  intros. simpl.
  rewrite fv_open_. reflexivity.
  assumption.
  
  (*Caso t: t1 [t2]*)
  intros. simpl.
  repeat rewrite in_union.
  repeat rewrite fv_open_.
  reflexivity. assumption. assumption.
  
  (*Caso t: t1 [[t2]]*)
  intros. simpl.
  repeat rewrite in_union.
  repeat rewrite fv_open_.
  reflexivity. assumption. assumption.
Qed.
    
Lemma notin_fv_close : forall t k x, x \notin fv (close_rec k x t).
Proof.
  induction t.
  
  (*Caso t: bvar n*)
  intros. simpl.
  apply notin_empty.
  
  (*Caso t: fvar v*)
  intros. simpl.
  case (v == x).
  intro. simpl. apply notin_empty.
  intro. simpl.
  apply notin_singleton_swap.
  apply notin_singleton. assumption.
  
  
  (*Caso t: app t1 t2*)
  intros. simpl.
  rewrite notin_union.
  split. apply IHt1.
  apply IHt2.
  
  (*Caso t: abs t*)
  intros. simpl.
  apply IHt.
  
  (*Caso t: t1 [t2]*)
  intros. simpl.
  rewrite notin_union.
  split. apply IHt1.
  apply IHt2.
  
  (*Caso t: t1 [[t2]]*)
  intros. simpl.
  rewrite notin_union.
  split. apply IHt1.
  apply IHt2.
Qed.

Lemma fv_in_or_notin : forall t x, x \in fv t \/ x \notin fv t.
Proof.
  induction t.
  intro.
  right. simpl.
  apply notin_empty.

  intro.
  case (x == v). intro.
  left. rewrite e. simpl.
  SearchAbout VarSet.elt.
  apply in_singleton; reflexivity.

  intro.
  right. simpl.
  apply notin_singleton. assumption.
  
  intro.
  simpl. rewrite notin_union.
  rewrite in_union.
  destruct IHt1 with (x:=x).
  left; left; assumption.
  destruct IHt2 with (x:=x).
  left; right; assumption.
  right; split; assumption.
  
  intro. simpl.
  apply IHt.
  
  intro. simpl.
  rewrite notin_union.
  rewrite in_union.
  destruct IHt1 with (x:=x).
  left; left; assumption.
  destruct IHt2 with (x:=x).
  left; right; assumption.
  right; split; assumption.
  
  intro. simpl.
  rewrite notin_union.
  rewrite in_union.
  destruct IHt1 with (x:=x).
  left; left; assumption.
  destruct IHt2 with (x:=x).
  left; right; assumption.
  right; split; assumption.
Qed.

(**Definicao de um termo simples,
sterm, sem substituições explícitas
t:= fvar x | abs x t | app t t 
Inductive sterm : pterm -> Prop :=
  | sterm_var : forall x,
      sterm (pterm_fvar x)
  | sterm_app : forall t1 t2,
      sterm t1 -> 
      sterm t2 -> 
      sterm (pterm_app t1 t2)
  | sterm_abs : forall L t1,
      (forall x, x \notin L -> sterm (t1 ^ x)) ->
      sterm (pterm_abs t1).*)


Fixpoint lc_at' (k:nat) (t:pterm) {struct t} : Prop :=
  match t with 
  | pterm_bvar i    => i < k
  | pterm_fvar x    => True
  | pterm_app t1 t2 => lc_at' k t1 /\ lc_at' k t2
  | pterm_abs t1    => lc_at' (S k) t1
  | pterm_sub t1 t2 => (lc_at' (S k) t1) /\ lc_at' k t2
  | pterm_sub' t1 t2 => (
    match t2 with
    | pterm_sub' t1' t2' => False
    | _ => (SN lex t2) /\ lc_at' k t2
    end) /\ (lc_at' (S k) t1) 
  end.

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

Lemma lc_at_le: forall t n m, n <= m ->
      lc_at' n t -> lc_at' m t.
Proof.
  induction t. simpl.
  intros n0 m0 H H1.
  apply Lt.lt_le_trans with n0;
  assumption.
  
  simpl. intros. constructor.
  
  simpl. intros. destruct H0.
  split. apply IHt1 with n; assumption.
  apply IHt2 with n; assumption.
  
  simpl. intros. apply IHt with (S n).
  apply Le.le_n_S. assumption.
  assumption.
  
  simpl. intros. destruct H0.
  split. apply IHt1 with (S n).
  apply Le.le_n_S. assumption. assumption.
  apply IHt2 with n. assumption. assumption.
  
  simpl. intros.
  case t2 in *.
    destruct H0. destruct H0.
    split. split. assumption.
    apply IHt2 with n; assumption.
    apply IHt1 with (S n).
    apply Le.le_n_S. assumption.
    assumption.
    
    destruct H0. destruct H0.
    split. split. assumption.
    apply IHt2 with n; assumption.
    apply IHt1 with (S n).
    apply Le.le_n_S; assumption.
    assumption.
    
    destruct H0. destruct H0.
    split. split. assumption.
    apply IHt2 with n; assumption.
    apply IHt1 with (S n).
    apply Le.le_n_S; assumption.
    assumption.
    
    destruct H0. destruct H0.
    split. split. assumption.
    apply IHt2 with n; assumption.
    apply IHt1 with (S n).
    apply Le.le_n_S; assumption.
    assumption.
    
    destruct H0. destruct H0.
    split. split. assumption.
    apply IHt2 with n; assumption.
    apply IHt1 with (S n).
    apply Le.le_n_S; assumption.
    assumption.
    
    destruct H0. contradiction.
Qed.

Lemma term_open_lab_term_open: forall t x, term (t^x) -> lab_term (t^x).
Proof.
  intros. induction H.
    apply lab_term_var.
    
    apply lab_term_app.
    apply IHterm1; assumption.
    apply IHterm2; assumption.
    
    pick_fresh y.
    apply notin_union in Fr; destruct Fr.
    apply notin_union in H1; destruct H1.
    apply notin_union in H1; destruct H1.
    apply lab_term_abs with L.
    intros. apply H0. assumption.
    
    pick_fresh y.
    apply notin_union in Fr; destruct Fr.
    apply notin_union in H2; destruct H2.
    apply notin_union in H2; destruct H2.
    apply notin_union in H2; destruct H2.
    apply lab_term_sub with L.
    intros. apply H0. assumption.
    assumption.
Qed.

Lemma term_lab_term: forall t, term t -> lab_term t.
Proof.
  induction t.
  intro. inversion H.
  
  intro. apply lab_term_var.
  
  intro. inversion H.
  apply lab_term_app.
  apply IHt1; assumption.
  apply IHt2; assumption.
  
  intro. inversion H.
  pick_fresh x.
  apply lab_term_abs with L. intros.
  apply term_open_lab_term_open.
  apply H1. assumption.
  
  intro. inversion H.
  pick_fresh x.
  apply lab_term_sub with L. intros.
  apply term_open_lab_term_open.
  apply H2. assumption.
  apply IHt2. assumption.
  
  intro. inversion H.
Qed.

Lemma lc_at_open_abs: 
      forall t x, lc_at' 1 t  <-> lc_at' 0 (t^x).
Proof.
  intros. split.
  generalize dependent x.
  generalize dependent t.
  induction t using pterm_size_induction.
  
  intros.
  unfold open. simpl.
  case n in *.
    simpl. constructor.
    inversion H. inversion H1. 
  
  simpl. intros. constructor.
  
  Focus 2.
  simpl. intros. destruct H.
  split.
  apply IHt1. assumption.
  apply IHt2. assumption.
  
  Focus 2. simpl. intros.
  destruct H0. split. 
  Focus 2. apply IHt1. assumption.
  SearchAbout open.
(*PAREI AQUI*)
Admitted.  

Lemma lab_term_to_lc_at': forall t i, lab_term t -> lc_at' i t.
Proof.
  assert (forall t x, lc_at' 0 (t^x) -> lc_at' 1 t). 
  apply lc_at_open_abs.
  assert (forall t x i, lc_at' 0 (t^x) -> lc_at' 1 t -> lc_at' (S i) t).
  intros.
  apply lc_at_le with 1.
  apply Le.le_n_S. apply Le.le_0_n. assumption.
  
  induction t using pterm_size_induction.
  intros.
  inversion H1.

  intros.
  simpl. constructor.

  intros. simpl.
  inversion H2. subst.
  pick_fresh x.
  apply notin_union in Fr; destruct Fr.
  apply notin_union in H3; destruct H3.
  apply H0 with x.
    apply H1. assumption. reflexivity.
    apply H4. assumption.
    
    apply H with x. apply H1.
    assumption. reflexivity.
    apply H4. assumption.
  
  intros. simpl.
  inversion H1. split.
  apply IHt1; assumption.
  apply IHt2; assumption.
  
  intros. simpl.
  inversion H2. subst.
  pick_fresh x.
  apply notin_union in Fr; destruct Fr. 
  apply notin_union in H3; destruct H3.
  apply notin_union in H3; destruct H3.
  split.
    apply H0 with x.
    apply H1. assumption. reflexivity.
    apply H5. assumption.
    apply H with x. apply H1.
    assumption. reflexivity.
    apply H5. assumption.
    
    apply IHt1. assumption.
      
  intros. simpl.
  inversion H2. subst.
  pick_fresh x.
  apply notin_union in Fr; destruct Fr.
  apply notin_union in H3; destruct H3.
  apply notin_union in H3; destruct H3.
  inversion H6. subst.
    simpl. split. split.
    assumption. constructor.
    apply lc_at_le with 1.
      apply Le.le_n_S. apply Le.le_0_n.
      
      apply H with x.
      apply H1. assumption. reflexivity.
      apply H5. assumption.
    
    subst. split. split. assumption.
    apply IHt1. apply term_lab_term.
    assumption.
    apply lc_at_le with 1.
      apply Le.le_n_S. apply Le.le_0_n.
      
      apply H with x. apply H1. assumption. reflexivity.
      apply H5. assumption.
    
    subst. split. split. assumption.
    apply IHt1. apply term_lab_term. assumption.
    apply lc_at_le with 1.
      apply Le.le_n_S. apply Le.le_0_n.
      
      apply H with x. apply H1. assumption. reflexivity.
      apply H5. assumption.
      
    subst. split. split. assumption.
    apply IHt1. apply term_lab_term. assumption.
    apply lc_at_le with 1.
      apply Le.le_n_S. apply Le.le_0_n.
      
      apply H with x. apply H1. assumption. reflexivity.
      apply H5. assumption.
Qed.

Lemma lc_at_open_lab_term_open: forall t x, 
      lc_at' 0 (t^x) -> lab_term (t^x).
Admitted.

Lemma lab_term_equiv_lc_at': forall t, lc_at' 0 t <-> lab_term t.
Proof.
  intro. split.
  Focus 2.
  apply lab_term_to_lc_at'.
  
  intro.
  induction t.
  inversion H.
  
  constructor.
  
  destruct H. apply lab_term_app.
  apply IHt1; assumption.
  apply IHt2; assumption.
  
  simpl in H.
  apply lab_term_abs with (fv t).
  intros.
  assert (lc_at' 1 t -> lc_at' 0 (t^x)).
  apply lc_at_open_abs.
  assert (lc_at' 0 (t^x)).
  apply H1. assumption.
  apply lc_at_open_lab_term_open. assumption.  
  pick_fresh x.
  inversion H.
  apply lab_term_sub with (fv t1 \u fv t2).
    intros. 
    assert (lc_at' 1 t1 -> lc_at' 0 (t1^x0)).
    apply lc_at_open_abs.
    assert (lc_at' 0 (t1^x0)). apply H3. assumption.
    apply lc_at_open_lab_term_open. assumption.
    apply IHt2. assumption.
  
  pick_fresh x.
  assert (forall t x, lc_at' 1 t -> lc_at' 0 (t^x)).
  apply lc_at_open_abs.
  assert (lc_at' 0 (t1 ^ x)).
  apply H0. inversion H. assumption.
  inversion H.
  apply lab_term_sub' with (fv t1 \u fv t2).
  intros. apply lc_at_open_lab_term_open.
  apply H0. assumption.
  case t2 in *.
    destruct H2. inversion H4.
    constructor.
    destruct H2.
Admitted.
(*PAREI AQUI*)
Definition term'' t := lc_at' 0 t.

Definition body'' t := lc_at' 1 t.

Lemma term_term''_equiv: forall t, term t <-> term'' t.
Proof.
  intro. unfold term''. split.
  generalize dependent t. induction 1.
  
  (**Ida *)
  simpl. apply I.
  
  simpl. split.
  apply IHterm1; assumption.
  apply IHterm2; assumption.
  
  simpl. assert (body t1). unfold body. 
  exists L. apply H.
  pick_fresh y. apply notin_union in Fr.
  destruct Fr.
  apply lema1 with y. apply H0. assumption.
  
  simpl. pick_fresh y.
  apply notin_union in Fr. destruct Fr.
  split. apply lema1 with y. apply H0.
  apply notin_union in H2. destruct H2.
  assumption. assumption.
  
  (**Volta*)
  induction t.
  simpl. intro. inversion H.
  
  simpl. intro. apply term_var.
  
  simpl. intro.
  destruct H. apply term_app.
  apply IHt1; assumption.
  apply IHt2; assumption.
  
  simpl. intro.
  apply term_abs with (L:=fv(t)).
  intros.
Admitted.

Fixpoint xc_rec (n:nat) (t: pterm) : pterm :=
  match t with
    | pterm_app t1 t2 => pterm_app (xc_rec n t1) (xc_rec n t2)
    | pterm_abs t1 => pterm_abs (xc_rec (S n) t1)
    | pterm_sub t1 t2 => pterm_sub (xc_rec (S n) t1) (xc_rec n t2)
    | pterm_sub' t1 t2 => (xc_rec (S n) t1)^^(t2)
    | _ => t
  end.

Definition xc (t: pterm) := xc_rec 0 t.
(*
Fixpoint xc (t: pterm) : pterm :=
  match t with
    | pterm_app t1 t2 => pterm_app (xc t1) (xc t2)
    | pterm_abs t1 => pterm_abs (xc t1)
    | pterm_sub t1 t2 => pterm_sub (xc t1) (xc t2)
    | pterm_sub' t1 t2 => (xc t1)^^(t2)
    | _ => t
  end.
*)

Lemma lc_n_xc_n: forall t n, lc_at' n t -> xc_rec n t = t.
Proof.
  induction t.
  
  simpl; reflexivity.
  
  simpl; reflexivity.
  
  simpl. intros.
  destruct H. rewrite IHt1.
  rewrite IHt2. reflexivity.
  assumption. assumption.
  
  simpl. intros.
  rewrite IHt. reflexivity.
  assumption.
  
  simpl. intros.
  destruct H. rewrite IHt1.
  rewrite IHt2. reflexivity.
  assumption. assumption.
  
  case t2 in *.
  intros. simpl. destruct H. destruct H0.
  rewrite IHt1. 2: assumption.
  2:simpl; intros; destruct H; destruct H0.
  2:rewrite IHt1. 3:assumption.
  3:simpl; intros; destruct H; destruct H0.
  3:rewrite IHt1. 4:assumption.
  4:simpl; intros; destruct H; destruct H0.
  4:rewrite IHt1. 5:assumption.
  5:simpl; intros; destruct H; destruct H0.
  5:rewrite IHt1. 6:assumption.
  6:simpl; intros; destruct H; contradiction.
Admitted.

Lemma xc_term_term: forall t, term' t -> xc t = t.
Proof.
  unfold term'.
  unfold xc. intros. apply lc_n_xc_n.
  assumption.
Qed.

Lemma xc_idempotent: forall t, term' t -> xc(xc(t)) = t.
Proof.
  intros.
  rewrite xc_term_term with (t:=(xc t)).
  apply xc_term_term. assumption.
  rewrite xc_term_term; assumption.
Qed.

Lemma term'_abs_iff_body: forall t, term' (pterm_abs t) <-> body' t.
Proof.
  intro. split. unfold term'. unfold body'.
  simpl. intro. assumption.
  
  unfold body'. unfold term'.
  simpl. intro. assumption.
Qed.

Lemma open_var_term': forall t x, body' t -> term' (t ^ x).
Proof.
  unfold body'. unfold term'.
  induction t.

  simpl. intros. case n in *. simpl.
  apply I. simpl. apply Lt.lt_S_n in H.
  apply Lt.lt_n_0 in H. contradiction.
  
  simpl. intros; assumption.
  
  simpl. intros. destruct H. split.
  apply IHt1; assumption.
  apply IHt2; assumption.
  
  intros.
Admitted.
  
  


Lemma equiv_term_term': forall t, term' t <-> term t.
Proof.
  intro. split. intro.
  induction t.
  
  inversion H.
  
  apply term_var.
  
  inversion H.
  apply term_app.
  apply IHt1. unfold term'. assumption.
  apply IHt2. unfold term'. assumption.
  
  apply term_abs with (L:= {}).
  intros. 
Lemma 
(*
Lemma lc_sterm: forall t n, sterm t -> lc_at' n t -> xc_rec n t = t.
Proof.
  induction 1.
  
  simpl. reflexivity.
  
  simpl. intros. destruct H1.
  rewrite IHsterm1. rewrite IHsterm2.
  reflexivity. assumption. assumption.
  
  simpl. intros. 
Admitted.

Lemma lc_at_Sn: forall t n0 n1, n0 <= n1 -> lc_at n0 t -> lc_at n1 t.
Proof.
  induction t.
  simpl. intros.
  apply Lt.lt_le_trans with n0.
  assumption. assumption.
  
  simpl. intros; assumption.
  
  simpl. intros.
  destruct H0. split.
  apply IHt1 with n0; assumption.
  apply IHt2 with n0; assumption.
  
  simpl. intros. apply IHt with (S n0).
  apply Le.le_n_S. assumption. assumption.
  
  simpl. intros.
  destruct H0. split.
  apply IHt1 with (S n0).
  apply Le.le_n_S. assumption. assumption.
  apply IHt2 with n0. assumption. assumption.
  
  simpl.
  intros. assumption.
Qed.

Lemma xc_rec_Sn: forall t n0 n1, n0 <= n1 -> xc_rec n0 t = t -> xc_rec n1 t = t.
Proof.
  induction t.
  
  simpl. reflexivity.
  
  simpl. reflexivity.
  
  simpl. intros.
  inversion H0. rewrite H2. rewrite H3.
  rewrite IHt1 with n0 n1.
  rewrite IHt2 with n0 n1.
  reflexivity. assumption. assumption.
  assumption. assumption.
  
  simpl. intros. rewrite IHt with (S n0) (S n1).
  reflexivity. apply Le.le_n_S. assumption.
  inversion H0. rewrite H2. assumption.
  
  simpl. intros. rewrite IHt2 with n0 n1.
  rewrite IHt1 with (S n0) (S n1). reflexivity.
  apply Le.le_n_S. assumption.
  inversion H0. rewrite H2. assumption.
  assumption.
  inversion H0. rewrite H3. assumption.
  
  simpl. intros.
  rewrite IHt1 with (S n0) (S n1).
  rewrite <- H0. rewrite IHt1 with (S n0) (S n0).
  reflexivity. reflexivity.
  2: apply Le.le_n_S; assumption.
Admitted.*)

(*
Lemma subst_fv : forall t u, fv(t ^^ u) [=] fv(t) \u fv(u).
Proof.
  induction t.
  intros. simpl.
  case u. intros. simpl.
  Admitted.

  
Lemma xc_open : forall t x, fv (xc (t^x)) [=] fv ((xc t)^x).
Proof.
  Admitted.

Lemma xc_fv: forall t, fv(xc(t)) [=] fv(t).
Proof.
  induction t.
  simpl; reflexivity.
  simpl; reflexivity.
  simpl.
  rewrite IHt1.
  rewrite IHt2.
  reflexivity.
  simpl. assumption.
  simpl.
  rewrite IHt1.
  rewrite IHt2.
  reflexivity.

  simpl.
  rewrite subst_fv.
  rewrite IHt1. reflexivity.
Qed.
  
  (*
Print VarSet.remove.
SearchAbout VarSet.t. 
Lemma lema3: forall t x, term t -> fv (t^x) [=] fv t. (*\rem (fv t \rem x).*)
Proof.
  intros.
  induction H.
  simpl. reflexivity.
  
  simpl.

  unfold open.
  rewrite fv_open_.
  simpl.
  
  assert (term (t1^y)).
  apply H. assumption.
  induction H4.
  simpl.
  
  Focus 2. SearchAbout fv.
  unfold open. induction t1.
  simpl.



  unfold open. apply fv_in_open with (a:=y).
  simpl.  rewrite fv_open_in. apply in_union.
  right. apply in_singleton. reflexivity.
  SearchAbout fv.
  apply LambdaES_FV.fv_open_both_notin with (x:=y).
  rewrite <- xc_open. assumption.
  pick_fresh x.
  apply notin_union in Fr. destruct Fr.
  apply notin_union in H5. destruct H5.
  assert (y<>x -> y \notin fv (xc (t1 ^ x))).
  rewrite xc_open. intro. rewrite fv_open_in_neq.
  2:assumption. 

  apply fset_union_notin with (x:=y).

  rewrite xc_open in H4.
  rewrite LambdaES_FV.fv_open_in in H4.
  rewrite LambdaES_FV.fv_open_in in H4.
  Focus 5.
  *)
Lemma fv_notin_xc: forall t x, term t -> x \notin fv t -> x \notin fv (xc t).
Proof.
  intros t x H. induction H.
  simpl. intro; assumption.
  simpl. intro.
  apply notin_union in H1. destruct H1.
  apply notin_union. split.
  apply IHterm1; assumption.
  apply IHterm2; assumption.
  simpl. intro.
  pick_fresh y.
  apply notin_union in Fr. destruct Fr.
  apply notin_union in H2. destruct H2.
  assert (term (t1 ^y)).
  apply H. assumption.
  assert (x \notin fv (xc (t1 ^ y))).
  apply H0. assumption.
  unfold open. rewrite fv_open_.
  assumption. 
  apply notin_singleton_swap in H4.
  apply notin_singleton. assumption.

  Admitted.



Lemma xc_term_term: forall t, term t -> xc t = t.
Proof.
  intros t H.
  induction H.
  
  unfold xc.
  reflexivity.

  simpl. 
  rewrite IHterm1.
  rewrite IHterm2.
  reflexivity.

  simpl.
  pick_fresh y.
  apply notin_union in Fr.
  destruct Fr. 
  assert (fv(xc(t1)) [=] fv(t1)).
  apply xc_fv.
  generalize H2. intro.
  rewrite <- H3 in H4.
  assert (xc (t1^y) = t1 ^y).
  apply H0.
  assumption.
  rewrite xc_open in H5.
  apply open_var_inj in H5.
  rewrite H5; reflexivity.
  assumption.
  assumption.

  simpl.
  rewrite IHterm.
  pick_fresh y.
  apply notin_union in Fr.
  destruct Fr.
  apply notin_union in H2.
  destruct H2.
  assert (fv(xc(t1)) [=] fv(t1)).
  apply xc_fv.
  generalize H4. intro.
  rewrite <- H5 in H4.
  assert (xc (t1 ^ y) = t1 ^ y).
  apply H0. assumption.
  rewrite xc_open in H7.
  apply open_var_inj in H7.
  rewrite H7. reflexivity.
  assumption. assumption.
Qed.
*)

