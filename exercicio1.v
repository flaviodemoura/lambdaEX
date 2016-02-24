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
(*| pterm_sub t1 t2 => (lc_at' (S k) t1) /\ lc_at' k t2*)
  | pterm_sub t1 t2 => (lc_at' k t1) /\ lc_at' k t2
  | pterm_sub' t1 t2 => (
    match t2 with
    | pterm_sub' t1' t2' => False
(*  | _ => (SN lex t2) /\ lc_at' (S k) t2*)
    | _ => (SN lex t2) /\ lc_at' k t2
  end) /\ (lc_at' k t1)
  end. (*ALTERADOS COM BASE NO SUBST_LC DO CHARGUERAUD*)

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

Inductive lab_term_lc : pterm -> Prop :=
  | lab_term_var_lc : forall x,
      lab_term_lc (pterm_fvar x)
  | lab_term_app_lc : forall t1 t2,
      lab_term_lc t1 -> 
      lab_term_lc t2 -> 
      lab_term_lc (pterm_app t1 t2)
  | lab_term_abs_lc : forall L t1,
      (forall x, x \notin L -> lab_term_lc (t1 ^ x)) ->
      lab_term_lc (pterm_abs t1)
  | lab_term_sub_lc : forall L t1 t2,
     (forall x, x \notin L -> lab_term_lc (t1 ^ x)) ->
      lab_term_lc t2 -> lab_term_lc (t1[t2])
  | lab_term_sub_lc' : forall L t1 t2,
     (forall x, x \notin L -> lab_term_lc (t1 ^ x)) ->
      (lc_at' 0 (t1 [[t2]])) -> (SN lex t2) -> 
      lab_term_lc (t1 [[ t2 ]]).

Definition lc' t := lc_at' 0 t.

Definition body' t := exists L, forall x, x \notin L -> lc_at' 0 (t ^ x).


  
(*
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
*)

Lemma lc_at_abs: forall t n, lc_at' n (pterm_abs t) = lc_at' (S n) t.
Proof.
  simpl. reflexivity.
Qed.

Lemma open_var_lc: forall t x, body' t -> lc_at' 0 (t^x).
Proof.
Admitted.

(*Lemma lc_at_abs_iff_lc_at_open: forall t, 
      lc_at' 0 (pterm_abs t) <-> exist L, (forall x, x \notin L -> lc_at' 0 (t ^ x)).*)
Lemma lc_abs_iff_body: forall t, 
      lc_at' 0 (pterm_abs t) <-> body' t.
Proof.
  unfold body'.
  split. intro. exists (fv t).
  generalize dependent t.
  induction t.
  simpl. intros.
  inversion H. simpl. constructor.
  apply Le.le_Sn_0 in H2. contradiction.
    
  simpl. constructor.
  
  simpl in *. intros.
  apply notin_union in H0. split.
  apply IHt1. apply H. apply H0.
  apply IHt2. apply H. apply H0.
  
  intros.
  apply open_var_lc.
  unfold body'. exists (fv (pterm_abs t)).
  intros. rewrite lc_at_abs in H. simpl in *.
  skip. (*SKIPPED SUBGOAL*)
  
  simpl in *. intros.
  apply notin_union in H0. split.
  (*VERIFICAR COMPORTAMENTO DE sub EM RELACAO A t1*)
Admitted.
  
(** Alteração na definicao de LAB_TERM para LAB_TERM_LC
    exigencia (TERM t2) trocada por (LC_AT 0 (t1 [[t2]])) **)

Lemma lab_term_lc_equiv_lc_at': forall t, lc_at' 0 t <-> lab_term_lc t.
Proof.
  split.
  induction t.
  simpl. intro. apply Lt.lt_n_0 in H. contradiction.
  
  simpl. constructor.
  
  simpl. intro. constructor.
  apply IHt1. apply H.
  apply IHt2. apply H.
  
  intro.
  rewrite lc_abs_iff_body in H.
  destruct H.
  apply lab_term_abs_lc with x.
  intros. assert (lc_at' 0 (t ^ x0)).
  apply H. assumption.
  unfold open in *.
  case t in *.
    simpl. case n in *.
      constructor. inversion H1.
    
    simpl. constructor.
    
    simpl in *. apply lab_term_app_lc.
    
    

(*PAREI AQUI*)
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

