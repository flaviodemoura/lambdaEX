(***************************************************************************
* Formalization of ES calculi						   *
*									   *
* Infrastructure for explicit substitutions, not specific to a calculus    *
*									   *
* Arthur Chargu\u00e9raud, 2007						   *
* Fabien Renaud & St\u00e9phane Zimmerman, 2011				   *
* Flávio L. C. de Moura, 2015                                              *
***************************************************************************)


Set Implicit Arguments.
Require Import  Metatheory LambdaES_Defs LambdaES_Tac LambdaES_FV.
Require Import Arith List. 

(* ********************************************************************** *)
(** * Instanciation of tactics *)

(* Tactic [gather_vars] returns a set of variables occurring in
    the context of proofs, including domain of environments and
    free variables in terms mentionned in the context. *)
Ltac gather_vars :=
  let A := gather_vars_with (fun x : vars => x) in
  let B := gather_vars_with (fun x : var => {{ x }}) in
  let D := gather_vars_with (fun x : pterm => fv x) in
  constr:(A \u B \u D).

(* Tactic [pick_fresh x] adds to the context a new variable x
    and a proof that it is fresh from all of the other variables
    gathered by tactic [gather_vars]. *)
Ltac pick_fresh Y :=
  let L := gather_vars in (pick_fresh_gen L Y).

(* Tactic [apply_fresh T as y] takes a lemma T of the form 
    [forall L ..., (forall x, x \notin L, P x) -> ... -> Q.]
    instanciate L to be the set of variables occurring in the
    context (by [gather_vars]), then introduces for the premise
    with the cofinite quantification the name x as "y" (the second
    parameter of the tactic), and the proof that x is not in L. *)
Tactic Notation "apply_fresh" constr(T) "as" ident(x) :=
  apply_fresh_base T gather_vars x.
Tactic Notation "apply_fresh" "*" constr(T) "as" ident(x) :=
  apply_fresh T as x; auto_star.
Tactic Notation "apply_fresh" constr(T) :=
  apply_fresh_base T gather_vars ltac_no_arg.
Tactic Notation "apply_fresh" "*" constr(T) :=
  apply_fresh T; auto_star.

(** ES terms are expressions without dangling deBruijn indexes. *)
Inductive term : pterm -> Prop :=
  | term_var : forall x,
      term (pterm_fvar x)
  | term_app : forall t1 t2,
      term t1 -> 
      term t2 -> 
      term (pterm_app t1 t2)
  | term_abs : forall L t1,
      (forall x, x \notin L -> term (t1 ^ x)) ->
      term (pterm_abs t1)
  | term_sub : forall L t1 t2,
     (forall x, x \notin L -> term (t1 ^ x)) ->
      term t2 -> 
      term (pterm_sub t1 t2).

Lemma term_size_non_null : forall t, term t -> pterm_size t > 0.
Proof.
  intros t Ht. destruct t.
  simpl; auto.  
  simpl; auto.  
  simpl. omega.
  simpl. omega.
  simpl. omega.
  simpl. omega.
Qed.  

(** Pure lambda terms. *)
Inductive Lterm : pterm -> Prop :=
  | Lterm_var : forall x,
      Lterm (pterm_fvar x)
  | Lterm_app : forall t1 t2,
      Lterm t1 -> 
      Lterm t2 -> 
      Lterm (pterm_app t1 t2)
  | Lterm_abs : forall L t1,
      (forall x, x \notin L -> Lterm (t1 ^ x)) ->
      Lterm (pterm_abs t1).

(** Body *) 
Definition body t := exists L, forall x, x \notin L -> term (t ^ x).

(** Body for pure lambda terms *) 
Definition Lbody t := exists L, forall x, x \notin L -> Lterm (t ^ x).

Hint Constructors term.
Hint Constructors Lterm.

(******************************************************)
(** Lemmas. *)

(* Open_var with fresh names is an injective operation *)
Lemma open_var_inj : forall (x:var) t1 t2, x \notin (fv t1) -> 
	x \notin (fv t2) ->  (t1 ^ x = t2 ^ x) -> (t1 = t2).
Proof.
  intros x t1. unfold open. generalize 0.
  induction t1; intro k; destruct t2; simpl; intros; inversion H1;
  try solve [ f_equal* 
  | do 2 try case_nat; inversions* H1; try notin_contradiction ]. 
  rewrite IHt1_1 with (n:=k) (t2:=t2_1) ; auto.
  rewrite IHt1_2 with (n:=k) (t2:=t2_2) ; auto.
  rewrite IHt1_1 with (n:=S k) (t2:=t2_1) ; auto.
  rewrite IHt1_2 with (n:=k) (t2:=t2_2) ; auto.
  rewrite IHt1_1 with (n:=S k) (t2:=t2_1) ; auto.
  rewrite IHt1_2 with (n:=k) (t2:=t2_2) ; auto.
Qed.

Lemma open_rec_term_core :forall t j v i u, i <> j -> 
	{j ~> v}t = {i ~> u}({j ~> v}t) -> 
	t = {i ~> u}t.
Proof.
  induction t; introv Neq Equ; simpls; inversion* Equ; fequals*.  
  case_nat*. case_nat*.
Qed.

(** Open a locally closed term is the identity *)
Lemma open_rec_term : forall t u,  term t -> forall k, t = {k ~> u}t.
Proof.
  induction 1; intros; simpl; fequals*; unfolds open ;
  pick_fresh x; apply* (@open_rec_term_core t1 0 (pterm_fvar x)).
Qed.

(** Substitution for a fresh name is identity. *)
Lemma subst_fresh : forall x t u,   x \notin fv t ->  [x ~> u] t = t.
Proof.
  intros. induction t; simpls; fequals*.
  case_var*. 
Qed.

(** Substitution distributes on the open operation. *)
Lemma subst_open_gen : forall x u t1 t2 k, term u -> 
  [x ~> u] ({k ~> t2}t1) = {k ~> ([x ~> u]t2)} ([x ~> u]t1).
Proof.
  intros x u t1 t2 k term_u. gen k.
  induction t1; intros; simpl; fequals*.
  case_nat*. case_var*. apply* open_rec_term.
Qed.

Lemma subst_open : forall x u t1 t2, term u -> 
  [x ~> u] (t1 ^^ t2) = ([x ~> u]t1) ^^ ([x ~> u]t2).
Proof.  intros. apply subst_open_gen. exact H. Qed.

(** Substitution and open_var for distinct names commute. *)
Lemma subst_open_var : forall x y u t, y <> x -> term u ->
  ([x ~> u]t) ^ y = [x ~> u] (t ^ y).
Proof.
  introv Neq Wu. rewrite* subst_open. simpl. case_var*.
Qed.

(** Open up t with a term u is the same as open it with a fresh free variable
   x and then substitute u for x. *)
Lemma subst_intro : forall x t u, 
  x \notin (fv t) -> 
  t ^^ u = [x ~> u](t ^ x).
Proof.
  introv H. unfold open. generalize 0. gen H.
  induction t; simpl; intros; fequals*.
  case_nat*.
  simpl. case_var*.
  case_var*.
Qed.

(** Terms are stable by substitution *)
Lemma subst_term : forall t z u,
  term u -> term t -> term ([z ~> u]t).
Proof.
  induction 2; simpls*.
  case_var*.
  apply_fresh term_abs. rewrite* subst_open_var.
  apply_fresh term_sub. rewrite* subst_open_var. assumption.
Qed.
Hint Resolve subst_term.

(** Every term is a body *)
Lemma term_is_a_body : forall t, term t -> body t.
Proof.
  intros. unfold body. exists {}. intros. unfold open. rewrite <- open_rec_term. auto. auto.
Qed.

(**  Open a body with a term gives a term *)
Lemma body_open_term : forall t u, body t -> term u -> term (t ^^ u).
Proof.
  intros. destruct H. pick_fresh y. rewrite* (@subst_intro y).
Qed.
Hint Resolve body_open_term.

(**  Open a term with a term gives a term *)
Lemma term_open_term : forall t u, term t -> term u -> term (t ^^ u).
Proof. intros.  apply* body_open_term. apply* term_is_a_body. Qed.

(** Conversion from locally closed abstractions and bodies *)
Lemma term_abs_to_body : forall t1, term (pterm_abs t1) -> body t1.
Proof. intros. unfold body. inversion* H. Qed.

Lemma body_to_term_abs : forall t1, body t1 -> term (pterm_abs t1).
Proof. intros. inversion* H. Qed.

Lemma term_sub_to_body : forall t s, term (t[s]) -> body t.
Proof.  intros. unfold body. inversion* H. Qed.

Lemma term_sub_to_term : forall t s, term (t[s]) -> term s.
Proof. intros. inversion* H. Qed.

Lemma body_to_subs : forall t u, body t -> term u -> term (pterm_sub t u).
Proof. intros. inversion* H. Qed.

Lemma subs_to_body : forall t u,  term (pterm_sub t u) -> (body t /\ term u).
Proof. intros. inversion* H. split; trivial. 
       unfold body. exists L. intros x Fr. apply H2; trivial. Qed.

Lemma term_to_subs : forall t u, term t -> term u -> term (pterm_sub t u).
Proof. intros. apply_fresh term_sub. apply term_open_term.  assumption. auto. auto. Qed.

Lemma term_app_to_term_l : forall t1 t2, term (pterm_app t1 t2) -> term t1.
Proof. intros. inversion* H. Qed.

Lemma term_app_to_term_r : forall t1 t2, term (pterm_app t1 t2) -> term t2.
Proof. intros. inversion* H. Qed.

Lemma fvar_body : forall x, body (pterm_fvar x).
Proof. intro. unfold body. exists {}. intros. unfold open. simpl. apply term_var. Qed.

Hint Resolve term_abs_to_body body_to_term_abs term_sub_to_body body_to_subs fvar_body.  
      
Lemma body_distribute_over_application : forall t u, body (pterm_app t u) <-> body t /\ body u.
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
  
Lemma term_abs_term : forall t, term t -> term (pterm_abs t).
Proof.
  intros. apply term_abs with (L:={}). intros. apply term_open_term. assumption. auto.
Qed.

Lemma body_abs : forall t, body t -> body (pterm_abs t).
Proof.
  intros. unfold body. exists {}.
  intros. apply* term_open_term.
Qed.

Lemma close_var_rec_open : forall t x y z i j , i <> j -> x <> y -> y \notin fv t ->
  {i ~> pterm_fvar y}({j ~> pterm_fvar z} (close_rec j x t)) = {j ~> pterm_fvar z}(close_rec j x ({i ~> pterm_fvar y}t)).
Proof.
  induction t; simpl; intros; try solve [ f_equal* ].
  do 2 (case_nat; simpl); try solve [ case_var* | case_nat* ]. 
  case_var*. simpl. case_nat*.
Qed. 
         
Lemma open_close_var : forall x t,  term t -> t = (close t x) ^ x.
Proof.
  introv W. unfold close, open. generalize 0.
  induction W; intros k; simpls; f_equal*.
  case_var*. simpl. case_nat*.
  let L := gather_vars in match goal with |- _ = ?t => 
    destruct (var_fresh (L \u fv t)) as [y Fr] end.
  apply* (@open_var_inj y).
  unfolds open. rewrite* close_var_rec_open. VSD.fsetdec.
  let L := gather_vars in match goal with |- _ = ?t => 
    destruct (var_fresh (L \u fv t)) as [y Fr] end.
  apply* (@open_var_inj y).
  unfolds open. rewrite* close_var_rec_open.  VSD.fsetdec.
Qed. 

Lemma close_var_body : forall x t,  term t -> body (close t x).
Proof.
  introv W. exists {{x}}. intros y Fr.
  unfold open, close. generalize 0. gen y.
  induction W; intros y Fr k; simpls.
  case_var; simpl. case_nat*.
  auto*.
  apply* term_app.
  apply_fresh* term_abs.
    unfolds open. rewrite* close_var_rec_open. VSD.fsetdec.
  apply_fresh* term_sub. unfolds open. rewrite* close_var_rec_open.  VSD.fsetdec.
Qed.

Lemma close_fresh : forall t x k, x \notin fv t -> close_rec k x t = t.
Proof. 
  intros t x k x_notin_t. unfold close. gen k. 
  induction t ; intro k ; simpls* ; try (fequals ; eauto).
    case_var*.
Qed.

Lemma subst_close : forall t x y u, 
    x \notin fv u -> 
    y \notin fv u -> 
    x <> y ->  
[y ~> u] (close t x) = close ([y ~> u]t) x.
Proof.
  intros t x y u x_notin_u y_notin_u x_neq_y.
  unfold close. generalize 0 as k.
  induction t ; intro k ; simpls* ; try (fequals ; eauto). 
    case_var ; simpl ; case_var ; simpls.
      case_var*.
      rewrite* close_fresh.
      case_var*.
Qed.

Lemma subst_as_close_open : forall t x u, term t -> [x ~> u] t = (close t x) ^^ u.
Proof.
  intros t x u term_t. rewrite subst_intro with (x:=x).
  rewrite <- open_close_var with (x:=x) ; auto.
  apply notin_fv_close.
Qed.

(** Auxiliary lemmas. *)

Lemma term_distribute_over_application : forall t u, term (pterm_app t u) <-> term t /\ term u.
Proof.
  split.
    (* -> *)
  intro. split; 
  inversion H; assumption.
  (* <- *)
  intro.
  destruct H.
  apply term_app; assumption.
Qed.

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
Hint Resolve body_open_term.

Lemma not_body_Sn: forall n, ~(body (pterm_bvar (S n))).
Proof.
  intro n.
  intro H. 
  elim H.
  intro L.
  intro H1.
  pick_fresh z.
  assert (z \notin L). auto.
  assert (term (pterm_bvar (S n) ^ z)).
  apply H1.
  assumption.
  inversion H2.
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

Lemma body_to_term: forall t x, x \notin fv t -> body t -> term (t^x).
Proof.
  intros.
  inversion* H0.
Qed.

(*
Lemma term_to_body: forall t x, x \notin fv t -> term (t^x) -> body t.
Proof.
  induction t.
  intros.
  unfold body.  
  simpl in H.
  exists {}.
  intros.
  inversion H0.
  inversion H3.
  unfold open.
 *) 
  
(* ********************************************************************** *)
(** Induction Principles Part 1*)

(* Useful to show the induction principle term_size *)
Lemma peano_induction :
 forall (P:nat->Prop),
   (forall n, (forall m, m < n -> P m) -> P n) ->
   (forall n, P n).
Proof.
  introv H. cuts* K: (forall n m, m < n -> P m).
  induction n; introv Le. inversion Le. apply H.
  intros. apply IHn. omega.
Qed.

Lemma pterm_size_open_var : forall n t x, pterm_size t = pterm_size (open_rec n (pterm_fvar x) t).
Proof.  
  intros n t x.
  generalize n; clear n; induction t.
  (* bvar *)
  intro n'; simpl; case_nat*.
  (* fvar *)
  intro n; simpl; trivial.
  (* app *)
  intro n; simpl; rewrite (IHt1 n); rewrite (IHt2 n); trivial. 
  (* abs *)
  intro n; simpl; rewrite (IHt (S n)); trivial.
  (* sub *)
  intro n; simpl; rewrite (IHt1 (S n)); rewrite (IHt2 n); trivial.
  (* sub' *)
  intro n; simpl; rewrite (IHt1 (S n)); rewrite (IHt2 n); trivial.
Qed.

Lemma pterm_size_induction :
 forall P : pterm -> Prop,
 (forall n, P (pterm_bvar n)) ->
 (forall x, P (pterm_fvar x)) ->
 (forall t1,
    (forall t2 x, x \notin fv t2 -> pterm_size t2 = pterm_size t1 ->
    P (t2 ^ x)) -> P (pterm_abs t1)) ->
 (forall t1 t2, P t1 -> P t2 -> P (pterm_app t1 t2)) ->
 (forall t1 t3, P t3 -> 
    (forall t2 x, x \notin fv t2 -> pterm_size t2 = pterm_size t1 ->
    P (t2 ^ x)) -> P (t1[t3])) ->
  (forall t1 t3, P t3 -> 
    (forall t2 x, x \notin fv t2 -> pterm_size t2 = pterm_size t1 ->
    P (t2 ^ x)) -> P (t1[[t3]])) -> 
 (forall t, P t).
Proof.
  intros P Ha Hb Hc Hd He Hf t.
  gen_eq n: (pterm_size t). gen t.
  induction n using peano_induction.
  introv Eq. subst. destruct t. 
     apply Ha.
     apply Hb.
     (* app *)
     apply~ Hd. apply~ H. simpl; omega. apply~ H. simpl; omega.
     (* abs *)
     apply* Hc.
     introv Fr Eq.
     apply~ H. unfold open. 
     rewrite <- pterm_size_open_var. simpl. omega.
     (* sub *)
     apply* He.
     apply~ H. simpl. omega.
     introv Fr Eq.
     apply~ H. unfold open.
     rewrite <- pterm_size_open_var. simpl. omega.
     (* sub' *)
     apply* Hf.
     apply~ H. simpl. omega.
     introv Fr Eq.
     apply~ H. unfold open.
     rewrite <- pterm_size_open_var. simpl. omega.
Qed.


Lemma pterm_induction :
 forall P : pterm -> Prop,
 (forall n, P (pterm_bvar n)) ->
 (forall x, P (pterm_fvar x)) ->
 (forall t1, P t1 -> forall t2, P t2 -> P (pterm_app t1 t2)) ->
 (forall t1, P (t1) -> P (pterm_abs t1)) ->
 (forall t1, P t1 -> forall t2, P (t2) -> P (t1[t2])) ->
 (forall t1, P t1 -> forall t2, P (t2) -> P (t1[[t2]])) ->
 (forall t, P t).
Proof.
  intros P Hbvar Hfvar Happ Habs Hsub Hsub' t.
  gen t. simple induction t.
  assumption. assumption.
  apply Happ.
  apply Habs.
  apply Hsub.
  apply Hsub'.
Qed.

Fixpoint lc_at (k:nat) (t:pterm) {struct t} : Prop :=
  match t with 
  | pterm_bvar i    => i < k
  | pterm_fvar x    => True
  | pterm_app t1 t2 => lc_at k t1 /\ lc_at k t2
  | pterm_abs t1    => lc_at (S k) t1
  | pterm_sub t1 t2 => (lc_at (S k) t1) /\ lc_at k t2
  | pterm_sub' t1 t2 => False
  end.

Definition term' t := lc_at 0 t.

Definition body' t := lc_at 1 t.

(* ********************************************************************** *)
(** Local closure for Lambda terms, recursively defined *)

Fixpoint Llc_at (k:nat) (t:pterm) {struct t} : Prop :=
  match t with 
  | pterm_bvar i    => i < k
  | pterm_fvar x    => True
  | pterm_app t1 t2 => Llc_at k t1 /\ Llc_at k t2
  | pterm_abs t1    => Llc_at (S k) t1
  | pterm_sub t1 t2 => False
  | pterm_sub' t1 t2 => False
  end.

Definition Lterm' t := Llc_at 0 t.

Definition Lbody' t := Llc_at 1 t.
  
(* ********************************************************************** *)
(** Equivalence of [term and [term'] *)

Lemma lc_rec_open_var_rec : forall x t k,
  lc_at k (open_rec k x t) -> lc_at (S k) t.
Proof.
  induction t; simpl; introv H; auto*.
  case_nat; simpls~.
Qed.

Lemma term_to_term' : forall t,
  term t -> term' t.
Proof.
  introv T. induction T; unfold term'; simple~.
  pick_fresh x. apply~ (@lc_rec_open_var_rec (pterm_fvar x)). apply~ H0.
  split.
  pick_fresh x. apply~ (@lc_rec_open_var_rec (pterm_fvar x)). apply~ H0.
  unfold term' in IHT. assumption.
Qed.

Lemma lc_at_open_var_rec : forall x t k,
  lc_at (S k) t -> lc_at k (open_rec k (pterm_fvar x) t).
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

Lemma term'_to_term : forall t,
  term' t -> term t.
Proof.
  introv. unfold term'.
  apply pterm_size_induction with (t := t).
  (* bvar *)
  simpl. intros. 
  assert (~ n < 0). auto with arith.
  contradiction.
  (* fvar *)
  simpl. intros.
  apply term_var. 
  (* abs *)
  simpl. intros.
  apply term_abs with (L := fv t1).
  intros x Fr.
  apply (H t1); trivial.
  unfold open. 
  apply lc_at_open_var_rec; trivial.
  (* app *)
  intros t1 t2 IHt1 IHt2 H.
  simpl in H. apply term_app.
  apply IHt1; apply H.
  apply IHt2; apply H.
  (* sub *)
  intros. simpl in H1.
  apply term_sub with (L := fv t1).
  intros x Fr.
  apply (H0 t1); trivial.
  unfold open. 
  apply lc_at_open_var_rec. apply H1.
  apply H.  apply H1. 
  (* sub' *)
  intros. simpl in H1. contradiction.
Qed.


Lemma term_eq_term' : forall t, term t <-> term' t.
Proof. intros. split. apply term_to_term'. apply term'_to_term. Qed.


(* ********************************************************************** *)
(** Equivalence of [body] and [body'] *)

Lemma body_to_body' : forall t,
  body t -> body' t.
Proof.
  introv [L H]. pick_fresh x. 
  applys (@lc_rec_open_var_rec (pterm_fvar x)).
  apply term_to_term'. apply~ H.
Qed.

Lemma body'_to_body : forall t,
  body' t -> body t.
Proof.
  introv B. exists ({}:vars). introv F.
  apply term'_to_term. apply~ lc_at_open_var_rec.
Qed.

Lemma body_eq_body' : forall t, body t <-> body' t.
Proof. intros. split. apply body_to_body'. apply body'_to_body. Qed.


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
(** Weakening property of [lc_at] *)

Lemma lc_at_weaken_ind : forall k1 k2 t,
  lc_at k1 t -> k1 <= k2 -> lc_at k2 t.
Proof. introv. gen k1 k2. induction t; simpl; introv T Lt; auto*.
       omega. apply (IHt (S k1) (S k2)); trivial; try omega.
       case T; clear T; intros Tt1 Tt2. split. 
       apply (IHt1 (S k1) (S k2)); trivial; try omega.
       apply (IHt2 k1 k2); trivial; try omega.
Qed. 

Lemma lc_at_weaken : forall k t,
  term' t -> lc_at k t.
Proof. introv H. apply~ (@lc_at_weaken_ind 0). omega. Qed.


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

(* ********************************************************************** *)
(** pterm lists *)

Fixpoint mult_app (t : pterm) (l : list pterm) {struct l} : pterm := 
 match l with 
  | nil => t 
  | u::lv => pterm_app (mult_app t lv) u  
end. 

Notation "t // lu" := (mult_app t lu) (at level 66).

Fixpoint mult_sub (t : pterm) (l : list pterm) {struct l} : pterm := 
 match l with 
  | nil => t 
  | u::lv => (mult_sub t lv)[u]  
end. 

Notation "t // [ lu ]" := (mult_sub t lu) (at level 66).

Fixpoint P_list (P : pterm -> Prop) (l : list pterm) {struct l} : Prop :=
 match l with
 | nil => True
 | t::lu =>  (P t) /\ (P_list P lu) 
 end.

Notation "P %% lu" := (P_list P lu) (at level 66).

Lemma P_list_eq : forall (P : pterm -> Prop) l, (forall u, In u l -> P u) <-> (P %% l).
Proof.
 intros P l. induction l; simpl; split; intros; trivial.
 contradiction. split. apply H. left; trivial.
 apply IHl. intros. apply H. right; trivial.
 destruct H. destruct H0. rewrite <- H0. trivial.
 apply IHl; trivial.
Qed.

(* ********************************************************************** *)
(** SN & NF **)

Inductive NF_ind (R : pterm -> pterm -> Prop): pterm -> Prop :=
 | NF_ind_app : forall x l, (forall u, In u l -> NF_ind R u) -> NF_ind R ((pterm_fvar x) // l)
 | NF_ind_abs : forall t L, (forall x, x \notin L -> NF_ind R (t ^ x)) ->  NF_ind R (pterm_abs t).

Inductive SN_ind (n : nat) (R : pterm -> pterm -> Prop) (t : pterm) : Prop :=
 | SN_intro : (forall t', R t t' -> exists k, k < n /\ SN_ind k R t') -> SN_ind n R t.

Definition SN (R : pterm -> pterm -> Prop) (t : pterm) := exists n, SN_ind n R t.
Definition NF (R : pterm -> pterm -> Prop) (t : pterm) := forall t', ~ R t t'.

Lemma mult_app_append : forall t1 t2 l, pterm_app t1 t2 // l = t1 // l ++ (t2 :: nil).
Proof.
 intros. induction l; simpl; trivial.
 rewrite IHl. trivial.
Qed.

Lemma mult_app_append' : forall t1 t2 l l', pterm_app (t1 // l') t2 // l = t1 // l ++ (t2 :: l').
Proof.
 intros. generalize t1 t2 l; clear t1 t2 l. induction l'; intros.
 simpl; apply mult_app_append.
 replace (l ++ t2 :: a :: l') with ((l ++ (t2 :: nil)) ++ (a :: l')). rewrite <- IHl'  .
 simpl. rewrite mult_app_append. trivial.
 rewrite <- app_assoc. simpl.
 trivial.
Qed.

Lemma P_list_append : forall P l1 l2, P_list P (l1 ++ l2) <-> ((P_list P l1) /\ (P_list P l2)).
Proof.
 intros. induction l1; simpl.
 split. intro H.  split; trivial.
 intro H. destruct H; trivial.
 split. intro H. split. split.
 apply H. apply IHl1. apply H.
 apply IHl1. apply H.
 intro H. split. apply H.
 apply IHl1. split; apply H.
Qed.

Lemma eqdec_nil : forall A (l: list A), (l = nil) \/ (l <> nil).
Proof.
 intros A l. induction l.
 left; trivial. right; discriminate.
Qed.

Lemma m_app_eq_app : forall t lu, lu <> nil -> 
exists t', exists u', t // lu = pterm_app t' u'.
Proof.
 intros. destruct lu. apply False_ind. apply H; trivial.
 simpl. exists (t // lu). exists p. trivial.
Qed.

Lemma not_nil_append : forall A (l: list A), l <> nil -> 
 exists a, exists l', l = l' ++ (a :: nil).
Proof.
 intros. induction l. apply False_ind. apply H; trivial.
 case eqdec_nil with (l := l). intro H'. rewrite H'.
 exists a. exists (nil (A := A)). simpl; trivial.
 intro H'. case IHl; trivial; clear IHl.
 intros a' H0. case H0; clear H0.
 intros l' H0. rewrite H0. 
 exists a'. exists (a :: l'). simpl.
 trivial.
Qed.

(** mult_app injectivity **)

Lemma mult_app_inj_l : forall t t' l, t // l = t' // l -> t = t'.
Proof.
 intros t t' l H. induction l;
 simpl in *|-*; inversion H; try apply IHl; trivial.
Qed.

Lemma mult_app_inj_r : forall t0 t t' l l', t0 // (l ++ (t :: l')) = t0 // (l ++ (t':: l')) -> t = t'.
Proof. 
 intros t0 t t' l l' H. 
 rewrite <- mult_app_append' in H. rewrite <- mult_app_append' in H.
 apply mult_app_inj_l in H. inversion H. trivial.
Qed.

Lemma mult_app_inj_r'_aux : forall t l, t = t // l -> l = nil.
Proof.
 intro t. induction t; intros; destruct l; trivial; simpl in H;
 try inversion H. rewrite mult_app_append in H1.
 apply IHt1 in H1. apply False_ind. clear t1 p IHt1 IHt2 H H2. 
 case eqdec_nil with (l := l); intros.
 rewrite H in H1. simpl in H1. inversion H1.
 apply app_eq_nil in H1. destruct H1.
 contradiction.
Qed. 

Lemma mult_app_inj_r' : forall t l l', t // l = t // l' -> l = l'.
Proof.
 intros t l. generalize t; clear t. induction l; intros.
 simpl in H. apply mult_app_inj_r'_aux in H. rewrite H. trivial. 
 destruct l'. replace (t // nil) with t in H.
 assert (Q : a :: l = nil). apply mult_app_inj_r'_aux with (t := t). rewrite H; trivial. 
 trivial. simpl. trivial.
 simpl in H. inversion H. apply IHl in H1.
 rewrite H1. trivial.
Qed.

Lemma mult_app_inj_aux : forall l t t', t = t' // l -> ((t = t' /\ l = nil) \/ 
(exists l', exists u, l = l' ++ (u :: nil))).
Proof. 
 intro l. induction l; simpl; intros.
 left; split; trivial. destruct t; try inversion H.
 apply IHl in H1. 
 right. destruct H1. destruct H0. rewrite H1.
 simpl. exists (nil (A := pterm)) a. 
 simpl; split; trivial.
 case H0; clear H0; intros l0 H0.
 case H0; clear H0; intros u0 H0. 
 rewrite H0. exists (a :: l0) u0. 
 simpl. trivial.
Qed. 

Lemma length_0 : forall (A : Set) (l : list A), 0 = length l -> l = nil.
Proof.
  intros. induction l; trivial.
  simpl in H. inversion H.
Qed.

Lemma mult_app_eq_length_inj : forall t t' l l', (length l) = (length l') -> 
t // l = t' // l' -> t = t' /\ l = l'.
Proof. 
  intros. generalize t t' l' H H0.  clear t t' l' H H0. induction l; simpl; intros.
  apply length_0 in H. rewrite H in *|-*. simpl in H0. split; trivial.
  destruct l'; simpl in H. inversion H.
  simpl in H0. inversion H0. apply IHl in H2.
  destruct H2. rewrite H1. rewrite H2. split; trivial.
  omega.
Qed.

Lemma mult_app_var_inj : forall l l' x x', 
                         (pterm_fvar x) // l = (pterm_fvar x') // l' -> (x = x' /\ l = l'). 
Proof. 
  intro l. induction l; intros; destruct l'; simpl in H; inversion H. 
  split; trivial. apply IHl in H1. destruct H1. rewrite H1. 
  split; trivial.
Qed.

Lemma mult_app_diff_var_abs : forall l l' x t, 
                            (pterm_fvar x) // l <> (pterm_abs t) // l'. 
Proof. 
  intros l. induction l; destruct l'; simpl in *|-*; try discriminate.
  intros. intro H. inversion H. generalize H1.
  apply IHl.
Qed.

Lemma mult_app_diff_var_sub : forall l l' x t u, 
                            (pterm_fvar x) // l <> (t[u]) // l'. 
Proof. 
  intros l. induction l; destruct l'; simpl in *|-*; try discriminate.
  intros. intro H. inversion H. generalize H1.
  apply IHl.
Qed.

Lemma mult_app_abs_inj : forall l l' t t', 
                         (pterm_abs t) // l = (pterm_abs t') // l' -> (t = t' /\ l = l'). 
Proof. 
  intro l. induction l; intros; destruct l'; simpl in H; inversion H. 
  split; trivial. apply IHl in H1. destruct H1. rewrite H1. 
  split; trivial.
Qed.

Lemma mult_app_diff_abs_sub : forall l l' t u v, 
                            (pterm_abs t) // l <> (u[v]) // l'. 
Proof. 
  intros l. induction l; destruct l'; simpl in *|-*; try discriminate.
  intros. intro H. inversion H. generalize H1.
  apply IHl.
Qed.

Lemma mult_app_sub_inj : forall l l' t u t' u', 
                         (t[u]) // l = (t'[u']) // l' -> (t = t' /\ u = u' /\ l = l'). 
Proof. 
  intro l. induction l; intros; destruct l'; simpl in H; inversion H.
  split; trivial. split; trivial. apply IHl in H1. destruct H1. destruct H1. 
  rewrite H0. rewrite H1. rewrite H3. 
  split; trivial. split; trivial.
Qed.


Lemma app_singleton : forall l (t : pterm) l1 l2,
 l <> nil -> l1 ++ (t :: nil) = l2 ++ l -> exists l', l = l' ++ (t :: nil).
Proof.
  induction l; simpl; intros. apply False_ind. apply H; trivial.
  case eqdec_nil with (l := l). intro H1. rewrite H1 in *|-*.
  apply app_inj_tail in H0. destruct H0. rewrite H2. 
  exists (nil (A := pterm)). simpl. trivial.
  intro H1. case IHl with  (t := t) (l1 := l1) (l2 := l2 ++ a :: nil); trivial. 
  rewrite H0. rewrite <- app_assoc; simpl; trivial.
  intros l' H2. rewrite H2. exists (a :: l'). simpl. trivial.
Qed.  

Lemma geq_app_list : forall (l4 l1 l2 l3 : list pterm), l1 ++ l2 = l3 ++ l4 ->
  length l2 > length l4 -> (exists l, l2 = l ++ l4 /\ l3 = l1 ++ l).
Proof.
 intro l4. induction l4; simpl; destruct l2; intros. 
 simpl in H0. assert (~ 0 > 0). auto with arith. contradiction.
 exists (p :: l2). simpl.
 rewrite app_nil_r in *|-*. rewrite H. split; trivial. simpl in H0. 
 assert (~ 0 > S (length l4)). auto with arith. contradiction.
 simpl in H0. case IHl4 with (l1 := l1 ++ (p::nil)) (l2 := l2) (l3 := l3 ++ (a::nil)). 
 rewrite <- app_assoc. rewrite <- app_assoc. simpl. trivial. omega.
 clear IHl4; intros l H1. destruct H1. rewrite H1. rewrite <- app_assoc in H2. simpl in H2.
 case eqdec_nil with (l := l). intro H4.
 rewrite H4 in H2. apply app_inj_tail in H2. destruct H2. 
 rewrite H2. rewrite H3. rewrite H4. exists (nil (A := pterm)).
 rewrite app_nil_l. rewrite app_nil_l. rewrite app_nil_r. split; trivial.
 replace (l1 ++ p :: l) with ((l1 ++ p :: nil) ++ l) in H2.
 intros. generalize H2. intro H4. apply app_singleton in H4; trivial.
 case H4; clear H4; intros l' H4. rewrite H4. rewrite H4 in H2. exists (p :: l'); split.
 simpl. rewrite <- app_assoc. simpl. trivial. simpl in H2.
 replace ((l1 ++ p :: nil) ++ l' ++ a :: nil) with ((l1 ++ p :: l') ++ a :: nil) in H2.
 apply app_inj_tail in H2. destruct H2; trivial.
 rewrite <- app_assoc. rewrite <- app_assoc; simpl; trivial.
 rewrite <- app_assoc; simpl; trivial. 
Qed.

Lemma P_eq_app_list : forall (P: pterm -> Prop) t1 t2 l1 l2 l3 l4,
  P %% l2 -> P %% l4 -> ~ P t1 -> ~ P t2 -> l1 ++ t1 :: l2 = l3 ++ t2 :: l4 ->
  (l1 = l3 /\ t1 = t2 /\ l2 = l4).
Proof.
 intros. case (length l2 == length l4).

 intro H4. gen_eq l2' : (t1 :: l2). gen_eq l4' : (t2 :: l4). intros H5 H6. 
 assert (H7 : length l2' = length l4'). 
   rewrite H5. rewrite H6. simpl. rewrite H4. trivial.
 clear H H0 H1 H2 H4.
 assert (H8 : length l1 = length l3).
  assert (Q : length (l1 ++ l2') = length l1 + length l2').
    rewrite app_length; trivial.
  assert (Q' : length (l3 ++ l4') = length l3 + length l4').
    rewrite app_length; trivial.
  rewrite H3 in Q. rewrite Q in Q'. rewrite H7 in Q'.
  omega.
 assert (H9: l1 = l3).
  clear H5 H6 H7. generalize l3 l2' l4' H3 H8; clear t1 t2 l2' l2 l3 l4 l4' H3 H8.
  induction l1; simpl; intros.
  apply length_0 in H8. rewrite H8; trivial.
  destruct l3. simpl in H8. inversion H8.
  simpl in H3. inversion H3. fequals. simpl in H8.
  apply IHl1 with (l2' := l2') (l4' := l4'); try omega; trivial.
  split; trivial. rewrite H9 in H3.
  apply app_inv_head in H3. rewrite H5 in H3. rewrite H6 in H3.
  inversion H3. split; trivial.

  intro H4.
  assert (Q : length l2 > length l4 \/ length l4 > length l2).
    clear H H0 H1 H2 H3. generalize l4 H4; clear l1 l3 l4 H4. 
    induction l2; destruct l4; simpl; intros; try omega.
    apply False_ind. apply H4; trivial. 
     assert (Q'' : length l2 > length l4 \/ length l4 > length l2).       
       apply IHl2; try omega. intro H5. apply H4. rewrite H5; trivial. 
     destruct Q''. left. omega. right. omega.
  clear H4. destruct Q. 
  apply geq_app_list with (l1 := l1 ++ (t1 :: nil)) (l3 := l3 ++ (t2 :: nil)) in H4; trivial.
  case H4; clear H4. intros l H4. destruct H4. case eqdec_nil with (l := l). intro H6.
  rewrite H6 in H5. rewrite app_nil_r in H5. apply app_inj_tail in H5. destruct H5.
  rewrite H6 in H4. simpl in H4. rewrite H5. rewrite H7. split; trivial. split; trivial.
  intro H6.  apply app_singleton in H5; trivial. case H5; clear H5; intros l' H5.
  assert (Q : In t2 l2). rewrite H4. rewrite H5. apply in_or_app. left. apply in_or_app. right.
    simpl. left; trivial.
  rewrite <- P_list_eq in H. apply H in Q. contradiction.
  rewrite <- app_assoc. rewrite <- app_assoc; simpl; trivial.
  symmetry in H3. 
  apply geq_app_list with (l3 := l1 ++ (t1 :: nil)) (l1 := l3 ++ (t2 :: nil)) in H4; trivial.
  case H4; clear H4. intros l H4. destruct H4. case eqdec_nil with (l := l). intro H6.
  rewrite H6 in H5. rewrite app_nil_r in H5. apply app_inj_tail in H5. destruct H5.
  rewrite H6 in H4. simpl in H4. rewrite H5. rewrite H7. rewrite H4. split; trivial. split; trivial.
  intro H6.  apply app_singleton in H5; trivial. case H5; clear H5; intros l' H5.
  assert (Q : In t1 l4). rewrite H4. rewrite H5. apply in_or_app. left. apply in_or_app. right.
    simpl. left; trivial.
  rewrite <- P_list_eq in H0. apply H0 in Q. contradiction.
  rewrite <- app_assoc. rewrite <- app_assoc; simpl; trivial.
Qed.  


(** maybe realocate  end *)


(* ********************************************************************** *)
(** Induction Principles Part 2 *)

(* A home made induction principle based on the size of the terms *)
Lemma term_size_induction :
 forall P : pterm -> Prop,
 (forall x, P (pterm_fvar x)) ->
 (forall t1,
    body t1 ->
    (forall t2 x, x \notin fv t2 -> pterm_size t2 = pterm_size t1 ->
      term (t2 ^ x) -> P (t2 ^ x)) ->
    P (pterm_abs t1)) ->
 (forall t1 t2,
    term t1 -> P t1 -> term t2 -> P t2 -> P (pterm_app t1 t2)) ->
(forall t1 t3,
    term t3 -> P t3 -> body t1 -> 
    (forall t2 x, x \notin fv t2 -> pterm_size t2 = pterm_size t1 ->
      term (t2 ^ x) -> P (t2 ^ x)) ->
    P (t1[t3])) ->
 (forall t, term t -> P t).
Proof.
  intros P Ha Hb Hc Hd t.
  gen_eq n: (pterm_size t). gen t.
  induction n using peano_induction.
  introv Eq T. subst. inverts T. 
     apply Ha.
     (* app *)
     apply~ Hc. apply~ H. simpl; omega. apply~ H. simpl; omega.
     (* abs *)
     apply* Hb.
       introv Fr Eq T.
       apply~ H. unfold open.
      rewrite <- pterm_size_open_var. simpl. omega.
     (* sub *)
     apply* Hd.
       apply~ H. simpl; omega.
       introv Fr Eq T.  apply~ H.  unfold open.
       rewrite <- pterm_size_open_var. simpl. omega.
Qed.

(** Tentativa de princípio de indução mais intuitivo *)
(*
Lemma term_induction :
  forall P : pterm -> Prop,
    (forall x, term x ->
       (forall y, term y -> pterm_size y < pterm_size x -> P y -> P x)) ->
    (forall t, term t -> P t).
Proof.
  intros P Hind t Ht.
  destruct t.
  inversion Ht.
  apply Hind with (y := pterm_fvar v). assumption.
  intros y Hy Hsize.
  inversion Hsize.
  apply  term_size_non_null in Hy.
  rewrite H0 in Hy.
  apply False_ind.
  apply (lt_irrefl 0).
  assumption.
  apply  term_size_non_null in Hy.
  apply le_Sn_le in H0.
  absurd (pterm_size y > 0).
  apply le_not_gt in H0; assumption. assumption.
  inversion Ht.
  apply Hind. assumption.
  intros.
  *)
Lemma body_size_induction :
 forall P : pterm -> Prop,
 (P (pterm_bvar 0)) ->
 (forall x, P (pterm_fvar x)) ->
 (forall t1, (lc_at 2 t1) ->
    (forall t2 x, x \notin fv t2 -> pterm_size t2 = pterm_size t1 ->
    body (open_rec 1 (pterm_fvar x) t2) -> P (open_rec 1 (pterm_fvar x) t2)) -> P (pterm_abs t1)) ->
 (forall t1 t2, body t1 -> body t2 -> P t1 -> P t2 -> P (pterm_app t1 t2)) ->
 (forall t1 t3, (lc_at 2 t1) -> body t3 -> P t3 -> 
    (forall t2 x, x \notin fv t2 -> pterm_size t2 = pterm_size t1 ->
    body (open_rec 1 (pterm_fvar x) t2) -> P (open_rec 1 (pterm_fvar x) t2)) -> P (t1[t3])) -> 
 (forall t, body t -> P t).
Proof.
  intros P Ha Hb Hc Hd He t.
  gen_eq n: (pterm_size t). gen t.
  induction n using peano_induction.
  introv Eq B. subst. destruct t. 
     (* bvar *)
     generalize B; clear B; case n.
     intro B; apply Ha.
     intros n' H'; apply not_body_Sn in H'; contradiction.
     (* fvar *)
     apply Hb.
     (* app *)
     apply~ Hd;
     apply body_distribute_over_application in B.
     apply B. apply B.
     apply~ H. simpl; omega. 
     apply B. apply~ H. simpl; omega.
     apply B.
     (* abs *)
     apply* Hc.
     apply body_to_body' in B.
     unfold body' in B. simpl in B; trivial.
     introv Fr Eq.
     apply~ H. rewrite <- pterm_size_open_var. simpl. omega.
     (* sub *)
     apply body_to_body' in B.
     unfold body' in B. simpl in B.
     apply* He. apply body'_to_body.
     unfold body'. apply B.
     apply~ H. simpl. omega.
     apply body'_to_body.
     unfold body'. apply B.
     introv Fr Eq.
     apply~ H. rewrite <- pterm_size_open_var. simpl. omega.
     (* sub' *)
     apply body_to_body' in B. unfold body' in B. simpl in B.
     contradiction.
Qed.

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

Lemma term_size_induction2 :
 forall P : pterm -> Prop,
 (forall x l, (forall u, In u l -> (term u /\ P u)) -> P ((pterm_fvar x) // l)) ->
 (forall t1 l, (forall u, In u l -> (term u /\ P u)) -> body t1 ->
  (forall t2 x, x \notin fv t2 -> pterm_size t2 = pterm_size t1 -> term (t2 ^ x) -> P (t2 ^ x)) ->
      P ((pterm_abs t1) // l)) ->
(forall t1 t3 l,
    (forall u, In u l -> (term u /\ P u)) -> term t3 -> P t3 -> body t1 -> 
    (forall t2 x, x \notin fv t2 -> pterm_size t2 = pterm_size t1 -> term (t2 ^ x) -> P (t2 ^ x)) ->
    P ((pterm_sub t1 t3) // l) ) ->
 (forall l t, (forall u, In u l -> (term u /\ P u)) -> term t -> P (t // l)).
Proof.
 intros. generalize H3.  intro T. generalize l H2 H3. clear l H2 H3.
 apply term_size_induction with (t := t); trivial; intros.
 apply H; trivial.
 apply H0; trivial; intros.
 assert (Q : P (t2 ^ x // nil)).
   apply H3; simpl; trivial; intros. contradiction.
 simpl in Q. trivial.
 replace (pterm_app t1 t2 // l) with (t1 // l ++ (t2 :: nil)).  
 apply H3. intros. apply in_app_iff in H8. destruct H8.
 apply H6; trivial. simpl in H8. destruct H8; try contradiction.
 rewrite <- H8. clear H8. apply term_distribute_over_application in H7.
 destruct H7. split; trivial.
 assert (Q : P (t2 // nil)). 
   apply H5; simpl; trivial; intros. contradiction. 
 simpl in Q. trivial. trivial. 
 rewrite mult_app_append. trivial.
 apply H1; trivial.
 assert (Q : P (t3 // nil)).
   apply H3; simpl; trivial; intros. contradiction.
 simpl in Q. trivial.
 intros.
 assert (Q : P (t2 ^ x // nil)).
   apply H5; simpl; trivial; intros. contradiction.
 simpl in Q. trivial.
Qed.

Lemma term_size_induction3 :
 forall P : pterm -> Prop,
 (forall x l, (forall u, In u l -> (term u /\ P u)) -> P ((pterm_fvar x) // l)) ->
 (forall t1 l, (forall u, In u l -> (term u /\ P u)) -> body t1 ->
  (forall t2 x, x \notin fv t2 -> pterm_size t2 = pterm_size t1 -> term (t2 ^ x) -> P (t2 ^ x)) ->
      P ((pterm_abs t1) // l)) ->
(forall t1 t3 l,
    (forall u, In u l -> (term u /\ P u)) -> term t3 -> P t3 -> body t1 -> 
    (forall t2 x, x \notin fv t2 -> pterm_size t2 = pterm_size t1 -> term (t2 ^ x) -> P (t2 ^ x)) ->
    P ((pterm_sub t1 t3) // l) ) ->
 (forall t, term t -> P t).
Proof. 
 intros. replace t with (t // nil).
 apply term_size_induction2; simpl; trivial.
 intros; contradiction. 
 simpl. trivial.
Qed.

(* A home made induction principle based on the size of the terms *)
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




(* ******************************* *)
(** * Tactics depending on lemmas  *)
Ltac remove_dupterms :=
try match goal with
| H1 : term ?t,
  H2 : term ?t |- _ => clear H2
| H1 : body ?t,
  H2 : body ?t |- _ => clear H2
end.

(** Definitions for solver tactics *)
Hint Resolve 
    term_var 
    term_app 
    body_open_term 
    term_open_term 
    body_to_term_abs
    body_to_subs 
    term_to_subs 
    term_abs_term
    close_var_body : term_building_db.

(** Extracts all the information about what is a term in the context (one step) *)
Ltac term_extractor H :=
try(
  match (type of H) with
  | term (pterm_app ?u ?u') =>
        let tmp := fresh H in
        duplicate H tmp;
        apply term_app_to_term_l in tmp ; term_extractor tmp;
        apply term_app_to_term_r in H ; term_extractor H
  | term (pterm_sub ?t ?u) => 
        let tmp := fresh H in
        duplicate H tmp;
        apply term_sub_to_term in tmp ; term_extractor tmp;
        apply term_sub_to_body in H ; term_extractor H
  | term (pterm_abs ?t) =>
        apply term_abs_to_body in H ; term_extractor H
  |_ => generalize H ; clear H
  end).


(** Extracts all the information about what is a term in the context (many step) *)
Ltac saturate_term :=
try(
  match goal with
  | H : term _ |- _ => term_extractor H ; saturate_term
end).

(* ********************************************************************** *)
(** About the interations between open, close, fvar, swap and bswap *)

Lemma swap_id : forall x t, [(x,x)]t = t.
Proof.
 intros. induction t; simpl; trivial.
 case (v == x). intro. rewrite e. trivial. intro; trivial.
 rewrite IHt1. rewrite IHt2. trivial.
 rewrite IHt. trivial.
 rewrite IHt1. rewrite IHt2. trivial.
 rewrite IHt1. rewrite IHt2. trivial.
Qed.

Lemma swap_fresh : forall x y t, x \notin (fv t) -> y \notin (fv t) -> [(x,y)]t = t.
Proof. 
 intros. induction t; simpl in *|-*; trivial. 
 apply notin_singleton in H. apply notin_singleton in H0.
 assert (Q : v <> x). intro. apply H. rewrite H1; trivial.
 assert (Q': v <> y). intro. apply H0. rewrite H1; trivial. clear H H0.
 case (v == x); case (v == y); intros; try contradiction; trivial.
 apply notin_union in H. destruct H. apply notin_union in H0. destruct H0.
 rewrite IHt1; try rewrite IHt2; trivial. 
 rewrite IHt; trivial.
 apply notin_union in H. destruct H. apply notin_union in H0. destruct H0.
 rewrite IHt1; try rewrite IHt2; trivial. 
 apply notin_union in H. destruct H. apply notin_union in H0. destruct H0.
 rewrite IHt1; try rewrite IHt2; trivial. 
Qed.

Lemma swap_inv : forall x y t, [(x,y)]([(x,y)]t) = t.
Proof.
 intros. induction t; simpl; trivial.
 case (v == x); intros; simpl. case (y == x); case (y == y); intros.
 rewrite e; rewrite e1; trivial. apply False_ind; apply n; trivial.
 rewrite e; trivial. apply False_ind; apply n; trivial.
 case (v == y); intros; simpl. case (x == x); case (x == y); intros.
 rewrite e; trivial. rewrite e; trivial. apply False_ind; apply n0; trivial.
 apply False_ind; apply n1; trivial. case (v == x); case (v == y); intros; try contradiction; trivial.
 rewrite IHt1; rewrite IHt2; trivial. rewrite IHt; trivial.
 rewrite IHt1; rewrite IHt2; trivial. rewrite IHt1; rewrite IHt2; trivial.
Qed.

Lemma swap_var_id : forall x y z, z <> x -> z <> y -> [(x,y)](pterm_fvar z) = pterm_fvar z.
Proof. 
  intros. rewrite swap_fresh; simpl; try apply notin_singleton; trivial. 
  intro. apply H. rewrite H1; trivial.
  intro. apply H0. rewrite H1; trivial.
Qed.

Lemma swap_sym : forall x y t, [(x,y)]t = [(y,x)]t.
Proof.
 intros x y t. induction t; simpl in *|-*; trivial.
 case (v == x); case (v == y); intros H H'; trivial.
 rewrite <- H; rewrite <- H'; trivial. 
 rewrite IHt1; rewrite IHt2; trivial.
 rewrite IHt; trivial.
 rewrite IHt1; rewrite IHt2; trivial.
 rewrite IHt1; rewrite IHt2; trivial.
Qed.


Lemma swap_var_l : forall x y, [(x,y)](pterm_fvar x) = pterm_fvar y.
Proof. 
  intros; simpl. case (x == x); case (x == y); intros; trivial.
  rewrite e; trivial. apply False_ind. apply n0; trivial.
Qed.

Lemma swap_var_r : forall x y, [(x,y)](pterm_fvar y) = pterm_fvar x.
Proof. 
  intros. rewrite swap_sym. apply swap_var_l.
Qed.

Lemma swap_eq_subst : forall (x y z : var) t, z <> x -> z <> y -> z \notin (fv t) ->  
      subst z (pterm_fvar y) ((subst y (pterm_fvar x) (subst x (pterm_fvar z) t))) = [(x,y)] t.
Proof.
 intros. induction t.
 simpl; trivial. simpl in H. apply notin_singleton in H1.
 simpl. case (v == x); simpl. case (z == y); simpl. case (x == z); simpl; trivial.
 intros. contradiction. case (z == z); intros; trivial. apply False_ind. apply n; trivial. 
 case (v == y); simpl. case (x == z); intros; trivial. apply False_ind. apply H. rewrite e; trivial.
 case (v == z); intros; trivial. apply False_ind. apply H1. rewrite e; trivial.
 simpl in H1|-*. apply notin_union in H1. destruct H1.
 rewrite IHt1; trivial. rewrite IHt2; trivial.
 simpl in H1|-*. rewrite IHt; trivial.
 simpl in H1|-*. apply notin_union in H1. destruct H1.
 rewrite IHt1; trivial. rewrite IHt2; trivial.
 simpl in H1|-*. apply notin_union in H1. destruct H1.
 rewrite IHt1; trivial. rewrite IHt2; trivial.
Qed.


Lemma open_swap_comm : forall x y z t n, 
                       [(x,y)]({n ~> pterm_fvar z}t) = {n ~> ([(x,y)]pterm_fvar z)}([(x,y)]t).
Proof.
 intros x y z t. induction t; intros; simpl.
 case (n0 === n); simpl; intros; trivial. 
 case (v == x); case (v == y); case (z == x); case (z == y); intros; trivial.
 rewrite IHt1. rewrite IHt2. trivial.
 rewrite IHt; trivial.
 rewrite IHt1. rewrite IHt2. trivial.
 rewrite IHt1. rewrite IHt2. trivial.
Qed.

Lemma open_swap : forall (x y z : var) t, z <> x -> z <> y -> ([(x,y)]t)^z = [(x,y)]t^z.
Proof. intros. unfold open. rewrite open_swap_comm. rewrite swap_var_id; trivial. Qed.

Lemma subst_fvar: forall x u, [x ~> u](pterm_fvar x) = u. 
Proof. intros. simpl. case (x == x); intros; trivial. apply False_ind. apply n; trivial. Qed.

Lemma swap_eq_open : forall (x y : var) t, x \notin (fv t) -> y \notin (fv t) ->
        ({1 ~> pterm_fvar y}({0 ~> pterm_fvar x}t)) = 
[(x,y)] ({1 ~> pterm_fvar x}({0 ~> pterm_fvar y}t)).
Proof.
 intros. case (x == y). intro. rewrite e. rewrite swap_id. trivial.
 intro H1. pick_fresh z. 
 apply notin_union in Fr. destruct Fr. apply notin_union in H2. destruct H2.
 apply notin_singleton in H2. apply notin_singleton in H4.
 rewrite <- swap_eq_subst with (z := z); trivial.
 repeat rewrite subst_open_gen; trivial.  
 replace  ([z ~> pterm_fvar y]([y ~> pterm_fvar x]([x ~> pterm_fvar z]t))) with t.
 replace ([x ~> pterm_fvar z]pterm_fvar y) with (pterm_fvar y).
 replace ([y ~> pterm_fvar x]pterm_fvar y) with (pterm_fvar x).
 replace ([z ~> pterm_fvar y]pterm_fvar x) with (pterm_fvar x).
 replace ([x ~> pterm_fvar z]pterm_fvar x) with (pterm_fvar z).
 replace ([y ~> pterm_fvar x]pterm_fvar z) with (pterm_fvar z).
 replace ([z ~> pterm_fvar y]pterm_fvar z) with (pterm_fvar y); trivial.   
 rewrite subst_fvar; trivial. rewrite subst_fresh; simpl; trivial.
 apply notin_singleton. intro. apply H4. rewrite H5; trivial.
 rewrite subst_fvar; trivial. rewrite subst_fresh; simpl; trivial.
 apply notin_singleton; trivial. rewrite subst_fvar; trivial.
 rewrite subst_fresh; simpl; trivial. apply notin_singleton; trivial.
 repeat rewrite subst_fresh; simpl; trivial.
 repeat rewrite fv_open_; trivial. 
Qed.

Lemma swap_term : forall x y t, term t -> term ([(x,y)]t).
Proof. 
 intros. induction H; simpl.
 case (x0 == x); case (x0 ==y); intros; trivial.
 apply term_app; trivial.
 apply term_abs with (L := L \u {{x}} \u {{y}}). intros z Hz.
 apply notin_union in Hz. destruct Hz. apply notin_union in H1. destruct H1.
 apply notin_singleton in H2. apply notin_singleton in H3.
 rewrite open_swap; trivial. apply H0; trivial.
 apply term_sub with (L := L \u {{x}} \u {{y}}); trivial. intros z Hz.
 apply notin_union in Hz. destruct Hz. apply notin_union in H2. destruct H2.
 apply notin_singleton in H3. apply notin_singleton in H4.
 rewrite open_swap; trivial. apply H0; trivial.
Qed.

Lemma swap_fvar : forall x y S t, x \in S -> y \in S -> fv t << S -> fv ([(x,y)]t) << S.
Proof. 
 intros. induction t; simpl.
 apply subset_empty_l. case (v == x); case (v == y); simpl; intros; trivial;
 apply subset_singleton; trivial.
 simpl in H1. rewrite subset_union_l in *|-*. destruct H1.
 split; [apply IHt1; trivial | apply IHt2; trivial].
 simpl in H1. apply IHt; trivial.
 simpl in H1. rewrite subset_union_l in *|-*. destruct H1.
 split; [apply IHt1; trivial | apply IHt2; trivial].
 simpl in H1. rewrite subset_union_l in *|-*. destruct H1.
 split; [apply IHt1; trivial | apply IHt2; trivial].
Qed.

Lemma fv_subset_swap : forall x y t L, fv t << L -> fv ([(x, y)]t) << L \u {{x}} \u {{y}}.
Proof.
 intros x y t L H. unfold VarSet.Subset in *|-*.
 intros z Hz. apply in_union. case (z == y). 
 intro H'. right. apply in_singleton; trivial.
 intro H'. left. apply in_union. case (z == x).
 intro H''. right. apply in_singleton; trivial.
 intro H''. left. apply H. clear H. induction t; simpl in *|-*; trivial.
 generalize Hz; clear Hz. case (v == x); case (v == y); simpl; 
 intros H H0 H1; try rewrite in_singleton in *|-*; try contradiction; trivial.
 try rewrite in_union in *|-*. destruct Hz.
 left; apply IHt1; trivial. right; apply IHt2; trivial. 
 apply IHt; trivial.
 try rewrite in_union in *|-*. destruct Hz.
 left; apply IHt1; trivial. right; apply IHt2; trivial. 
 try rewrite in_union in *|-*. destruct Hz.
 left; apply IHt1; trivial. right; apply IHt2; trivial. 
Qed.


Lemma fv_swap : forall x y t, y \notin fv t -> [(x,y)]t = [x ~> pterm_fvar y]t.
Proof.
 intros x y t H. induction t; simpl in *|-*; trivial.
 case (v == y);  intro H'. apply notin_singleton in H. apply False_ind.
 apply H; rewrite H'; trivial. case (v == x); intros; trivial.
 apply notin_union in H. destruct H. rewrite IHt1; try rewrite IHt2; trivial.
 rewrite IHt; trivial.
 apply notin_union in H. destruct H. rewrite IHt1; try rewrite IHt2; trivial.  
 apply notin_union in H. destruct H. rewrite IHt1; try rewrite IHt2; trivial.
Qed.

Lemma bswap_swap_comm : forall x y t n, [(x,y)](bswap_rec n t) = bswap_rec n ([(x,y)]t).
Proof.
 intros x y t; induction t; intros.
 unfold swap. fold swap. unfold bswap_rec. 
 case (n0 === n); case (S n0 === n); intros; simpl; trivial.
 unfold bswap_rec. fold bswap_rec. unfold swap. 
 case (v == x); case (v == y); intros; simpl; trivial.
 simpl. rewrite IHt1; rewrite IHt2; trivial. 
 simpl. rewrite IHt; trivial.
 simpl. rewrite IHt1; rewrite IHt2; trivial. 
 simpl. rewrite IHt1; rewrite IHt2; trivial. 
Qed.

Lemma bswap_eq_openclose : forall n x y t, x \notin (fv t) -> y \notin (fv t \u {{x}}) ->
 (close_rec (S n) x (close_rec n y (open_rec (S n) (pterm_fvar y) (open_rec n (pterm_fvar x) t)))) =
 bswap_rec n t. 
Proof.
 intros. apply notin_union in H0. destruct H0. apply notin_singleton in H1.
 generalize n; clear n. induction t; intros.
 unfolds bswap_rec. unfolds open_rec. unfolds close_rec. case (n0 === n); intros.
 case (x == y); intros. symmetry in e0. contradiction.
 case (x == x); intros; trivial. apply False_ind. apply n2; trivial.
 case (S n0 === n); intros. case (y == y); intros; trivial.
 apply False_ind. apply n2; trivial. trivial. 
 simpl in *|-*. apply notin_singleton in H. apply notin_singleton in H0.
 case (v == y); intros; simpl. symmetry in e. contradiction.
 case (v == x); intros; simpl; trivial. symmetry in e. contradiction.
 simpl in H. apply notin_union in H. destruct H.
 simpl in H0. apply notin_union in H0. destruct H0.
 simpl. rewrite IHt1; trivial. rewrite IHt2; trivial.
 simpl in H. simpl in H0. simpl. rewrite IHt; trivial.
 simpl in H. apply notin_union in H. destruct H.
 simpl in H0. apply notin_union in H0. destruct H0.
 simpl. rewrite IHt1; trivial. rewrite IHt2; trivial.
 simpl in H. apply notin_union in H. destruct H.
 simpl in H0. apply notin_union in H0. destruct H0.
 simpl. rewrite IHt1; trivial. rewrite IHt2; trivial.
Qed. 



Lemma openclose_com : forall x y i j t, x <> y -> i <> j -> 
      ({i ~> pterm_fvar x}close_rec j y t) = close_rec j y ({i ~> pterm_fvar x}t).
Proof.
 intros. generalize i j H0; clear i j H0. induction t; intros.
 unfold open_rec. unfold close_rec. 
 case (i === n); case (x == y); intros; trivial. contradiction.
 simpl. case (v == y); intros; trivial. unfold open_rec.
 case (i ===j); intros; trivial. contradiction.
 simpl. rewrite IHt1; trivial. rewrite IHt2; trivial.
 simpl. rewrite IHt; try omega; trivial.
 simpl. rewrite IHt1; try omega; trivial. rewrite IHt2; trivial.
 simpl. rewrite IHt1; try omega; trivial. rewrite IHt2; trivial.
Qed.


Lemma body_term_fvar : forall x t n, 
lc_at (S n) t -> x \notin (fv t) -> x \notin (fv (open_rec n (pterm_fvar x) t)) ->
lc_at n t.
Proof.
  intros x t n.
  generalize n; clear n. induction t.
  (* bvar *)
  intros n' H0 H1.
  unfolds open_rec.  
  case (n' === n). intros. simpl in H.
  apply notin_singleton in H. assert (x = x). 
  trivial. contradiction. intros. simpl in *|-*. omega.
  (* fvar *)
  intros n H0 H1 H2. simpl. trivial.
  (* app *)
  intros n H0 H1 H2. simpl in *|-*.
  apply notin_union in H1.
  apply notin_union in H2.
  case H0; clear H0; intros H0t1 H0t2.
  case H1; clear H1; intros H1t1 H1t2.
  case H2; clear H2; intros H2t1 H2t2.
  split.
  apply (IHt1 n H0t1 H1t1 H2t1).
  apply (IHt2 n H0t2 H1t2 H2t2).
  (* lam *) 
  intros n H0 H1 H2. simpl in *|-*.
  apply (IHt (S n) H0 H1 H2).
  (* sub *)
  intros n H0 H1 H2. simpl in *|-*.
  apply notin_union in H1.
  apply notin_union in H2.
  case H0; clear H0; intros H0t1 H0t2.
  case H1; clear H1; intros H1t1 H1t2.
  case H2; clear H2; intros H2t1 H2t2.
  split.
  apply (IHt1 (S n) H0t1 H1t1 H2t1).
  apply (IHt2 n H0t2 H1t2 H2t2).
  (* sub' *)
  intros. simpl in H. contradiction.
Qed.

Lemma not_body_term_fvar : forall x t n, 
lc_at (S n) t -> x \notin (fv t) -> x \in (fv (open_rec n (pterm_fvar x) t)) ->
~ lc_at n t.
Proof.
  intros x t n.
  generalize n; clear n. induction t.
  (* bvar *)
  intros n' H0 H1.
  unfolds open_rec.  
  case (n' === n). intros. simpl in *|-*. omega.
  intros. simpl in *|-*. contradiction.
  (* fvar *)
  intros n H0 H1 H2. simpl in *|-*. contradiction.
  (* app *)
  intros n H0 H1 H2. simpl in *|-*.
  apply notin_union in H1.
  apply in_union in H2.
  case H0; clear H0; intros H0t1 H0t2.
  case H1; clear H1; intros H1t1 H1t2.
  intro H. case H. clear H. intros H H'.
  case H2. 
  intro H2'. generalize H. 
  apply (IHt1 n H0t1 H1t1 H2').
  intro H2'. generalize H'. 
  apply (IHt2 n H0t2 H1t2 H2').
  (* lam *) 
  intros n H0 H1 H2. simpl in *|-*.
  apply (IHt (S n) H0 H1 H2).
  (* sub *)
  intros n H0 H1 H2. simpl in *|-*.
  apply notin_union in H1.
  apply in_union in H2.
  case H0; clear H0; intros H0t1 H0t2.
  case H1; clear H1; intros H1t1 H1t2.
  intro H. case H. clear H. intros H H'.
  case H2. 
  intro H2'. generalize H. 
  apply (IHt1 (S n) H0t1 H1t1 H2').
  intro H2'. generalize H'. 
  apply (IHt2 n H0t2 H1t2 H2').
  (* sub' *)
  intros. simpl in H. contradiction.
Qed.

Lemma rec_close_open_term : forall t x k, x \notin (fv t) -> t = close_rec k x (open_rec k (pterm_fvar x) t). 
 Proof.
 intros t x.
 induction t.
 (* bvar *) 
 intros k H1. simpl.
 case (k === n).
 intro H2. simpl.
 case (x == x). 
 intro H. rewrite H2. trivial.
 intro H3. assert (x = x); trivial.
 contradiction.
 intro H2. simpl. trivial.
 (* fvar *)
 intros k H. simpl in H.
 apply notin_singleton in H.
 simpl. case (v == x).
 intro H1. assert (x = v).
 auto. contradiction.
 intro. trivial.
 (* app *)
 intros k H.
 simpl in H. apply notin_union in H.
 simpl; fequals.
 apply IHt1. apply H.
 apply IHt2. apply H.  
 (* abs *)
 intros k H. simpl.
 fequals. apply IHt.
 simpl in H. assumption.
 (* subs *)
 intros k H. simpl.
 simpl in H. 
 apply notin_union in H.
 fequals.
 apply IHt1. apply H.
 apply IHt2. apply H.  
 (* subs' *)
 intros k H. simpl.
 simpl in H. 
 apply notin_union in H.
 fequals.
 apply IHt1. apply H.
 apply IHt2. apply H.  
Qed.


Lemma close_open_term : forall t x, x \notin (fv t) -> t = close (t ^ x) x. 
Proof.
 intros. unfold open. unfold close.
 apply rec_close_open_term.
 assumption.
Qed.


Lemma lc_at_subst: forall n t u x, lc_at n t -> lc_at n u -> lc_at n ([x ~> u]t).
Proof.
 intros n t u x. generalize n; clear n.  
 induction t.  
 intro n'. simpl. intros; trivial.
 intro n'. simpl. intros; case (v == x). 
 intros; trivial. simpl. intros; trivial.
 simpl. intros n H1 H2. case H1; clear H1; intros H1 H3.
 split. apply IHt1; trivial. apply IHt2; trivial.
 simpl. intros n' H1 H2. apply IHt; trivial.
 apply lc_at_weaken_ind with (k1 := n'); trivial; omega.
 simpl. intros n' H1 H2. case H1; clear H1; intros H1 H3.
 split. apply IHt1; trivial.
 apply lc_at_weaken_ind with (k1 := n'); trivial; omega.
 apply IHt2; trivial.
 intros. simpl in H. contradiction.
Qed.

Lemma lc_at_subst': forall n t u x, lc_at n ([x ~> u]t) -> lc_at n t.
Proof. 
intros n t u x. generalize n; clear n.  
 induction t.  
 intro n'. simpl. intros; trivial.
 intro n'. simpl. intros; case (v == x);
 intros; trivial. 
 simpl. intros n H. case H; clear H; intros H1 H2.
 split. apply IHt1; trivial. apply IHt2; trivial.
 simpl. intros n' H. apply IHt; trivial.
 simpl. intros n' H. case H; clear H; intros H1 H2.
 split. apply IHt1; trivial.
 apply IHt2; trivial.
 intros.  simpl in H. contradiction.
Qed.

Lemma size_bswap_rec : forall n t, pterm_size (bswap_rec n t) = pterm_size t.
Proof.
 intros n t. generalize n; clear n. 
 induction t.
 intro n'. unfolds bswap_rec.
 case (n' === n).
 intro; simpl; trivial.
 case (S n' === n).
 intros; simpl; trivial.
 intros; simpl; trivial.
 intro n; simpl; trivial.
 simpl; intro n; rewrite (IHt1 n); rewrite (IHt2 n); trivial.
 simpl; intro n; rewrite (IHt (S n)); trivial.
 simpl; intro n; rewrite (IHt1 (S n)); rewrite (IHt2 n); trivial.
 simpl; intro n; rewrite (IHt1 (S n)); rewrite (IHt2 n); trivial.
Qed.

Lemma fv_bswap_rec : forall n t, fv (bswap_rec n t) = fv t.
Proof.
 intros n t. generalize n; clear n. 
 induction t.
 intro n'. unfolds bswap_rec.
 case (n' === n).
 intro; simpl; trivial.
 case (S n' === n).
 intros; simpl; trivial.
 intros; simpl; trivial.
 intro n; simpl; trivial.
 simpl; intro n; rewrite (IHt1 n); rewrite (IHt2 n); trivial.
 simpl; intro n; rewrite (IHt (S n)); trivial.
 simpl; intro n; rewrite (IHt1 (S n)); rewrite (IHt2 n); trivial.
 simpl; intro n; rewrite (IHt1 (S n)); rewrite (IHt2 n); trivial. 
Qed.


Lemma open_bswap : forall n t u v, term v -> 
(open_rec (S n) u (open_rec n v t)) = (open_rec n u (open_rec (S n) v (bswap_rec n t))).
Proof.
 intros n t u v T. 
 generalize n; clear n; induction t. 
 (* bvar *)
 intro n'.
 unfolds bswap_rec. unfolds open_rec. 
 case_nat*. fold open_rec. case_nat*.
 replace ({S n ~> u}v) with v;
 replace ({n ~> u}v) with v; trivial;
 apply open_rec_term; trivial.
 case_nat*. fold open_rec. case_nat*. 
 rewrite e0 in e. contradiction.  
 simpl. case_nat*.  case_nat*.
 case_nat. trivial.
 (* fvar *) 
 intro n'.
 simpl; trivial.
 (* app *)
 intro n'.
 simpl. rewrite (IHt1 n'). rewrite (IHt2 n').
 trivial. 
 (* abs *)
 intro n'.
 simpl. rewrite (IHt (S n')). trivial.
 (* sub *)
 intro n'.
 simpl. rewrite (IHt1 (S n')). rewrite (IHt2 n').
 trivial.
 (* sub' *)
 intro n'.
 simpl. rewrite (IHt1 (S n')). rewrite (IHt2 n').
 trivial.
Qed.

Lemma subst_com :forall i j t u v, i <> j -> term u -> term v -> 
(open_rec i u (open_rec j v t)) = (open_rec j v (open_rec i u t)).
Proof.
 intros i j t u v H Tu Tv.
 generalize i j H. clear H i j.
 induction t.
 (* bvar *)
 intros i j H.
 unfolds open_rec. case_nat*. 
 fold open_rec. case_nat.
 unfolds open_rec. case_nat*.
 fold open_rec. replace ({i ~> u}v) with v; trivial.
 apply open_rec_term; trivial.
 case_nat. fold open_rec.
 apply open_rec_term; trivial.
 case_nat. trivial.
 (* fvar *)
 intros i j H.
 simpl; trivial.
 (* app *)
 intros i j H. simpl.
 rewrite (IHt1 i j H).
 rewrite (IHt2 i j H). trivial.
 (* abs *)
 intros i j H. simpl.
 assert (Q: (S i) <> (S j)). omega.
 rewrite (IHt (S i) (S j) Q). trivial.
 (* sub *)
 intros i j H. simpl.
 assert (Q: (S i) <> (S j)). omega.
 rewrite (IHt1 (S i) (S j) Q). trivial.
 rewrite (IHt2 i j H). trivial.
 (* sub' *)
 intros i j H. simpl.
 assert (Q: (S i) <> (S j)). omega.
 rewrite (IHt1 (S i) (S j) Q). trivial.
 rewrite (IHt2 i j H). trivial.
Qed.

Lemma body_open_bswap: forall i j t x, 
lc_at i ({j ~> pterm_fvar x} t) ->
lc_at i ({(S j) ~> pterm_fvar x}(bswap_rec j t)).
Proof.
 intros i j t x.
 generalize i j; clear i j.
 induction t.
 (* bvar *)
 intros i j H. unfolds bswap_rec. unfolds open_rec.
 case_nat*. case_nat. trivial.
 case_nat*. case_nat. simpl. trivial.
 replace n with (S j) in H.
 simpl in H. unfolds lc_at. omega.
 case_nat. simpl. trivial. trivial.
 (* fvar *)
 intros i j H. simpl. trivial.
 (* app *) 
 simpl. intros i j H. split.
 apply (IHt1 i j). apply H.
 apply (IHt2 i j). apply H.
 (* abs *)
 simpl. intros i j H.
 apply (IHt (S i) (S j)). apply H.
 (* sub *)
 simpl. intros i j H. split.
 apply (IHt1 (S i) (S j)). apply H.
 apply (IHt2 i j). apply H.
 (* sub' *)
 simpl. intros; contradiction.
Qed.
 

Lemma lc_at_bswap : forall n k t, S k < n -> lc_at n t -> lc_at n (bswap_rec k t).
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
 intros n k H0 H1. simpl in *|-*. destruct H1. split.
 apply IHt1; try omega; trivial. apply IHt2; trivial.
 (* sub' *)
 intros n k H0 H1. simpl in *|-*. contradiction.
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

 
Lemma lc_at_open : forall n t u, term u -> (lc_at (S n) t <-> lc_at n (open_rec n u t)).
Proof.
 intros n t u T. split.
(* -> *)
 generalize n; clear n.
 induction t.
 (* bvar *)
 intros n' H0. unfolds open_rec.
 case (n' === n). intro H1.
 rewrite H1 in H0. rewrite H1. simpl in *|-*. 
 apply term_to_term' in T. unfold term' in T.
 apply lc_at_weaken_ind with (k1 := 0); try omega; trivial.
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
 intros n H. simpl in *|-*.
 case H; clear H; intros Ht1 Ht2; split.
 apply (IHt1 (S n) Ht1). 
 apply (IHt2 n Ht2).
 (* sub' *)
 simpl. intros. contradiction.
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
 simpl in *|-*. intros n H. 
 case H; clear H; intros Ht1 Ht2; split.
 apply (IHt1 (S n) Ht1). 
 apply (IHt2 n Ht2).
 (* sub' *)
 simpl. intros. contradiction.
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


Lemma lc_at_open' : forall n k t u, term u -> k < n -> (lc_at n (open_rec k u t) <-> lc_at n t).
Proof.
 intros n k t u H; generalize n k; clear n k. induction t; simpl; intros; trivial.
 case (k === n); simpl. intros. split. omega.
 intros. apply lc_at_weaken_ind with (k1 := 0); try omega.
 apply term_eq_term'; trivial. intros; split; trivial. split; trivial.
 assert (Q1 : lc_at n ({k ~> u}t1) <-> lc_at n t1). apply IHt1; trivial. 
 assert (Q2 : lc_at n ({k ~> u}t2) <-> lc_at n t2). apply IHt2; trivial.
 split; intro H1; destruct H1. 
 split; [apply Q1; trivial | apply Q2; trivial].
 split; [apply Q1; trivial | apply Q2; trivial].
 assert (Q :(lc_at (S n) ({(S k) ~> u}t) <-> lc_at (S n) t)). apply IHt; try omega; trivial.
 apply Q; trivial.
 assert (Q1 :(lc_at (S n) ({(S k) ~> u}t1) <-> lc_at (S n) t1)). apply IHt1; try omega; trivial.
 assert (Q2 : lc_at n ({k ~> u}t2) <-> lc_at n t2). apply IHt2; trivial.
 split; intro H1; destruct H1.
 split; [apply Q1; trivial | apply Q2; trivial].
 split; [apply Q1; trivial | apply Q2; trivial].
 intros. split; intros; contradiction.
Qed.


(** bswap is idempotent. *)

Lemma bswap_rec_id : forall n t, bswap_rec n (bswap_rec n t)  = t.
Proof.
 intros. generalize n. clear n.
 induction t.
 (* bvar *)
 intros n'. unfolds bswap_rec.
 case (n' === n). intro H1.
 case (n' === S n'). intros H2.
 assert (Q: n' <> S n'). omega.
 contradiction. intro H2.
 case (S n' === S n'). intro H3.
 rewrite H1. trivial. intro H3.
 assert (Q: S n' = S n'). trivial.
 contradiction. intro H. fold bswap_rec.
 case (S n' === n). intro H1. unfolds bswap_rec.
 case (n' === n'). intro H2. rewrite H1. trivial.
 intros H2. assert (Q: n' = n'). trivial.
 contradiction. intro H1. unfolds bswap_rec.
 case (n' === n). intro H2. contradiction. intro H2.
 case (S n' === n). intro H3. contradiction. intro H3.
 trivial.
 (* fvar *)
 intro n. simpl. trivial.
 (* app *)
 intro n. simpl. rewrite (IHt1 n). rewrite (IHt2 n).
 trivial.
 (* abs *)
 intro n. simpl. rewrite (IHt (S n)). trivial.
 (* sub *)
 intro n. simpl. rewrite (IHt1 (S n)). rewrite (IHt2 n).
 trivial.
 (* sub' *)
 intro n. simpl. rewrite (IHt1 (S n)). rewrite (IHt2 n).
 trivial.
Qed.

Lemma bswap_idemp : forall t, (& (& t)) = t.
Proof.
  intro t. unfold bswap.
  apply bswap_rec_id.
Qed.

Lemma bswap_lc_at : forall n t, lc_at n t -> bswap_rec n t = t.
Proof.
 intros n t. generalize n. clear n. induction t.
 intros n' H. simpl in H. unfolds bswap_rec.
 case (n' === n). intro H1. rewrite H1 in H. assert (~ n < n). auto with arith. 
 contradiction.
 intro H1. case (S n' === n). intro H2. 
 replace n with (S n') in H. assert (~ (S n') < n'). auto with arith.
 contradiction.
 intro H2; trivial.
 intros; trivial. 
 simpl. intros n H. case H; clear H; intros H1 H2.
 rewrite (IHt1 n H1). rewrite (IHt2 n H2). trivial.
 simpl. intros n H. rewrite (IHt (S n) H). trivial.
 simpl. intros n H. case H; clear H; intros H1 H2.
 rewrite (IHt1 (S n) H1). rewrite (IHt2 n H2). trivial.
 intros. simpl in H. contradiction.
Qed. 

Lemma bswap_n_term : forall t n, term t -> bswap_rec n t = t.
Proof.
 intros t n H. 
  apply bswap_lc_at. apply lc_at_weaken.
  apply term_to_term'; trivial.
Qed.

Lemma bswap_term : forall t, term t -> t = & t.
Proof.
  intros t H. unfold bswap.
  rewrite bswap_n_term; trivial.
Qed.
  
Lemma subst_bswap_rec : forall n x u t, lc_at n u ->
     [x ~> u] (bswap_rec n t) = bswap_rec n ([x ~> u] t).
Proof.
 intros n x u t. generalize n. clear n. induction t.
 intro n'. replace ([x ~> u]pterm_bvar n) with (pterm_bvar n).
 unfolds bswap_rec.
 case (n' === n). intros; simpl; trivial.
 case (S n' === n); intros; simpl; trivial.
 simpl; trivial.
 intros n'. simpl. case (v == x).
 intros. rewrite bswap_lc_at; trivial.
 intros. simpl. trivial.
 intros n H. simpl. rewrite (IHt1 n H). rewrite (IHt2 n H). trivial.
 intros n H. simpl. rewrite (IHt (S n)). trivial.
 apply lc_at_weaken_ind with (k1 := n); trivial; try omega.
 intros n H. simpl. rewrite (IHt1 (S n)). rewrite (IHt2 n); trivial.
 apply lc_at_weaken_ind with (k1 := n); trivial; try omega.
 intros n H. simpl. rewrite (IHt1 (S n)). rewrite (IHt2 n); trivial.
 apply lc_at_weaken_ind with (k1 := n); trivial; try omega.
Qed.


Lemma open_lc_at : forall n t u, lc_at n t -> open_rec n u t = t.
Proof.
 intros n t u. generalize n; clear n. 
 induction t. intro n'.
 simpl. intro H. case (n' === n).
 intro H1. rewrite H1 in H. assert (~ n < n). auto with arith. 
 contradiction.
 intro H1. reflexivity. 
 intro n. simpl. reflexivity.
 simpl. intros n H. 
 rewrite IHt1; try apply H.
 rewrite IHt2; try apply H. reflexivity.
 simpl. intros n H.
 rewrite IHt; try apply H. reflexivity.
 simpl. intros n H.
 rewrite IHt1; try apply H.
 rewrite IHt2; try apply H. reflexivity.
 simpl. intros. contradiction.
Qed.

Lemma bswap_open_rec : forall n k t u, k > S n -> lc_at n u ->
      bswap_rec n (open_rec k u t) = open_rec k u (bswap_rec n t).
Proof.
 intros n k t u. generalize n k; clear n k.
 induction t. intros n' k H H'.
 unfolds open_rec. case (k === n). fold open_rec.
 intro H0. unfold bswap. unfolds bswap_rec.
 case (n' === n). fold bswap_rec. intro H1.
 rewrite H1 in H. rewrite H0 in H. 
 assert (~ n > S n). auto with arith. contradiction.
 fold bswap_rec. case (S n' === n).
 intros H1 H2. rewrite H0 in H. rewrite H1 in H.
 assert (~ n < n). auto with arith. contradiction.
 intros H1 H2.
 rewrite H0. simpl. case (n === n).
 intro H3. apply bswap_lc_at; trivial. intro H3. 
 assert (n = n). reflexivity.
 contradiction. intro H0. fold open_rec.
 unfold bswap. unfolds bswap_rec.
 case (n' === n). fold bswap_rec. intro H1.
 unfolds open_rec. case (k === S n').
 intro H2. rewrite H2 in H. rewrite H1 in H.
 assert (~ S n > S n). auto with arith. contradiction.
 intro H2. reflexivity.
 fold bswap_rec. case (n' === n).
 intros H1 H2. case (S n'=== n). intro H3. 
 contradiction. unfolds open_rec.
 case (k === n). intros H3 H4; contradiction.
 reflexivity. case (S n' === n). intros H1 H2 H3.
 unfolds open_rec. case (k === n'). intro H4.
 rewrite H4 in H. assert (~ n' > S n').  auto with arith. contradiction.
 reflexivity. intros H1 H2 H3.
 unfolds open_rec. case (k === n). intro H4.
 contradiction. reflexivity.
 intros; unfolds; simpl. reflexivity.
 unfold bswap in *|-*. simpl. intros n k H H'.
 rewrite IHt1; trivial. rewrite IHt2; trivial.
 unfold bswap in *|-*. simpl. intros n k H H'.
 rewrite IHt; try omega; trivial.
 apply lc_at_weaken_ind with (k1 := n); 
 try omega; trivial.
 unfold bswap in *|-*. simpl. intros n k H H'.
 rewrite IHt1; try omega; trivial.
 rewrite IHt2; trivial.
 apply lc_at_weaken_ind with (k1 := n); 
 try omega; trivial.
 simpl. intros n k H H'.
 rewrite IHt1; try omega; trivial.
 rewrite IHt2; trivial.
 apply lc_at_weaken_ind with (k1 := n); 
 try omega; trivial.
Qed.

