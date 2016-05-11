(***************************************************************************
* Formalization of ES calculi						   *
*									   *
* Infrastructure for explicit substitutions, not specific to a calculus    *
*									   *
* Arthur Chargu\u00e9raud, 2007						   *
* Fabien Renaud & St\u00e9phane Zimmerman, 2011				   *
* Flávio L. C. de Moura, 2016                                              *
***************************************************************************)


Set Implicit Arguments.
Require Import  Metatheory LambdaES_Defs. 
Require Import Rewriting LambdaES_Tac LambdaES_FV.
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
  intro. split; inversion H; assumption.
  intro. destruct H.
  apply term_app; assumption.
Qed.

Hint Resolve body_open_term.

Lemma not_body_Sn: forall n, ~(body (pterm_bvar (S n))).
Proof.
  intro n. intro H. elim H.
  intro L. intro H1. pick_fresh z.
  assert (z \notin L). auto.
  assert (term (pterm_bvar (S n) ^ z)).
  apply H1. assumption. inversion H2.
Qed.  
  
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
  | pterm_lsub t1 t2 => False
  end.

Definition term' t := lc_at 0 t.

Definition body' t := lc_at 1 t.


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

Inductive SN_alt (R : pterm -> pterm -> Prop) (t : pterm) : Prop :=
| SN_nf : NF R t -> SN_alt R t
| SN_acc : forall t', R t t' -> SN_alt R t' -> SN_alt R t.

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

(*** about SN and NF in lists *)

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

(* ********************************************************************** *)
(** Induction Principles Part 2 *)

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

Lemma swap_eq_m_sb : forall (x y z : var) t, z <> x -> z <> y -> z \notin (fv t) ->  
      m_sb z (pterm_fvar y) ((m_sb y (pterm_fvar x) (m_sb x (pterm_fvar z) t))) = [(x,y)] t.
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
 rewrite <- swap_eq_m_sb with (z := z); trivial.
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

(*
Lemma open_rec_indep_comm: forall t x y, {0 ~> pterm_fvar x}({1 ~> pterm_fvar y}t) = {1 ~> pterm_fvar y}({0 ~> pterm_fvar x}t). 
Proof.
  Admitted.*)
    
Lemma lc_at_open_rec_rename: forall t x y m n, lc_at m (open_rec n (pterm_fvar x) t) -> lc_at m (open_rec n (pterm_fvar y) t).
Proof.
  induction t. simpl. introv H. case_nat. constructor. assumption.
  simpl. intros; trivial. simpl. introv H. destruct H.
  apply (IHt1 x y) in H. apply (IHt2 x y) in H0.
  split; assumption. simpl.
  introv H. apply IHt with x. assumption. simpl.
  introv H. destruct H. split. apply IHt1 with x; assumption. apply IHt2 with x; assumption.
  simpl. trivial.
Qed.  

Corollary term_open_rename: forall t x y, term (t^x) -> term (t^y).  
Proof.
  introv H. apply term_eq_term' in H. apply term_eq_term'.
  apply lc_at_open_rec_rename with x. assumption.
Qed.
  
Lemma body_to_term: forall t x, x \notin fv t -> body t -> term (t^x).
Proof.
  intros. inversion* H0.
Qed.

Lemma term_to_body: forall t x, x \notin fv t -> term (t^x) -> body t.
Proof.
  introv H H'. 
  unfold body.
  exists (fv t). introv H''. apply term_open_rename with x; assumption.
Qed.
  
(* ********************************************************************** *)
(** Properties of reduction *)

Definition red_regular (R : pterm -> pterm -> Prop) :=
  forall t t', R t t' -> term t /\ term t'.

Definition red_regular' (R : pterm -> pterm -> Prop) :=
  forall t t', R t t' -> (term t <-> term t').

Definition red_refl (R : pterm -> pterm -> Prop) :=
  forall t, term t -> R t t.

Definition red_in (R : pterm -> pterm -> Prop) :=
  forall t x u u', term t -> R u u' ->
  R ([x ~> u]t) ([x ~> u']t).
 
Definition red_all (R : pterm -> pterm -> Prop) :=
  forall x t t', R t t' -> 
  forall u u', R u u' -> 
  R ([x~>u]t) ([x~>u']t').

Definition red_out (R : pterm -> pterm -> Prop) :=
  forall x u t t', term u -> R t t' -> 
  R ([x~>u]t) ([x~>u]t').

Definition red_out' (R : pterm -> pterm -> Prop) :=
  forall x y t t', R t t' -> 
  R ([x~>pterm_fvar y]t) ([x~>pterm_fvar y]t').

Definition red_rename (R : pterm -> pterm -> Prop) :=
  forall x t t' y,
  x \notin (fv t) -> x \notin (fv t') ->
  R (t ^ x) (t' ^ x) -> 
  R (t ^ y) (t' ^ y).

Definition red_rename' (R : pterm -> pterm -> Prop) :=
  forall x t t' y,
  x \notin (fv t) -> x \notin (fv t') ->
  y \notin (fv t) -> y \notin (fv t') ->
  R (t ^ x) (t' ^ x) -> 
  R (t ^ y) (t' ^ y).

Definition red_swap (R : pterm -> pterm -> Prop) :=
  forall x t t' y,
  R t t' ->
  R ([(x,y)]t) ([(x,y)]t').

Definition red_through (R : pterm -> pterm -> Prop) :=
  forall x t1 t2 u1 u2, 
  x \notin (fv t1) -> x \notin (fv u1) ->
  R (t1 ^ x) (u1 ^ x) -> R t2 u2 ->
  R (t1 ^^ t2) (u1 ^^ u2).

Definition red_not_fv (R: pterm -> pterm -> Prop) :=
  forall x t t', R t t' ->
  x \notin (fv t) -> x \notin (fv t'). 

Definition red_fv (R: pterm -> pterm -> Prop) :=
  forall x t t', R t t' ->
  x \in (fv t') -> x \in (fv t). 

Lemma red_regular_ctx: forall (R : pterm -> pterm -> Prop),
  red_regular R -> red_regular (ES_contextual_closure R).
 Proof.
  intros_all. induction H0.
  apply H; trivial. 
  case IHES_contextual_closure; clear IHES_contextual_closure.
  intros H2 H3. split; apply term_distribute_over_application; split ; trivial.
  case IHES_contextual_closure; clear IHES_contextual_closure.
  intros H2 H3. split; apply term_distribute_over_application; split ; trivial.
  split; apply body_to_term_abs; unfold body; exists L;
  intros; apply H1; trivial.
  split; apply body_to_subs; trivial; unfold body; exists L; intros; apply H1; trivial.
  split; apply body_to_subs; apply term_is_a_body in H1.
  assumption. apply IHES_contextual_closure. 
  assumption. apply IHES_contextual_closure. 
Qed.

 (** flavio 2016/02/19
Lemma SN_app : forall n R t u, red_regular R ->  
               SN_ind n (ES_contextual_closure R) (pterm_app t u) ->
               SN_ind n (ES_contextual_closure R) t /\ SN_ind n (ES_contextual_closure R) u.
Proof.
 intros n R t u Reg. 
 generalize dependent u.
 generalize dependent t.
 induction n.  intros t u H. split; rewrite <- NF_eq_SN0 in *; unfold NF in *. 
 intros t' H'. apply (H (pterm_app t' u)).
 apply ES_app_left. assumption.
 false_goal.
 assert (ES_contextual_closure R (pterm_app t u) (pterm_app t' u)).
 apply ES_app_left; trivial. 
 intros u' H'. apply (H (pterm_app t u')). apply ES_app_right; trivial.
 intros t u H. destruct H. split. 
 apply SN_intro. intros t' H'. exists n. split; try omega. 
 apply IHn with (t := t') (u := u); trivial. apply red_regular_ctx in Reg.
 apply Reg in H'. apply H'. case (H (pterm_app t' u)). apply app_left; trivial. 
 intros k H''. apply WSN with (k := k). omega. apply H''.
 apply SN_intro. intros u' H'. exists n. split; try omega. 
 apply IHn with (t := t) (u := u'); trivial. apply red_regular_ctx in Reg.
 apply Reg in H'. apply H'. case (H (pterm_app t u')). apply app_right; trivial. 
 intros k H''. apply WSN with (k := k). omega. apply H''.
Qed. 


Lemma SN_abs : forall x n R t, red_regular R -> red_out R -> 
               SN_ind n (contextual_closure R) (pterm_abs t) ->
               x \notin (fv t) -> SN_ind n (contextual_closure R) (t ^ x).
Proof.
 intros x n R t Reg Out.
 generalize t; clear t.
 apply red_regular_ctx in Reg. gg
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
*)


(** Reduction on lists **)

Definition R_list (R : pterm -> pterm -> Prop) (l : list pterm) (l' : list pterm) := 
exists t, exists t', exists l0, exists l1, l = (l0 ++ t :: l1) /\ l' = (l0 ++ t' :: l1) /\ R t t'.

Lemma R_list_h: forall (R : pterm -> pterm -> Prop) a b lt, 
                R a b -> R_list R (a :: lt) (b :: lt).   
Proof.
 intros. unfold R_list. exists a. exists b. exists (nil (A := pterm)). exists lt.
 simpl. split; trivial; split; trivial.
Qed.

Lemma R_list_t: forall (R : pterm -> pterm -> Prop) a lt lt', 
                (R_list R lt lt') -> R_list R (a :: lt) (a :: lt').
Proof.
 unfold R_list. intros.
 case H; clear H. intros b H.
 case H; clear H. intros b' H.
 case H; clear H. intros l H.
 case H; clear H. intros l' H.
 destruct H. destruct H0. 
 rewrite H. rewrite H0.
 exists b. exists b'. 
 exists (a :: l). exists l'. simpl.
 split; trivial. split; trivial.
Qed.

Lemma term_mult_app : forall t lu, term (t // lu) <-> term t /\ (term %% lu).
Proof.
 intros t lu. induction lu; simpl; split; 
 intro H;  try apply H; try split; trivial.
 apply term_distribute_over_application in H. 
 apply IHlu. apply H.
 apply term_distribute_over_application in H.
 split. apply H. apply IHlu. apply H.
 apply term_distribute_over_application. split.
 apply IHlu. split; apply H. apply H.
Qed.

Lemma ctx_red_t_mult_app : forall R t lu lu', term t -> term %% lu -> R_list (ES_contextual_closure R) lu lu' -> (ES_contextual_closure R) (t // lu) (t // lu').
Proof.
 intros R t lu lu' Tt Tlu H. unfold R_list in H. 
 case H; clear H; intros t0 H.
 case H; clear H; intros t1 H.
 case H; clear H; intros l0 H.
 case H; clear H; intros l1 H.
 destruct H. destruct H0. 
 rewrite H. rewrite H0. rewrite H in Tlu. 
 clear H H0. induction l0; simpl. destruct l1; simpl. 
 apply ES_app_right; trivial.
 apply ES_app_right; trivial. 
 simpl in Tlu. rewrite term_distribute_over_application.
 rewrite term_mult_app. destruct Tlu. destruct H0.
 split; trivial. split; trivial.
 simpl in Tlu. destruct Tlu. 
 apply ES_app_left; trivial.
 apply IHl0; trivial. 
Qed.

Lemma contextual_R1_R2: forall (R1 R2: pterm -> pterm -> Prop), 
                           (forall t t', R1 t t' -> R2 t t') -> 
                           (forall t t', ES_contextual_closure R1 t t' -> ES_contextual_closure R2 t t').
Proof.
 intros R1 R2 H t t' H'. induction H'.
 apply ES_redex. apply H; trivial.
 apply ES_app_left; trivial.
 apply ES_app_right; trivial.
 apply ES_abs_in with (L := L); trivial.
 apply ES_subst_left with (L := L); trivial.
 apply ES_subst_right; trivial.
Qed.

Lemma ctx_red_h_mult_app : forall R t t' lu, term %% lu -> (ES_contextual_closure R) t t' -> (ES_contextual_closure R) (t // lu) (t' // lu).
Proof.
 intros R t t' lu Tlu H. induction lu; simpl in *|-*; trivial.
 destruct Tlu. apply ES_app_left; trivial.
 apply IHlu; trivial.
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
  repeat rewrite <- swap_eq_m_sb with (z := z); trivial.
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
  repeat rewrite <- swap_eq_m_sb with (z := z); trivial.
  repeat apply H; trivial.
Qed. 

(** flavio 2016/02/19
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
*)