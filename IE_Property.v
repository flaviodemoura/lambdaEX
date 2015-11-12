(********************************************************************************
* Formalization of lambda ex						        *		
*									        *
* Flavio L. C. de Moura & Daniel L. Ventura, & Washington R. Segundo, 2015	*
*********************************************************************************)

Set Implicit Arguments.
Require Import Recdef. (*no caso de usarmos Function*)
Require Import Metatheory LambdaES_Defs LambdaES_Infra LambdaES_FV LambdaES_Tac.
Require Import Rewriting_Defs Rewriting_Lib.
Require Import Equation_C Lambda Lambda_Ex LambdaESLab_Defs LambdaESLab_Lib.

(** The extended reduction system is related to the lex-calculus
through a function that computes all the labelled substitutions. *)

Fixpoint xc (t: pterm) : pterm :=
  match t with
    | pterm_app t1 t2 => pterm_app (xc t1) (xc t2)
    | pterm_abs t1 => pterm_abs (xc t1)
    | pterm_sub t1 t2 => pterm_sub (xc t1) (xc t2)
    | pterm_sub' t1 t2 => (xc t1)^^(t2)
    | _ => t
  end.

(*==============================================================================================*)

Lemma var_gen_fv: forall E x, x = var_gen(E) <-> x \notin E.

Proof.
introv.
split.
intro Ha.
rewrite Ha.
apply var_gen_spec.

intro Hb.
destruct E.
Admitted.

(* versao de xc com a propriedade de regularidade lc => lc com Recdef*)

Function xc2 (t: pterm) {measure pterm_size t}: pterm :=
  match t with
    | pterm_app t1 t2 => pterm_app (xc2 t1) (xc2 t2)
    | pterm_abs t1 => let x := var_gen (fv t1)  in 
                          pterm_abs (close (xc2 (t1^x)) x)
    | pterm_sub t1 t2 => let x := var_gen (fv t1)  in 
                          pterm_sub (close (xc2 (t1^x)) x) (xc2 t2)
    | pterm_sub' t1 t2 => (xc2 t1)^^(t2)
    | _ => t
  end.

Proof.
intros. simpl. 
auto with arith.

intros. simpl.
auto with arith.

intros. simpl. 
unfold open.
rewrite <- pterm_size_open_var. 
auto with arith.

intros. simpl.
auto with arith.

intros. simpl.
unfold open.
rewrite <- pterm_size_open_var.
auto with arith.

intros. simpl.
auto with arith.
Defined.

(*==============================================================================================*)

(* versao de xc com a propriedade de regularidade lc => lc a la Chargueraud 
   porque nao definimos o caso: termo indefinido ?*)
(*
Definition xc2_body (xc_2: pterm -> pterm) (t: pterm): pterm :=
  match t with
    | pterm_app t1 t2 => pterm_app (xc_2 t1) (xc_2 t2)
    | pterm_abs t1 => let x := var_gen (fv t1)  in 
                          pterm_abs (close (xc_2 (t1^x)) x)
    | pterm_sub t1 t2 => let x := var_gen (fv t1)  in 
                          pterm_sub (close (xc_2 (t1^x)) x) (xc_2 t2)
    | pterm_sub' t1 t2 => (xc_2 t1)^^(t2)
    | _ => t
  end.

Definition xc_2 := fixmu xc_2_body pterm_size. *)

(*==============================================================================================*)

(** fv is compatible with open. TO BE MOVED: LambdaES_Defs. *)
Lemma fv_open: forall t u, fv(t ^^ u) << fv(t) \u fv(u).
Proof.
  unfold open.
  intros.
  generalize 0.
  induction t.
    intros.
    case n.
    simpl.
    case_nat.
    apply subset_union_weak_r.
    simpl.
    apply subset_union_weak_l.
    intros.
    simpl.
    case_nat.
    apply subset_union_weak_r.
    simpl.
    apply subset_union_weak_l.
    intros. simpl.
    apply subset_union_weak_l.
    intros.
    simpl.
    apply subset_trans with (F := fv ({n ~> u}t1) \u (fv t2 \u fv u)).
    apply subset_union_trans_r.
    apply IHt2.
Admitted.

(*==================================================================================================*)

Lemma xc_fv: forall t, fv (xc t) << fv(t).
Proof.  
  induction t.
  simpl; reflexivity.
  simpl; reflexivity.
  simpl.
  rewrite IHt1.
  rewrite IHt2; reflexivity.
  assumption.
  simpl.
  rewrite IHt1.
  rewrite IHt2; reflexivity.
  simpl.
  apply subset_trans with (F := fv(xc(t1)) \u fv(t2)).
  apply fv_open.
  apply subset_union_trans_l. assumption.
Qed.

(*
Lemma xc_open_distr: forall t u, xc (t ^^ u) = (xc(t))^^ (xc(u)).
Proof.
  intros. unfold open. generalize 0 u. clear u.
  induction t.
  intro. simpl. case_nat; reflexivity.

  Focus 5.
  intros.
  simpl.  
  unfold open.
  rewrite IHt1.
  assert ()
  rewrite <- IHt1 with (u := t2).
  
  
Lemma xc_open_term: forall t u, term u -> xc (t ^^ u) = (xc(t))^^ u.
Proof.
  intros. unfold open. generalize 0.
  generalize u H. clear u H.
  induction t.
  Focus 6.

  intro. simpl.
*)

Lemma term_open_term: forall x t, term t -> t^x = t.
Proof.
  unfold open.
  intros.
  generalize x 0; clear x.
  induction H.

  intros.
  simpl; reflexivity.

  intros.
  simpl.
  rewrite IHterm1.
  rewrite IHterm2; reflexivity.

  intros.
  simpl.
  pick_fresh z.
  assert (Q: ({S n ~> pterm_fvar x}t1)^z = t1^z).
  simpl.
Admitted.
  
Lemma xc_open: forall t x, x \notin fv(t) -> xc (t ^ x) = (xc t)^x.
Proof. 
  intros. unfold open. generalize 0.
  induction t.
  unfold open.
  intro. unfold open_rec.
  case_nat.
  fold open_rec.
  simpl xc.
  unfold open_rec.
  case_nat. reflexivity.
  fold open_rec.
  simpl. case_nat. reflexivity.
  intro. simpl. reflexivity.

  intro. simpl.
  rewrite IHt1.
  rewrite IHt2. reflexivity.

  simpl fv in H.  
  apply notin_union in H.
  destruct H; assumption.
  simpl fv in H.  
  apply notin_union in H.
  destruct H; assumption.

  Focus 3.
  intros.
  simpl.
  
Admitted.

(*================================================================================================*)

(* Igualdade sintática para pré-termos*)

Lemma eq_abs: forall t u, t = u -> pterm_abs t = pterm_abs u.
Proof.
 intros t u.
 apply f_equal.
Qed.

Lemma eq_pterm_abs: forall t u L,  (forall x, x \notin L -> t^x = u^x) -> pterm_abs t = pterm_abs u.
Proof.
 intros t u L Ha.
 apply eq_abs.
 pick_fresh z.
 apply notin_union in Fr. destruct Fr as [Hb Hc].
 apply notin_union in Hb. destruct Hb as [Hba Hbb].
 apply open_var_inj with (x := z).
 trivial. trivial. 
 apply Ha. trivial.
Qed.

Lemma eq_sub: forall t u v w, (t = v) -> (u = w) -> t[u] = (v[w]). 
Proof.
 intros t u v w Ha Hb. 
 assert (pterm_sub t = pterm_sub v) as Hc.
 apply f_equal. trivial.
 rewrite Hc.
 apply f_equal. trivial.
Qed.

Lemma eq_pterm_sub: forall t u t' u' L, (forall x, x \notin L -> t^x = t'^x) -> u = u' -> (t[u]) = (t'[u']).
Proof.
 intros t u t' u' L Ha Hb.
 apply eq_sub.
 pick_fresh z.
 apply notin_union in Fr. destruct Fr as [Hc Hd].
 apply notin_union in Hc. destruct Hc as [He Hf].
 apply notin_union in He. destruct He as [Hg Hh]. 
 apply notin_union in Hg. destruct Hg as [Hi Hj]. 
 apply open_var_inj with (x := z).
 trivial. trivial.
 apply Ha. trivial.
 trivial.
Qed.

(*==================================================================================*)

(*comutatividade para open_rec*)

Lemma open_rec_subs_comut: forall t u v j, {j~>u}(t[[v]]) = ({(S j)~>u}t[[{j~>u}v]]).
Proof.
 simpl. trivial.
Qed. 

Lemma open_rec_xc_comut: forall t u, xc t ^^ u = xc(t[[u]]).
Proof.
 simpl. trivial.
Qed.

Lemma open_rec_xc2_comut: forall t u, xc2 t ^^ u = xc2(t[[u]]).
Proof.
  introv.
  apply eq_sym.
  rewrite xc2_equation.
  trivial.
Qed.

Lemma notin_set_subset: forall E F x, E << F -> x \notin F -> x \notin E.  
Proof.
 introv Hs Hx.
Admitted. 

Lemma open_xc2: forall t, exists L, forall x, x \notin L -> xc2 (t ^ x) = xc2 t ^ x.
Proof.
 unfold open.
 generalize 0.
 introv.
 exists (fv t).
 introv Hx. 
  
 induction t.
 
 simpl. 
 destruct (n === n0) as []eqn:He1. (*reducao para if then else*)
 rewrite xc2_equation. trivial.
 rewrite xc2_equation. trivial.

 simpl.
 rewrite xc2_equation. trivial.
 
 simpl in Hx.
 apply notin_union in Hx.
 destruct Hx as [Hxl Hxr].
 simpl.
 rewrite xc2_equation.
 apply eq_sym.
 rewrite xc2_equation.
 simpl.
 rewrite IHt1.
 rewrite IHt2.
 trivial. trivial. trivial.
 
 simpl in Hx.
 simpl.
 rewrite xc2_equation.
 apply eq_sym.
 rewrite xc2_equation.
 simpl.
 apply eq_abs.
 (*assert (x = var_gen (fv t)) as Ht.
 apply var_gen_fv.
 trivial.
 rewrite <- Ht.*)
 unfold open.
 apply eq_sym.
 rewrite IHt. (*problema com generalize, n, 0 e Sn*)
 rewrite <- close_open_term with (x:= x).
 pick_fresh z.
 (*apply notin_union in Fr.*)
 assert (z = var_gen (fv ({1 ~> pterm_fvar x}t))) as Hz. 
 apply var_gen_fv.
 apply notin_set_subset with (F := (fv t \u {{x}})).
 apply fv_open_subset.
 rewrite  union_comm. trivial.
 rewrite <- Hz.
 unfold open.
 rewrite subst_com.
 unfold open  in IHt.
 rewrite IHt.
Admitted.
 
(*==================================================================================*)

Lemma xc_term_term: forall t, term t -> xc t = t.
Proof.
 (* intros t H.
  induction H.

  simpl; reflexivity.

  simpl.
  rewrite IHterm1.
  rewrite IHterm2; reflexivity.

  simpl.
  apply eq_pterm_abs with (L := L).
  intros x Ha.
  rewrite <- H0.
  rewrite xc_open_2 with (L := L). 
  trivial. trivial. 
  apply H. trivial. trivial.
  
  simpl.
  apply eq_pterm_sub with (L := L).
  intros x Ha.
  rewrite <- H0.
  rewrite xc_open_2 with (L := L).
  trivial. trivial. 
  apply H. trivial. trivial. trivial.
  
  (*
  simpl.
  pick_fresh z.
  apply notin_union in Fr.
  destruct Fr. 
  assert (Q: (xc t1)^z = t1^z).
  assert (U: xc(t1^z) = xc(t1)^z).
  apply xc_open; assumption.
  rewrite <- U.
  apply H0; assumption.
  apply open_var_inj with (x := z) in Q.
  rewrite Q; reflexivity.
Admitted.*)
 Qed.*)
Admitted.

Lemma term_lab_term: forall t, term t -> lab_term t.
Proof.
 introv Ha.
 induction Ha. 
 
 apply lab_term_var.
 apply lab_term_app. trivial. trivial.
 apply lab_term_abs with (L:= L). trivial.
 apply lab_term_sub with (L:=L). trivial. trivial.
Qed. 

Lemma xc2_reg: forall t, lab_term t -> term (xc2 t).
Proof.
 introv Ha.
 induction Ha.

 rewrite xc2_equation. 
 apply term_var.

 rewrite xc2_equation.
 apply term_app. trivial. trivial.
 
 rewrite xc2_equation.
 apply body_to_term_abs.
 apply close_var_body.
 pick_fresh z.
 assert (z = var_gen(fv t1)) as Ha.
 apply var_gen_fv. 
 apply notin_union_r2 with (E:= L). trivial.
 rewrite <- Ha.
 apply H0.
 apply notin_union_r1 with (F:= (fv t1)). trivial.
 
 rewrite xc2_equation.
 apply body_to_subs.
 apply close_var_body.
 pick_fresh z.
 assert (z = var_gen(fv t1)) as Hb.
 apply var_gen_fv. 
 apply notin_union_r2 with (E:= L). 
 apply notin_union_r1 with (F:= (fv t2)). trivial.
 rewrite <- Hb.
 apply H0.
 apply notin_union_r1 with (F:= fv t1). 
 apply notin_union_r1 with (F:= fv t2). trivial.
 trivial.
 
 rewrite xc2_equation.
 apply body_open_term.
 unfold body.
 exists L.
 introv Ha.
 pick_fresh z.

Admitted. 

Lemma xc2_term_term: forall t, term t -> xc2 t = t.
Proof.
 intros t Ha. 
 induction Ha.

 rewrite xc2_equation. 
 trivial.

 rewrite xc2_equation.
 rewrite IHHa1.
 rewrite IHHa2.
 trivial.

 rewrite xc2_equation.
 pick_fresh z.
 apply notin_union in Fr.
 destruct Fr as [Hb Hc]. 
 assert (z=var_gen (fv t1)) as Hd.
 apply var_gen_fv. trivial.
 rewrite <- Hd.
 rewrite H0.
 rewrite <- close_open_term. 
 trivial. trivial. trivial.

 rewrite xc2_equation.
 pick_fresh z.
 apply notin_union in Fr.
 destruct Fr as [Hb Hc].
 apply notin_union in Hb.
 destruct Hb as [Hd He].
 assert (z=var_gen (fv t1)) as Hf.
 apply var_gen_fv.
 trivial.
 rewrite <- Hf.
 rewrite H0.
 rewrite <- close_open_term. 
 rewrite IHHa.
 trivial. trivial. trivial.
Qed.

 Lemma xc_bswap: forall t, bswap(xc(t)) = xc(bswap(t)).
Proof.  
  intro.
  unfold bswap.
   generalize 0.
  induction t.
  intro.
  assert (xc (pterm_bvar n) = pterm_bvar n).
  simpl xc; reflexivity.
  rewrite H. 
  case (n0 === n).
  intro. rewrite e.
  simpl bswap_rec at 2. case_nat.
  simpl bswap_rec. case_nat.
  simpl xc; reflexivity.
  intro. 
  case (S n0 === n).
  intro Hn0. rewrite <- Hn0.
  simpl bswap_rec.
  case_nat.
  simpl xc; reflexivity.
  case_nat.
  simpl; reflexivity.
  intro Hn0.
  unfold bswap_rec.
  case_nat.
  case_nat.
  contradiction.
  simpl xc; reflexivity.
  intro n.
  simpl bswap_rec. simpl; reflexivity.
  intro n.
  simpl bswap_rec.  
  simpl xc at 3.
  fequal. apply IHt1. apply IHt2.
  intro n.
  simpl bswap_rec.
  simpl xc at 2.
  fequal. apply IHt.
  intro n.
  simpl bswap_rec.  
  simpl xc at 3.  
  fequal. apply IHt1. apply IHt2.
  intro n.
  simpl bswap_rec.
  simpl xc.
  rewrite <- IHt1.
Admitted.  

 Lemma xc2_bswap: forall t, bswap(xc2(t)) = xc2(bswap(t)).
Proof.
 introv.   
Admitted. (*precisamos desse caso geral ou de um mais especifico ?*)

Lemma xc_idempotent: forall t, xc(xc(t)) = t.
Proof.
  induction t.
  simpl; reflexivity.
  simpl; reflexivity.
  simpl. rewrite IHt1. rewrite IHt2; reflexivity.
  simpl. rewrite IHt; reflexivity.
  simpl. rewrite IHt1. rewrite IHt2; reflexivity.
  simpl.

  
  
Lemma xc_equations: forall t t', t =~e t' ->  xc t = xc t'.
Proof.
  intros t t' He.
  elim He.
  intros.
  elim H.
  intros.
  elim H0.
  intros; reflexivity.
  intros. simpl.
  unfold open. simpl.
  
  destruct H.
  induction H; trivial.
  induction t.
  induction n.
  simpl. simpl.
  Admitted.

   Lemma xc2_equations: forall t t', t =~e t' ->  xc2 t = xc2 t'.
Proof.
  introv He.
  destruct He as [t1|t2].
  destruct H.
  destruct H.
  
  trivial.

  rewrite xc2_equation.
  unfold open.
  apply eq_sym.
  rewrite xc2_equation.
  SearchAbout bswap.
  
  elim Hb.
  introv. trivial.
  introv Hc Hd.
  rewrite xc2_equation.
  rewrite xc2_equation.
  apply eq_sym.
  rewrite xc2_equation.
  unfold open. simpl.
  
  destruct H.
  induction H; trivial.
  induction t.
  induction n.
  simpl. simpl.
Admitted.
  
  Lemma xc_ex_equal: forall t t', t -->[ex] t' -> xc t = xc t'.
Proof.
  intros t t' Hex.
  destruct Hex.
  destruct H.
  destruct H.
  destruct H0.
  destruct H0. 
  induction H0.
  assert (xc(t) = xc (pterm_bvar 0 [[t0]])).
  apply xc_equations; assumption.
  simpl in H2. unfold open in H2. simpl in H2.
  (*rewrite H.*)  
Admitted.

  Lemma xc2_ex_equal: forall t t', lab_term t -> t -->[ex] t' -> xc2 t = xc2 t'.
Proof.
  introv Ht Hex.
  
  inversion Hex as [t1 Ha].
  inversion Ha as [t2 Hb].
  destruct Hb as [Hb Hc].
  destruct Hc as [Hc Hd]. 

  induction Ht.

  case Hc.

Admitted.
  

  (*
Lemma SN_lab_1 : forall S t u', lab_term S t -> ((U_lab t) -->lex u') -> 
                 exists u, lab_term S u /\ (t -->[lex] u) /\ u' = U_lab u .
Proof.
 intros.  
 case H0; clear H0. intros t0 H'. 
 case H'; clear H'. intros u0 H'.
 destruct H'. destruct H1.
 induction H1. induction H1. destruct H1.
 exists (t0[[u]]). split. 
 skip. split. 

(*
 unfold body in H1. case H1; clear H1.  
 intros L H1. apply lab_term_sub' with (L := L); intros;
 try apply term_to_lab_term; trivial.
 apply H1; trivial. skip. skip. split. skip. simpl.
 *)  


 Admitted.

Lemma SN_lab_2 : forall S t, lab_term S t -> SN lab_lex t -> SN lex (U_lab t).  
Proof.
 intros. 
Admitted.


(** In order to prove the Perpetuality Theorem, IE Property is considered as a hypothesis, but in a future work the a formalization of this point needs to be done. A sofisticated approach with the extention of the lex grammar is used in D. Kesner's paper, and our intent is following the same steps of the pencil and paper proof. 
*)

*)

Hypothesis IE_property : forall t u lv, body t -> term u-> 
                         SN lex u -> SN lex ((t ^^ u) // lv) -> SN lex ((t[u]) // lv).
