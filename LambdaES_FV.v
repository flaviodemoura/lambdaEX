(***************************************************************************
* Formalization of ES calculi						   *		
*									   *
* Properties of free variables 		 				   *
*									   *
* Fabien Renaud, 2011							   *
* Flávio L. C. de Moura, 2015                                              * 
***************************************************************************)

Set Implicit Arguments.
Require Import  Metatheory LambdaES_Defs.

Lemma fv_open_ : forall t k x y, x<>y -> (x \in fv ({k~>pterm_fvar y}t )  <-> x \in fv t).
Proof.
  intro t; induction t. intros k x y H.  simpls.
  case_nat. simpls. split. intro H0.
  apply in_singleton in H0. contradiction.
  intro H0. apply in_empty in H0. contradiction.
  simpls. split. intro H0; assumption. intro H0; assumption.
  intros k x y H. simpls.
  split. intro H0; assumption. intro H0; assumption.
  intros k x y H. simpls. rewrite in_union. rewrite in_union.
  split. intro H0. destruct H0. left.
  generalize H0. apply IHt1; assumption.
  right. generalize H0.
  apply IHt2; assumption.
  intro H0. destruct H0. left.
  generalize H0. apply IHt1; assumption.
  right. generalize H0.
  apply IHt2; assumption.
  simpls. intros k x y.
  apply (IHt (S k) x y) ; assumption.
  simpls. intros k x y H.
  rewrite in_union. rewrite in_union.
  split. intro H0. destruct H0. left.
  generalize H0. apply IHt1; assumption.
  right. generalize H0.
  apply IHt2; assumption.
  intro H0. destruct H0.
  left. generalize H0.
  apply IHt1; assumption.
  right. generalize H0.
  apply IHt2; assumption.
  simpls. intros k x y.
  rewrite in_union. rewrite in_union. intro H.
  split. intro H0. destruct H0.
  left. generalize H0.
  apply IHt1; assumption.
  right. generalize H0.
  apply IHt2; assumption.
  intro H0. destruct H0.
  left. generalize H0.
  apply IHt1; assumption.
  right. generalize H0.
  apply IHt2; assumption.
Qed.


Lemma fv_open_in_neq : forall t x y, x<>y -> (x \in fv(t^y )  <-> x \in fv t).
Proof. intros. apply fv_open_. assumption. Qed.
    
Lemma notin_fv_close : forall t k x, x \notin fv (close_rec k x t).
Proof.
  intro. induction t ; intros ; simpl ; auto ; unfold close ; simpl. 
    case_var ; simpl ; auto.
Qed.
    
Lemma fv_in_or_notin : forall t x, x \in fv t \/ x \notin fv t.
Proof. 
  intros t x. induction t ; simpl ; auto.
    case_eq (x==v) ; intros. 
      rewrite e. left. rewrite in_singleton. reflexivity.
      right.  auto.
    destruct IHt1 ; destruct IHt2 ; auto.
      left. rewrite in_union. auto.
      left. rewrite in_union. auto.
      left. rewrite in_union. auto.
    destruct IHt1 ; destruct IHt2 ; auto.
      left. rewrite in_union. auto.
      left. rewrite in_union. auto.
      left. rewrite in_union. auto.
    destruct IHt1 ; destruct IHt2 ; auto.
      left. rewrite in_union. auto.
      left. rewrite in_union. auto.
      left. rewrite in_union. auto.
Qed.
    
Lemma fv_notin_open : forall t x z, x <> z -> (x \notin fv t  <-> x \notin fv (t^z)).
Proof. 
  intros t. unfold open. generalize 0 as k. induction t ; intros k x z neq ; split ; intros x_notin ; simpl ; auto.
    unfolds open ; simpls ; auto.
    compare k n ; intros. 
      rewrite e. case_nat ; simpl ; auto. case_nat ; simpl ; auto.
    rewrite notin_union. split.
      apply (IHt1 k x z) ; simpls ; auto.
      apply (IHt2 k x z) ; simpls ; auto.
    rewrite notin_union. split.
      apply (IHt1 k x z) ; simpls ; auto.
      apply (IHt2 k x z) ; simpls ; auto.
    apply (IHt (S k) x z) ; auto.
    apply (IHt (S k) x  z) ; auto.
    rewrite notin_union. split.
      apply (IHt1 (S k) x z) ; simpls ; auto.
      apply (IHt2 k x z) ; simpls ; auto.
    simpls. rewrite notin_union in *. destruct x_notin. split.
      apply (IHt1 (S k) x z) ; simpls ; auto.
      apply (IHt2 k x z) ; simpls ; auto.
    rewrite notin_union. split.
      apply (IHt1 (S k) x z) ; simpls ; auto.
      apply (IHt2 k x z) ; simpls ; auto.
    simpls. rewrite notin_union in *. destruct x_notin. split.
      apply (IHt1 (S k) x z) ; simpls ; auto.
      apply (IHt2 k x z) ; simpls ; auto.
Qed.

Lemma fv_open_subset : forall t k u, fv ({k~>u}t) << fv t \u fv u.
Proof.
  intros t. induction t ; intros k x ; try simpl_subset.
    induction n ; simpl ; case_nat ; simpl ; simpl_subset.
    simpl. specialize (IHt1 k x).  specialize (IHt2 k x). VSD.fsetdec.
    simpl. apply IHt.
    simpl. specialize (IHt1 (S k) x).  specialize (IHt2 k x). VSD.fsetdec.
    simpl. specialize (IHt1 (S k) x).  specialize (IHt2 k x). VSD.fsetdec.
Qed.

Lemma fv_open_notin : forall t x k, x \notin fv ({k ~>pterm_fvar x}t) -> fv ({k~>pterm_fvar x}t) = fv t.
Proof.
  intro t. induction t ; intros ; simpls ; auto.
    case_nat ; simpls ; try reflexivity.
      rewrite notin_singleton in H. contradiction H. reflexivity.
    rewrite IHt1 ; auto.    rewrite IHt2 ; auto.
    rewrite IHt1 ; auto.    rewrite IHt2 ; auto.
    rewrite IHt1 ; auto.    rewrite IHt2 ; auto.
Qed.
  

Lemma fv_in_open : forall t a x k, a \in fv ({k ~> pterm_fvar x}t) -> a \in fv t \u {{x}}.
Proof.
  intros t a x k H. assert (fv ({k ~> pterm_fvar x}t) << fv t \u {{x}}). apply fv_open_subset. VSD.fsetdec.
Qed.


Lemma fv_open_in : forall t x, x \in fv (t^x) -> 
                                     fv (t^x) [=] fv t \u {{x}}.
Proof. 
  intros t. unfold open.  generalize 0 as k. induction t ; intros k x x_in.
    (* bvar *)
    induction n ; unfold open ; simpl.
      rewrite union_empty_l. case_nat.
        reflexivity.
        simpls. case_nat.  contradiction (in_empty x_in).
      case_nat.
        simpl. rewrite union_empty_l. reflexivity.
        simpls. case_nat. 
           case_nat. contradiction (e). simpls.  contradiction (in_empty x_in).
           case_nat. contradiction (in_empty x_in).
    (* fvar *)
    unfolds open. simpls. apply in_singleton in x_in.
    rewrite x_in. rewrite union_same. reflexivity.
    (* app *)
    simpls.
    rewrite in_union in x_in.
    destruct x_in. 
      (* x \in fv ({k ~> pterm_fvar x}t1) *)
      specialize (IHt1 k x H) ; rewrite IHt1 ; unfold VarSet.Equal.
      intros a ; split ; intros a_in ; rewrite in_union in a_in ; destruct a_in ; try VSD.fsetdec .
        compare a x ; intros ; [ VSD.fsetdec | rewrite fv_open_ in H0 ; VSD.fsetdec].
        compare a x ; intros. VSD.fsetdec. rewrite in_union in *. destruct H0.
          rewrite fv_open_ ; [VSD.fsetdec | assumption].
          rewrite fv_open_ ; [VSD.fsetdec | assumption].
      (* x \in fv ({k ~> pterm_fvar x}t2) *)
      specialize (IHt2 k x H) ; rewrite IHt2 ; unfold VarSet.Equal.
      intros a ; split ; intros a_in ; rewrite in_union in a_in ; destruct a_in ; try VSD.fsetdec .
        compare a x ; intros ; [ VSD.fsetdec | rewrite fv_open_ in H0 ; VSD.fsetdec].
        compare a x ; intros. VSD.fsetdec. rewrite in_union in *. destruct H0.
          rewrite fv_open_ ; [VSD.fsetdec | assumption].
          rewrite fv_open_ ; [VSD.fsetdec | assumption].
    (* abs *)
    simpls. rewrite <- IHt with (k:= S k). reflexivity. assumption.
    (* Subs *)
    simpls.
    rewrite in_union in x_in.
    destruct x_in. 
      (* x \in fv ({S k ~> pterm_fvar x}t1) *)
      specialize (IHt1 (S k) x H) ; rewrite IHt1 ; unfold VarSet.Equal.
      intros a ; split ; intros a_in ; rewrite in_union in a_in ; destruct a_in ; try VSD.fsetdec .
        compare a x ; intros ; [ VSD.fsetdec | rewrite fv_open_ in H0 ; VSD.fsetdec].
        compare a x ; intros. VSD.fsetdec. rewrite in_union in *. destruct H0.
          rewrite fv_open_ ; [VSD.fsetdec | assumption].
          rewrite fv_open_ ; [VSD.fsetdec | assumption].
      (* x \in fv ({k ~> pterm_fvar x}t2) *)
      specialize (IHt2 k x H) ; rewrite IHt2 ; unfold VarSet.Equal.
      intros a ; split ; intros a_in ; rewrite in_union in a_in ; destruct a_in ; try VSD.fsetdec .
        compare a x ; intros ; [ VSD.fsetdec | rewrite fv_open_ in H0 ; VSD.fsetdec].
        compare a x ; intros. VSD.fsetdec. rewrite in_union in *. destruct H0.
          rewrite fv_open_ ; [VSD.fsetdec | assumption].
          rewrite fv_open_ ; [VSD.fsetdec | assumption].
    (* Subs' *)
    simpls.
    rewrite in_union in x_in.
    destruct x_in. 
      (* x \in fv ({S k ~> pterm_fvar x}t1) *)
      specialize (IHt1 (S k) x H) ; rewrite IHt1 ; unfold VarSet.Equal.
      intros a ; split ; intros a_in ; rewrite in_union in a_in ; destruct a_in ; try VSD.fsetdec .
        compare a x ; intros ; [ VSD.fsetdec | rewrite fv_open_ in H0 ; VSD.fsetdec].
        compare a x ; intros. VSD.fsetdec. rewrite in_union in *. destruct H0.
          rewrite fv_open_ ; [VSD.fsetdec | assumption].
          rewrite fv_open_ ; [VSD.fsetdec | assumption].
      (* x \in fv ({k ~> pterm_fvar x}t2) *)
      specialize (IHt2 k x H) ; rewrite IHt2 ; unfold VarSet.Equal.
      intros a ; split ; intros a_in ; rewrite in_union in a_in ; destruct a_in ; try VSD.fsetdec .
        compare a x ; intros ; [ VSD.fsetdec | rewrite fv_open_ in H0 ; VSD.fsetdec].
        compare a x ; intros. VSD.fsetdec. rewrite in_union in *. destruct H0.
          rewrite fv_open_ ; [VSD.fsetdec | assumption].
          rewrite fv_open_ ; [VSD.fsetdec | assumption].
Qed.

Lemma fv_open_both_notin :  forall t t' x, fv (t^x) [=] fv (t'^x) -> x \notin fv t -> x \notin fv t' -> fv t [=] fv t'.
Proof.
  intros. assert (x \in fv (t ^x) \/ x \notin fv (t^x)). apply fv_in_or_notin. destruct H2.
    (* x \in fv (t ^ x)  *)
    assert (x \in fv(t' ^x)). VSD.fsetdec.
    rewrite (fv_open_in t  H2) in H.   rewrite (fv_open_in t' H3) in H. 
    VSD.fsetdec.
    (* x \notin fv (t ^ x)  *)
    assert (x \notin fv(t' ^x)). VSD.fsetdec.
    unfolds open.
    rewrite (fv_open_notin t 0 H2) in H.  rewrite (fv_open_notin t' 0 H3) in H.
    assumption.
Qed.


Lemma fv_open_both_subset_notin :  forall t t' x, fv (t^x) << fv (t'^x) -> x \notin fv t -> x \notin fv t' -> fv t << fv t'.
Proof.
  intros. assert (x \in fv (t ^x) \/ x \notin fv (t^x)). apply fv_in_or_notin. destruct H2.
    (* x \in fv (t ^ x)  *)
    assert (x \in fv(t' ^x)). VSD.fsetdec.
    rewrite (fv_open_in t  H2) in H.   rewrite (fv_open_in t' H3) in H. 
    VSD.fsetdec.
    (* x \notin fv (t ^ x)  *)
    unfolds open.
    rewrite (fv_open_notin t 0 H2) in H.  rewrite fv_open_subset in H.
    simpl in H. VSD.fsetdec.
Qed.

Lemma fv_open_both_subset_context_notin :  forall t t' x y, x<> y -> fv (t^x) << fv (t'^x) \u {{y}} -> 
                             x \notin fv t -> x \notin fv t' -> fv t << fv t' \u {{y}}.
Proof.
  intros. assert (x \in fv (t ^x) \/ x \notin fv (t^x)). apply fv_in_or_notin. destruct H3.
    (* x \in fv (t ^ x)  *)
    assert (x \in fv(t' ^x)). VSD.fsetdec.
    rewrite (fv_open_in t  H3) in H0.   rewrite (fv_open_in t' H4) in H0. 
    VSD.fsetdec.
    (* x \notin fv (t ^ x)  *)
    unfolds open.
    rewrite (fv_open_notin t 0 H3) in H0.  rewrite fv_open_subset in H0.
    simpl in H0. VSD.fsetdec.
Qed.



Lemma fv_open_both_notin_open :  forall t t' x, fv (t^x) [=] fv (t'^x) -> x \notin fv (t^x) -> 
               x \notin fv (t'^x) -> fv t [=] fv t'.
Proof. intros. unfolds open. rewrite  fv_open_notin in H ; rewrite  fv_open_notin in H ; assumption. Qed.


Lemma fv_close : forall t k x, fv (close_rec k x t) [=] ((fv t) \rem x).
Proof.
  intro t. induction t ; intros k x ; simpl ; try VSD.fsetdec.
    case_var ; simpls ; VSD.fsetdec.
    rewrite IHt2. rewrite IHt1. VSD.fsetdec.
    apply IHt.
    rewrite IHt2. rewrite IHt1. VSD.fsetdec.
    rewrite IHt2. rewrite IHt1. VSD.fsetdec.
Qed.


Lemma fv_close' : forall t k x, x \notin fv (close_rec k x t).
Proof.
  intro t. induction t ; intros k x ; simpl ; try VSD.fsetdec.
    case_var ; simpls ; VSD.fsetdec.
    apply notin_union. split.
    apply IHt1. apply IHt2.
    apply IHt. 
    apply notin_union. split.
    apply IHt1. apply IHt2.
    apply notin_union. split.
    apply IHt1. apply IHt2.
Qed.



