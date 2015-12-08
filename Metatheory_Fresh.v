(***************************************************************************
* Formalization of ES calculi						   *	
*									   *
* Tactics and lemmas about freshnes 					   *	
*									   *
* Arthur Chargu\u00e9raud, 2007                                            *
* Flávio L. C. de Moura, 2015						   *
***************************************************************************)

Set Implicit Arguments.
Require Import LibTactics List Metatheory_Var.
Require Import Morphisms.

(* ********************************************************************** *)
(** * Tactics for fresh and notin *)

Ltac notin_from_fresh_in_context :=
  repeat (match goal with H: fresh _ _ _ |- _ =>
    progress (simpl in H; destructs H) end).


Lemma notin_var_gen : forall E F,
  (forall x, x \notin E -> x \notin F) ->
  (var_gen E) \notin F.
Proof. intros. auto~ var_gen_spec. Qed.

Implicit Arguments notin_singleton_r    [x y].
Implicit Arguments notin_singleton_l    [x y].
Implicit Arguments notin_singleton_swap [x y].
Implicit Arguments notin_union_r  [x E F].
Implicit Arguments notin_union_r1 [x E F].
Implicit Arguments notin_union_r2 [x E F].
Implicit Arguments notin_union_l  [x E F].

(** Tactics to deal with notin.  *)

Ltac notin_solve_target_from x E H :=
  match type of H with 
  | x \notin E => constr:(H)
  | x \notin (?F \u ?G) =>  
     let H' :=
        match F with 
        | context [E] => constr:(notin_union_r1 H)
        | _ => match G with 
          | context [E] => constr:(notin_union_r2 H)
          | _ => fail 20
          end
        end in
     notin_solve_target_from x E H' 
  end.

Ltac notin_solve_target x E :=
  match goal with 
  | H: x \notin ?L |- _ =>
    match L with context[E] =>
      let F := notin_solve_target_from x E H in
      apply F 
    end
  | H: x <> ?y |- _ => 
     match E with {{y}} => 
       apply (notin_singleton_l H)
     end
  end.

Ltac notin_solve_one :=
  match goal with
  | |- ?x \notin {{?y}} => 
     apply notin_singleton_swap; 
     notin_solve_target y ({{x}}) 
  | |- ?x \notin ?E => 
    notin_solve_target x E
  end.

Ltac notin_simpl :=
  match goal with 
  | |- _ \notin (_ \u _) => apply notin_union_l; notin_simpl 
  | |- _ \notin ({}) => apply notin_empty; notin_simpl
  | |- ?x <> ?y => apply notin_singleton_r; notin_simpl
  | |- _ => idtac
  end.

Ltac notin_solve_false :=
  match goal with 
  | H: ?x \notin ?E |- _ =>
    match E with context[x] =>
      apply (@notin_same x); 
      let F := notin_solve_target_from x ({{x}}) H in
      apply F
    end 
  | H: ?x <> ?x |- _ => apply H; reflexivity
  end.

Ltac notin_false :=
  match goal with
  | |- False => notin_solve_false
  | _ => false; notin_solve_false
  end.

Ltac notin_solve :=
  notin_from_fresh_in_context;
  first [ notin_simpl; try notin_solve_one
        | notin_false ].


(***************************************************************************)
(** * Automation: hints to solve notin subgoals automatically. *)

Hint Extern 1 (_ \notin _) => notin_solve.
Hint Extern 1 (_ <> _ :> var) => notin_solve.
Hint Extern 1 (_ <> _ :> Var_as_OT.t) => notin_solve.
Hint Extern 1 ((_ \notin _) /\ _) => splits.


(***************************************************************************)
(** * Morphisms definitions *)
Lemma fresh_morphism_ : forall l k E1 E2, E1 [=] E2 -> fresh E1 k l -> fresh E2 k l.
Proof. 
  intros l. induction l ;  intro k ; induction k; intros E1 E2 Eeq fresh_E1; auto.
  specialize (IHk E1 E2 Eeq).
  simpl. split. destruct fresh_E1. VSD.fsetdec.
  simpls. destruct fresh_E1. apply IHl with (E1:=E1\u{{a}}). VSD.fsetdec. assumption.
Qed.

Instance fresh_morphism : Proper (VarSet.Equal ==> eq ==> eq ==> Basics.flip Basics.impl) fresh.
Proof.
  unfold Basics.flip, Basics.impl. intros E1 E2 Eeq k1 k2 eq_k l1 l2 eq_l fresh_E2.
  rewrite eq_k, eq_l. apply fresh_morphism_ with (E1:=E2). VSD.fsetdec.
  assumption.
Qed.



(* ********************************************************************** *)
(** * Tactics for fresh *)

Lemma fresh_union_r : forall xs L1 L2 n,
  fresh (L1 \u L2) n xs -> fresh L1 n xs /\ fresh L2 n xs.
Proof.
  induction xs ; simpl ; intros ; destruct n ; tryfalse* ; auto.
  destruct H. split ; split ; auto.
   forwards*: (@IHxs (L1 \u {{a}}) L2 n).
   rewrite union_comm.
   rewrite union_comm_assoc.
   rewrite* union_assoc.
  forwards*: (@IHxs L1 (L2 \u {{a}}) n).
   rewrite* union_assoc.
Qed.

Lemma fresh_union_r1 : forall xs L1 L2 n,
  fresh (L1 \u L2) n xs -> fresh L1 n xs.
Proof. intros. forwards*: fresh_union_r. Qed.

Lemma fresh_union_r2 : forall xs L1 L2 n,
  fresh (L1 \u L2) n xs -> fresh L2 n xs.
Proof. intros. forwards*: fresh_union_r. Qed.

Lemma fresh_union_l : forall xs L1 L2 n,
  fresh L1 n xs -> fresh L2 n xs -> fresh (L1 \u L2) n xs.
Proof.
  induction xs; simpl; intros; destruct n; tryfalse*. auto.
  destruct H. destruct H0. split~.
  forwards~ K: (@IHxs (L1 \u {{a}}) (L2 \u {{a}}) n). 
  rewrite <- (union_same {{a}}).
  rewrite union_assoc.
  rewrite <- (@union_assoc L1).
  rewrite (@union_comm L2).
  rewrite (@union_assoc L1).
  rewrite* <- union_assoc.
Qed.

Lemma fresh_empty : forall L n xs,
  fresh L n xs -> fresh {} n xs.
Proof.
  intros. rewrite <- (@union_empty_r L) in H.
  destruct* (fresh_union_r _ _ _ _ H).
Qed.

Lemma fresh_length : forall L n xs,
  fresh L n xs -> n = length xs.
Proof.
  intros. gen n L. induction xs; simpl; intros n L Fr;
    destruct n; tryfalse*. 
  auto.
  rewrite* <- (@IHxs n (L \u {{a}})).
Qed.

Lemma fresh_resize : forall L n xs,
  fresh L n xs -> forall m, m = n -> fresh L m xs.
Proof.
  introv Fr Eq. subst~.
Qed.

Lemma fresh_resize_length : forall L n xs,
  fresh L n xs -> fresh L (length xs) xs.
Proof.
  introv Fr. rewrite* <- (fresh_length _ _ _ Fr).
Qed.

Implicit Arguments fresh_union_r [xs L1 L2 n].
Implicit Arguments fresh_union_r1 [xs L1 L2 n].
Implicit Arguments fresh_union_r2 [xs L1 L2 n].
Implicit Arguments fresh_union_l [xs L1 L2 n].
Implicit Arguments fresh_empty  [L n xs].
Implicit Arguments fresh_length [L n xs].
Implicit Arguments fresh_resize [L n xs].
Implicit Arguments fresh_resize_length [L n xs].

Ltac fresh_solve_target_from E n xs H :=
  match type of H with 
  | fresh E n xs => constr:(H)
  | fresh E ?m xs => 
      match n with 
      | length xs => constr:(fresh_resize_length H) 
      | _ => 
         match goal with 
         | Eq: m = n |- _ => constr:(fresh_resize H _ (sym_eq Eq)) 
         | Eq: n = m |- _ => constr:(fresh_resize H _ Eq) 
         end
      end
  | fresh (?F \u ?G) ?m xs => 
     let H' :=
        match F with 
        | context [E] => constr:(fresh_union_r1 H)
        | _ => match G with 
          | context [E] => constr:(fresh_union_r2 H)
          | _ => fail 20
          end
        end in
     fresh_solve_target_from E n xs H' 
  end.

Ltac fresh_solve_target E n xs :=
  match goal with H: fresh ?L _ xs |- _ =>
    match L with context[E] =>
      let F := fresh_solve_target_from E n xs H in
      apply F 
    end
  end.

Ltac fresh_solve_one :=
  match goal with 
  | |- fresh ?E ?n ?xs =>   
    fresh_solve_target E n xs 
  | |- fresh {} ?n ?xs =>
    match goal with H: fresh ?F ?m xs |- _ =>
      apply (fresh_empty H);
      fresh_solve_target F n xs 
    end
  end.

Ltac fresh_simpl :=
  try match goal with |- fresh (_ \u _) _ _ =>
    apply fresh_union_l; fresh_simpl end.

Ltac fresh_solve_by_notins :=
  simpl; splits; try notin_solve.

Ltac fresh_solve :=
  fresh_simpl; 
  first [ fresh_solve_one 
        | fresh_solve_by_notins 
        | idtac ].


(***************************************************************************)
(** Automation: hints to solve "fresh" subgoals automatically. *)

Hint Extern 1 (fresh _ _ _) => fresh_solve.


