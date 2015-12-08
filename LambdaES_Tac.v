(***************************************************************************
* Formalization of ES calculi						   *		
*									   *
* Tactics specific for terms with explicit substitutions		   *
*									   *
* St\u00e9phane Zimmermann                                                 *  
* Flávio L. C. de Moura, 2015						   *
***************************************************************************)

Require Import LambdaES_Defs.

(* Stupid tactic for stupid hypothesis *)
Ltac elim_zero_one :=
match goal with
| H : 0 = 1 |- _ => 
  let Hfresh := fresh H in
  assert (0 = 1 -> False) as Hfresh by omega ; elim Hfresh ; auto
| H : 1 = 0 |- _ => 
  let Hfresh := fresh H in
  assert (1 = 0 -> False) as Hfresh by omega ; elim Hfresh ; auto
| H : 1 = 0 |- _ => 
  let Hfresh := fresh H in
  assert (1 = 0 -> False) as Hfresh by omega ; elim Hfresh ; auto
end.

Ltac stupid_arith :=
match goal with
| H : 0 = 1 |- _ => 
  let Hfresh := fresh H in
  let T := type of H in
  assert (T -> False) as Hfresh by omega ; elim Hfresh ; auto
end.

Ltac elim_stupid H :=
  let typeH := type of H in
  let Hfresh := fresh H in
  try (assert (typeH -> False) as Hfresh by (try omega ; intuition) ; elim Hfresh ; assumption).

Ltac stupid_hyp :=
match goal with
| H : _ |- _ =>  elim_stupid H
end.


(** Performs an induction on the term t and basic test to solve the cases *)
Ltac easy_pterm_induction t Prefix Tac :=
  match (type of t)  with
  | pterm => induction t as [| |? IHt|? IHt1 ? IHt2|? IHt1 ? IHt2] ; 
      intros ; simpl ; try (Prefix ; solve[
            stupid_hyp
          | reflexivity
          | try rewrite IHt ; auto ; try omega
          | try rewrite IHt1 ; try rewrite IHt2 ; auto ; try omega
          | try rewrite <-IHt ; auto ; try omega
          | try rewrite <-IHt1 ; try rewrite <-IHt2 ; auto ; try omega
          | Tac
        ])
  end.

(** Notations to call easy_pterm_induction with prefixing or special tactic options *)
Tactic Notation "basic_pterm_induction" constr(t) "using" tactic(T) :=
easy_pterm_induction t idtac T.
Tactic Notation "basic_pterm_induction" constr(t) :=
easy_pterm_induction t idtac idtac.
Tactic Notation "basic_pterm_induction" constr(t) "prefixed_by" tactic(Prefix):=
easy_pterm_induction t Prefix idtac.
Tactic Notation "basic_pterm_induction" constr(t) "prefixed_by" tactic(Prefix) "using" tactic(T):=
easy_pterm_induction t Prefix T.

