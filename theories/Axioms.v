Declare ML Module "z3ml".
Declare ML Module "euclid_plugin".

Require Export Sorts.
Require Export ConstructionRules.
Require Export DiagrammaticInferences.
Require Export MetricInferences.
Require Export TransferInferences.

(* Superposition *)

Require Export Program.Tactics.
Require Export Psatz.

Lemma conj_hyp : forall (P Q R : Prop), P -> (P /\ Q -> R) -> (Q -> R).
Proof.
  auto.
Qed.

Hint Resolve DiagrammaticInferences.intersection_circle_circle_2.
Hint Resolve DiagrammaticInferences.center_inside_circle.

Ltac elim_conj H := 
    repeat match type of H with
           | ?P /\ ?Q -> ?R => match goal with
                               | [H' : ?P |- _] => replace_hyp H (conj_hyp P Q R H' H)
                               | _ => let H' := fresh "EUCLID_IMPLICIT_ASSUMPTION" in evar (H' : P)
                               end
    end.

Ltac euclid_apply' rule name := 
    let lemma := fresh in
    generalize rule; intros lemma;
    repeat match type of lemma with
           | ?P /\ ?Q -> _ => elim_conj lemma
           | forall _ : ?T, _ => match goal with
                                 | [ H : ?T |- _ ] => specialize (lemma H)
                                 | _ => let H := fresh "EUCLID_IMPLICIT_ASSUMPTION" in assert (H : T); [ eauto 10; euclid_smt; shelve |  idtac ]
                                 end
           | exists _ : _, _ => let Hname := fresh "H" name in destruct lemma as [name Hname];
                                            match type of Hname with
                                            | _ /\ _ => destruct Hname
                                            end
           | _ /\ _ => destruct lemma
           end.

Tactic Notation "euclid_apply" constr(rule) "as" ident(name) :=
    euclid_apply' rule name.

Tactic Notation "euclid_apply" constr(rule) :=
    let name := fresh "x" in
    euclid_apply' rule name.