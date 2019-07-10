Declare ML Module "z3ml".
Declare ML Module "euclid_plugin".

Require Export Sorts.
Require Export ConstructionRules.
Require Export DiagrammaticInferences.
Require Export MetricInferences.
Require Export TransferInferences.
Require Export SuperpositionInferences.

Require Export Program.Tactics.
Require Export Psatz.

Lemma conj_hyp : forall (P Q R : Prop), P -> (P /\ Q -> R) -> (Q -> R).
Proof.
  auto.
Qed.

Hint Resolve DiagrammaticInferences.intersection_circle_circle_2.
Hint Resolve DiagrammaticInferences.center_inside_circle.

(* destruct the conjunction of multiple propositions *)
Ltac destruct_conj H := 
    repeat match type of H with
           | ?P /\ ?Q => let Hname := fresh H in destruct H as [Hname H]
           end.

(* intros while destructing the hypotheses *)
Ltac euclid_intros := 
    repeat match goal with
           | [ |- forall _ : ?T, _] => match T with 
                                       | ?P /\ ?Q => let Hname := fresh "H" in intro Hname; destruct_conj Hname
                                       | _ => intro
                                       end
           end.

Tactic Notation "euclid_trivial" := 
    match goal with 
    |- exists _, _ => fail 999
    | _ => eauto 10; euclid_smt; shelve
    end.

Tactic Notation "euclid_trivial" constr(fact) := 
    let H := fresh "SMT_VERIFIED_ASSUMPTION" in
    assert (H : fact); [euclid_trivial |  idtac ].

(*
Combine H : ?P /\ ?Q -> _ and H' : ?P into ?Q -> _
When there is not such H', call SMT to check if H' can be deduced.
*)
Ltac elim_conj H := 
    repeat match type of H with
           | ?P /\ ?Q -> ?R => match goal with
                               | [H' : P |- _] => replace_hyp H (conj_hyp P Q R H' H)
                               | _ => euclid_trivial P
                               end
    end.

(* apply an inference rule, using SMT to fill the holes *)
Ltac euclid_apply' rule name name2 := 
    let lemma := fresh in
    generalize rule; intros lemma;
    repeat match type of lemma with
           | ?P /\ ?Q -> _ => elim_conj lemma
           | ?T -> _ => match goal with
                        | [ H : T |- _ ] => specialize (lemma H)
                        | _ => euclid_trivial T
                        end
           | exists _ : _, _ => let Hname := fresh "H" name in 
                                destruct lemma as [name Hname];
                                match type of Hname with
                                | _ /\ _ => destruct_conj Hname
                                | exists _ : _, _ => let Hname2 := fresh Hname name2 in 
                                                     destruct Hname as [name2 Hname2];
                                                     match type of Hname2 with
                                                     | _ /\ _ => destruct_conj Hname2
                                                     | _ => idtac
                                                     end
                                | _ => idtac
                                end
           | _ /\ _ => destruct_conj lemma
           end.

(* apply an inference rule and name the constructed object *)
Tactic Notation "euclid_apply" constr(rule) "as" ident(name) :=
    let name2 := fresh "y" in
    euclid_apply' rule name name2.

Tactic Notation "euclid_apply" constr(rule) "as" ident(name) ident(name2) :=
    euclid_apply' rule name name2.

(* apply an inference rule *)
Tactic Notation "euclid_apply" constr(rule) :=
    let name := fresh "x" in
    let name2 := fresh "y" in
    euclid_apply' rule name name2.

Require Import Logic.Classical_Prop.
Require Import Logic.Classical_Pred_Type.

Ltac destruct_neg H := repeat match type of H with
                       | ~ (forall t : _, _) => apply not_all_ex_not in H; 
                                                let name := fresh t in 
                                                destruct H as [name H]
                       end.


(* proof by case analysis *)
Ltac euclid_case G :=  let phi := fresh "phi" in 
                       let not_phi := fresh "not_phi" in 
                       pose proof (classic G) as [phi | not_phi]; 
                       destruct_neg not_phi.

(* proof by contradiction *)
Ltac euclid_contradict := match goal with
                          | |- ?G => euclid_case G; try trivial; exfalso
                          end.

Tactic Notation "euclid_superposition" constr(rule) "as" ident(name) ident(name2) :=
    match goal with
               | |- exists _, _ => fail 999
               | |- _ => idtac
    end;
    euclid_apply rule as name name2.
