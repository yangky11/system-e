(*
Core tactics used to implement Euclid's reasoning patterns, such as 
applying an existing theorem (`euclid_apply`), proof by contradiction 
(`euclid_contradict`), and proof by case analysis (`euclid_case`).

They utilize `euclid_trivial`: a tactic that fills Euclid's reasoning gaps
using SMT solvers. It calls a tactic `euclid_smt` implemented in OCaml.
*)
Declare ML Module "z3ml".
Declare ML Module "euclid_plugin".

Require Export Sorts.
Require Export ConstructionRules.
Require Export DiagrammaticInferences.
Require Export MetricInferences.
Require Export TransferInferences.

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
           | ?P /\ ?Q => let Hname := fresh H in 
                         destruct H as [Hname H]
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
    |- exists _, _ => exfalso; eauto 10; euclid_smt; shelve
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
Ltac euclid_apply' rule name1 name2 name3 name4 name5 name6 name7 name8 := 
    let lemma := fresh in
    generalize rule; intros lemma;
    repeat match type of lemma with
           | ?P /\ ?Q -> _ => elim_conj lemma
           | ?T -> _ => match goal with
                        | [ H : T |- _ ] => specialize (lemma H)
                        | _ => euclid_trivial T
                        end
           | _ /\ _ => destruct_conj lemma
           | exists _ : _, _ => let Hname1 := fresh "H" name1 in 
                                destruct lemma as [name1 Hname1];
                                match type of Hname1 with
                                | _ /\ _ => destruct_conj Hname1
                                | exists _ : _, _ => let Hname2 := fresh Hname1 name2 in 
                                                     destruct Hname1 as [name2 Hname2];
                                                     match type of Hname2 with
                                                     | _ /\ _ => destruct_conj Hname2
                                                     | exists _ : _, _ => let Hname3 := fresh Hname2 name3 in
                                                                          destruct Hname2 as [name3 Hname3];
                                                                          match type of Hname3 with
                                                                          | _ /\ _ => destruct_conj Hname3
                                                                          | exists _ : _, _ =>  let Hname4 := fresh Hname3 name4 in
                                                                                                destruct Hname3 as [name4 Hname4];
                                                                                                match type of Hname4 with
                                                                                                | _ /\ _ => destruct_conj Hname4
                                                                                                | exists _ : _, _ => let Hname5 := fresh Hname4 name5 in
                                                                                                                     destruct Hname4 as [name5 Hname5];
                                                                                                                     match type of Hname5 with
                                                                                                                     | _ /\ _ => destruct_conj Hname5
                                                                                                                     | exists _ : _, _ => let Hname6 := fresh Hname5 name6 in
                                                                                                                                          destruct Hname5 as [name6 Hname6];
                                                                                                                                          match type of Hname6 with
                                                                                                                                          | _ /\ _ => destruct_conj Hname6
                                                                                                                                          | exists _ : _, _ => let Hname7 := fresh Hname6 name7 in
                                                                                                                                                               destruct Hname6 as [name7 Hname7];
                                                                                                                                                               match type of Hname7 with
                                                                                                                                                               | _ /\ _ => destruct_conj Hname7
                                                                                                                                                               | exists _ : _, _ => let Hname8 := fresh Hname7 name8 in
                                                                                                                                                                                    destruct Hname7 as [name8 Hname8];
                                                                                                                                                                                    match type of Hname8 with
                                                                                                                                                                                    | _ /\ _ => destruct_conj Hname8
                                                                                                                                                                                    | _ => idtac
                                                                                                                                                                                    end
                                                                                                                                                               | _ => idtac
                                                                                                                                                               end
                                                                                                                                          | _ => idtac
                                                                                                                                          end
                                                                                                                     | _ => idtac
                                                                                                                     end
                                                                                                | _ => idtac
                                                                                                end
                                                                          | _ => idtac
                                                                          end
                                                     | _ => idtac
                                                     end
                                | _ => idtac
                                end
           end.

(* apply an inference rule *)
Tactic Notation "euclid_apply" constr(rule) :=
    let name1 := fresh "x" in
    let name2 := fresh "y" in
    let name3 := fresh "z" in
    let name4 := fresh "u" in
    let name5 := fresh "v" in
    let name6 := fresh "w" in
    let name7 := fresh "p" in
    let name8 := fresh "q" in
    euclid_apply' rule name1 name2 name3 name4 name5 name6 name7 name8.

(* apply an inference rule and name the constructed object *)
Tactic Notation "euclid_apply" constr(rule) "as" ident(name1) :=
    let name2 := fresh "y" in
    let name3 := fresh "z" in
    let name4 := fresh "u" in
    let name5 := fresh "v" in
    let name6 := fresh "w" in
    let name7 := fresh "p" in
    let name8 := fresh "q" in
    euclid_apply' rule name1 name2 name3 name4 name5 name6 name7 name8.

Tactic Notation "euclid_apply" constr(rule) "as" ident(name1) ident(name2) :=
    let name3 := fresh "z" in
    let name4 := fresh "u" in
    let name5 := fresh "v" in
    let name6 := fresh "w" in
    let name7 := fresh "p" in
    let name8 := fresh "q" in
    euclid_apply' rule name1 name2 name3 name4 name5 name6 name7 name8.

Tactic Notation "euclid_apply" constr(rule) "as" ident(name1) ident(name2) ident(name3) :=
    let name4 := fresh "u" in
    let name5 := fresh "v" in
    let name6 := fresh "w" in
    let name7 := fresh "p" in
    let name8 := fresh "q" in
    euclid_apply' rule name1 name2 name3 name4 name5 name6 name7 name8.

Tactic Notation "euclid_apply" constr(rule) "as" ident(name1) ident(name2) ident(name3) ident(name4) :=
    let name5 := fresh "v" in
    let name6 := fresh "w" in
    let name7 := fresh "p" in
    let name8 := fresh "q" in
    euclid_apply' rule name1 name2 name3 name4 name5 name6 name7 name8.

Tactic Notation "euclid_apply" constr(rule) "as" ident(name1) ident(name2) ident(name3) ident(name4) ident(name5) :=
    let name6 := fresh "w" in
    let name7 := fresh "p" in
    let name8 := fresh "q" in
    euclid_apply' rule name1 name2 name3 name4 name5 name6 name7 name8.

Tactic Notation "euclid_apply" constr(rule) "as" ident(name1) ident(name2) ident(name3) ident(name4) ident(name5) ident(name6) :=
    let name7 := fresh "p" in
    let name8 := fresh "q" in
    euclid_apply' rule name1 name2 name3 name4 name5 name6 name7 name8.

Tactic Notation "euclid_apply" constr(rule) "as" ident(name1) ident(name2) ident(name3) ident(name4) ident(name5) ident(name6) ident(name7) :=
    let name8 := fresh "q" in
    euclid_apply' rule name1 name2 name3 name4 name5 name6 name7 name8.

Tactic Notation "euclid_apply" constr(rule) "as" ident(name1) ident(name2) ident(name3) ident(name4) ident(name5) ident(name6) ident(name7) ident(name8) :=
    euclid_apply' rule name1 name2 name3 name4 name5 name6 name7 name8.

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

(* prove multiple goals sequentially *)
Ltac euclid_split := match goal with
                     | |- ?G1 /\ ?G2 => assert (G1)
                     | _ => fail 999
                     end.