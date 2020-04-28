Set Warnings "-notation-overridden-parsing".
Add LoadPath "/Users/lubis/Documents/study/software_foundations".
Require Export Tactics.

Check 3 = 3.
(* ===> Prop *)

Check forall n m : nat, n + m = m + n.
(* ===> Prop *)

Definition plus_fact : Prop := 2 + 2 = 4.
Check plus_fact.

Theorem plus_fact_is_true :
  plus_fact.
Proof. reflexivity. Qed.

Definition is_three (n: nat) : Prop :=
  n = 3.
Check is_three.

Definition injective {A B} (f: A -> B) :=
  forall x y: A, f x = f y -> x = y.

Lemma succ_inj: injective S.
Proof.
  unfold injective. intros n m H.
  inversion H. reflexivity.
Qed.

Check @eq.

Example and_example: 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  split.
  - reflexivity.
  - reflexivity.
Qed.

Lemma and_intro:
  forall A B: Prop, 
  A -> B -> A /\ B.
Proof.
  intros A B HA HB. split.
  - apply HA.
  - apply HB.
Qed.

Example and_example': 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  apply and_intro.
  - reflexivity.
  - reflexivity.
Qed.

(* Page 115 Exercise *)

Example and_exercise:
  forall n m: nat, n + m = 0 -> n = 0 /\ m = 0.
Proof.
  intros n m eq. apply and_intro.
  - induction n as [| n' IHn'].
    + reflexivity.
    + discriminate.
  - induction m as [| m' IHm'].
    + reflexivity.
    + rewrite plus_comm in eq. inversion eq.
Qed.

Example and_exercise':
  forall n m: nat, n + m = 0 -> n = 0 /\ m = 0.
Proof.
  intros n m eq. apply and_intro.
  - destruct n as [| n'].
    + reflexivity.
    + discriminate.
  - destruct m as [| m'].
    + reflexivity.
    + rewrite plus_comm in eq. discriminate.
Qed.

(* Exercise Ends *)

Lemma and_example2:
  forall n m: nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros n m H.
  destruct H as [HA HB].
  rewrite HA. rewrite HB.
  reflexivity.
Qed.

Lemma and_example3:
  forall n m: nat, n + m = 0 -> n * m = 0.
Proof.
  intros n m H.
  assert (H': n = 0 /\ m = 0).
    { apply and_exercise. apply H. }
  destruct H' as [Hn Hm].
  rewrite Hn. rewrite Hm. reflexivity.
Qed.

Lemma proj1:
  forall P Q: Prop, P /\ Q -> P.
Proof.
  intros P Q [HP HQ].
  apply HP.
Qed.

(* Page 117 Exercise *)

Lemma proj2:
  forall P Q: Prop, P /\ Q -> Q.
Proof.
  intros P Q [HP HQ].
  apply HQ.
Qed.

(* Exercise Ends *)

Theorem and_commut:
  forall P Q: Prop, P /\ Q -> Q /\ P.
Proof.
  intros P Q [HP HQ].
  split. 
  - apply HQ.
  - apply HP.
Qed.

(* Page 118 Exercise *) 

Theorem and_assoc : forall P Q R : Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R [HP [HQ HR]].
  split.
  - split.
    + apply HP.
    + apply HQ.
  - apply HR.
Qed.

(* Exercise Ends *)

Lemma or_example :
  forall n m : nat, n = 0 \/ m = 0 -> n * m = 0.
Proof.
  (* This pattern implicitly does case analysis on
     [n = 0 \/ m = 0] *)
  intros n m [Hn | Hm].
  - (* Here, [n = 0] *)
    rewrite Hn. reflexivity.
  - (* Here, [m = 0] *)
    rewrite Hm. rewrite <- mult_n_O.
    reflexivity.
Qed.

Lemma or_intro: forall A B: Prop, A -> A \/ B.
Proof.
  intros A B HA.
  left.
  apply HA.
Qed.

Lemma zero_or_succ:
  forall n: nat, n = 0 \/ n = S (pred n).
Proof.
  intros n. destruct n as [| n'].
  - left. reflexivity.
  - right. reflexivity.
Qed.

(* Page 118 Exercise *)

Lemma mult_eq_0:
  forall n m, n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros n m eq.
  destruct n as [| n'].
  - left. reflexivity.
  - right. destruct m as [| m'].
    + reflexivity.
    + discriminate.
Qed.

Theorem or_commut:
  forall P Q: Prop, P \/ Q -> Q \/ P.
Proof.
  intros P Q [HP | HQ].
  - right. apply HP.
  - left. apply HQ.
Qed.

(* Exercise Ends *)

Module MyNot.

Definition not (P: Prop) :=  P -> False.

Notation "~ x" := (not x): type_scope.

End MyNot.

(* Page 119 Exercise *)

Theorem ex_falso_quodlibet: forall P: Prop,
  False -> P.
Proof.
  intros P contra.
  destruct contra.
Qed.

Fact not_implies_our_not: forall P: Prop,
  ~ P -> (forall Q:Prop, P -> Q).
Proof.
  intros P NP. unfold not in NP.
  intros Q. intros HP. apply NP in HP.
  destruct HP.
Qed.

(* Exercise Ends *)

Theorem zero_not_one: 0 <> 1.
Proof.
  unfold not. intros contra.
  discriminate.
Qed.

Theorem not_False:
  ~ False.
Proof.
  unfold not. intros H. destruct H.
Qed.

Theorem contradiction_implies_anything:
  forall P Q: Prop, (P /\ ~ P) -> Q.
Proof.
  intros P Q [HP HNA]. unfold not in HNA.
  apply HNA in HP. destruct HP.
Qed.

Theorem double_neg: forall P: Prop,
  P -> ~(~ P).
Proof.
  intros P H. unfold not. intros G.
  apply G. apply H.
Qed.

(* Page 120~ Exercise *)

Theorem contrapositive: forall P Q: Prop,
  (P -> Q) -> (~Q -> ~P).
Proof.
  intros P Q HA HNQ.
  unfold not in HNQ. unfold not.
  intros H. apply HA in H. apply HNQ in H.
  destruct H.
Qed.

Theorem not_both_true_and_false:
  forall P: Prop, ~ (P /\ ~P).
Proof.
  intros P. unfold not.
  intros [HP HN].
  apply HN in HP.
  destruct HP.
Qed.

(* Exercise Ends *)

Theorem not_true_is_false:
  forall b: bool, b <> true -> b = false.
Proof.
  intros b H.
  destruct b.
  - unfold not in H. exfalso. apply H. reflexivity.
  - reflexivity.
Qed.

Theorem not_true_is_false':
  forall b: bool, b <> true -> b = false.
Proof.
  intros b H. destruct b.
  - unfold not in H. apply ex_falso_quodlibet.
    apply H. reflexivity.
  - reflexivity.
Qed.

Lemma True_is_true: True.
Proof.
  apply I.
Qed.

Module MyIff.

Definition iff (P Q: Prop) := (P -> Q) /\ (Q -> P).

Notation "P <-> Q" := (iff P Q)
                      (at level 95, no associativity) : type_scope.

End MyIff.

Theorem iff_sym:
  forall P Q: Prop, (P <-> Q) -> (Q <-> P).
Proof.
  intros P Q.  intros [HPQ HQP].
  split.
  - apply HQP.
  - apply HPQ.
Qed.

Lemma not_true_iff_false:
  forall b, b <> true <-> b = false.
Proof.
  intros b. split.
  - apply not_true_is_false.
  - intros H. rewrite H. intros H'. discriminate H'.
Qed.

(* Page 122 Exercise *)

Theorem iff_refl:
  forall P: Prop, P <-> P.
Proof.
  intros P. split.
  - intros H. apply H.
  - intros H. apply H.
Qed.

Theorem iff_trans:
  forall P Q R: Prop, 
  (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
  intros P Q R. intros H1 H2.
  destruct H1. destruct H2. split.
  - intros H3. apply H1. apply H. apply H3.
  - intros H3. apply H0. apply H2. apply H3.
Qed.

Theorem or_distributes_over_and: forall P Q R: Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R.
  split.
  - intros [HP | HQR].
    + split.
      * left. apply HP.
      * left. apply HP.
    + destruct HQR. split.
      * right. apply H.
      * right. apply H0.
  - intros [HPQ HPR].
    destruct HPQ.
    + left. apply H.
    + destruct HPR.
      * left. apply H0.
      * right. split. apply H. apply H0.
Qed.

(* Exercise Ends *)

From Coq Require Import Setoids.Setoid.

Lemma mult_0: forall n m,
  n * m = 0 <-> n = 0 \/ m = 0.
Proof.
  split.
  - apply mult_eq_0.
  - apply or_example.
Qed.

Lemma or_assoc: forall P Q R: Prop,
  P \/ (Q \/ R) <-> (P \/ Q) \/ R.
Proof.
  intros P Q R. split.
  - intros [H | [H | H]].
    + left. left. apply H.
    + left. right. apply H.
    + right. apply H.
  - intros [[H | H] | H].
    + left. apply H.
    + right. left. apply H.
    + right. right. apply H.
Qed.

Lemma mult_0_3:
  forall n m p, n * m * p = 0 <-> n = 0 \/ m = 0 \/ p = 0.
Proof.
  intros n m p.
  rewrite mult_0. rewrite mult_0. rewrite or_assoc.
  reflexivity.
Qed.

Lemma apply_iff_example:
  forall n m: nat, n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros n m H. apply mult_0. apply H.
Qed.

Lemma four_is_even: exists n: nat, 4 = n + n.
Proof.
  exists 2. reflexivity.
Qed.

Theorem exists_example_2: forall n,
  (exists m, n = 4 + m) -> (exists o, n = 2 + o).
Proof.
  intros n. intros [m Hm]. exists (2 + m).
  apply Hm.
Qed.

(* Page 124 Exercise *)

Theorem dist_not_exists:
  forall (X: Type) (P: X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
  intros X P. intros H.
  unfold not. intros H'.
  destruct H' as [x E]. apply E. apply H.
Qed.

Theorem dist_exists_or:
  forall (X: Type) (P Q: X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  intros X P Q. split.
  - intros H. destruct H. destruct H.
    + left. exists x. apply H.
    + right. exists x. apply H.
  - intros H. destruct H.
    + destruct H. exists x. left. apply H.
    + destruct H. exists x. right. apply H.
Qed.

(* Exercise Ends *)

