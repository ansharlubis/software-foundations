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

Fixpoint In {A: Type} (x: A) (l: list A): Prop :=
  match l with
  | [] => False
  | x' :: l' => x' = x \/ In x l'
  end.

Example In_example_1: In 4 [1;2;3;4;5].
Proof.
  simpl. right. right. right. left. reflexivity.
Qed.

Example In_example_2:
  forall n, In n [2;4] -> exists n', n = 2 * n'.
Proof.
  simpl.
  intros n [H | [H | ]].
  - exists 1. rewrite <- H. reflexivity.
  - exists 2. rewrite <- H. reflexivity.
  - exfalso. apply H.
Qed.

Lemma In_map:
  forall (A B: Type) (f: A -> B) (l: list A) (x: A),
  In x l -> In (f x) (map f l).
Proof.
  intros A B f l x.
  induction l as [| x' l' IHl'].
  - simpl. intros H. apply H.
  - simpl. intros [H | H].
    + rewrite H. left. reflexivity.
    + right. apply IHl'. apply H.
Qed.

(* Page 126~ Exercise *)

Lemma In_map_iff: 
  forall (A B: Type) (f: A -> B) (l: list A) (y: B),
  In y (map f l) <-> exists x, f x = y /\ In x l.
Proof.
  intros A B f l y. split.
  - induction l as [| n' l' IHl'].
    + simpl. intros HF. exfalso. apply HF.
    + simpl. intros H. destruct H.
      * exists n'. split.
        { apply H. }
        { left. reflexivity. }
      * apply IHl' in H. destruct H.
        exists x. destruct H. split.
        { apply H. }
        { right. apply H0. }
  - induction l as [| n' l' IHl'].
    + simpl. intros H. destruct H. 
      destruct H. apply H0.
    + simpl. intros H. destruct H. destruct H.
      destruct H0.
      * rewrite H0. left. apply H.
      * right. apply IHl'. exists x. split.
        { apply H. }
        { apply H0. }
Qed.

Lemma In_app_iff: forall A l l' (a: A),
  In a (l ++ l') <-> In a l \/ In a l'.
Proof.
  intros A l l' a. split.
  - induction l as [| n t IHt].
    + simpl. intros H. right. apply H.
    + simpl. intros H. destruct H.
      * left. left. apply H.
      * apply IHt in H. destruct H.
        { left. right. apply H. }
        { right. apply H. }
  - induction l as [| n t IHt].
    + simpl. intros H. destruct H.
      * exfalso. apply H.
      * apply H.
    + simpl. intros [[H | H] | H]. 
      * left. apply H.
      * right. apply IHt. left. apply H.
      * right. apply IHt. right. apply H.
Qed.

Fixpoint All {T: Type} (P: T -> Prop) (l: list T) : Prop :=
  match l with
  | [] => True
  | h :: t =>  P h /\ All P t
  end.

Lemma All_In:
  forall T (P: T -> Prop) (l: list T), (forall x, In x l -> P x) <-> All P l.
Proof.
  intros T P. split.
  - induction l as [| n' l' IHl'].
    + intros H. simpl. reflexivity.
    + simpl. intros H. split.
      * apply H. left. reflexivity.
      * apply IHl'. intros x. intros H'. apply H.
        right. apply H'.
  - induction l as [| n' l' IHl'].
    + simpl. intros H1. intros H2. intros H3. 
      destruct H3.
    + simpl. intros [H1 H2].
      intros x. intros H. destruct H.
      * rewrite H in H1. apply H1.
      * apply IHl'. 
        { apply H2. }
        { apply H. }
Qed.

Definition combine_odd_even (Podd Peven: nat -> Prop) : nat -> Prop :=
  fun (n: nat) => if oddb n then Podd n else Peven n.

Theorem combine_odd_even_intro:
  forall (Podd Peven: nat -> Prop) (n: nat),
  (oddb n = true -> Podd n) -> 
  (oddb n = false ->
  Peven n) -> combine_odd_even Podd Peven n.
Proof.
  intros Podd Peven n. intros H1 H2.
  unfold combine_odd_even. destruct (oddb n) eqn:En.
  - apply H1. reflexivity.
  - apply H2. reflexivity.
Qed.

Theorem combine_odd_even_elim_odd:
  forall (Podd Peven: nat -> Prop) (n: nat),
  combine_odd_even Podd Peven n ->
  oddb n = true -> 
  Podd n.
Proof.
  intros Podd Peven n. intros H1 H2.
  unfold combine_odd_even in H1.
  rewrite H2 in H1. apply H1.
Qed.

Theorem combine_odd_even_elim_even:
  forall (Podd Peven: nat -> Prop) (n: nat),
  combine_odd_even Podd Peven n ->
  oddb n = false ->
  Peven n.
Proof.
  intros Podd Peven n. intros H1 H2.
  unfold combine_odd_even in H1. rewrite H2 in H1.
  apply H1.
Qed.

(* Exercise Ends *)

Check plus_comm.

Lemma plus_comm3_take2:
  forall x y z, x + (y + z) = (z + y) + x.
Proof.
  intros x y z.
  rewrite plus_comm.
  assert (H: y + z = z + y).
    { rewrite plus_comm. reflexivity. }
  rewrite H. reflexivity.
Qed.

Lemma plus_comm3_take3:
  forall x y z, x + (y + z) = (z + y) + x.
Proof.
  intros x y z.
  rewrite plus_comm.
  rewrite (plus_comm y z ).
  reflexivity.
Qed.

Lemma in_not_nil:
  forall A (x: A) (l: list A), In x l -> l <> [].
Proof.
  intros A x l H. unfold not. intros Hl. destruct l.
  - simpl in H. destruct H.
  - discriminate Hl.
Qed.


Lemma in_not_nil_42_take2:
  forall l: list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply (in_not_nil nat 42).
  apply H.
Qed.

Lemma in_not_nil_42_take3:
  forall l: list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply (in_not_nil _ _ _ H).
Qed.


Example lemma_application_ex:
  forall {n: nat} {ns: list nat}, In n (map (fun m => m * 0) ns) -> n = 0.
Proof.
  intros n ns H.
  destruct (proj1 _ _ (In_map_iff _ _ _ _ _) H) as [m [Hm _]].
Abort.

Example function_equality_ex1:
  (fun x => 3 + x) = (fun x => (pred 4) + x).
Proof. reflexivity. Qed.

Example function_equality_ex2:
  (fun x => plus x 1) = (fun x => plus 1 x).
Proof. Abort.

Axiom functional_extensionality:
  forall {X Y: Type} {f g: X -> Y},
  (forall (x: X), f x = g x) -> f = g.

Example function_equality_ex2:
  (fun x => plus x 1) = (fun x => plus 1 x).
Proof.
  apply functional_extensionality. intros x.
  apply plus_comm.
Qed.

Print Assumptions function_equality_ex2.

(* Page 132 Exercise *)

Fixpoint rev_append {X} (l1 l2: list X) : list X :=
  match l1 with
  | [] => l2
  | x :: l1' => rev_append l1'(x :: l2)
  end.

Definition tr_rev {X} (l: list X) : list X :=
  rev_append l [].


(* Exercise Ends *)


Theorem evenb_double: forall k,
  evenb (double k) = true.
Proof.
  intros k. induction k as [| k' IHk'].
  - reflexivity.
  - simpl. apply IHk'.
Qed.

