Set Warnings "-notation-overridden-parsing".
Add LoadPath "/Users/lubis/Documents/study/software_foundations".
Require Export Poly.
Require Export Lists.

Theorem silly1: forall n m o p: nat,
  n = m -> [n;o] = [n;p] -> [n;o] = [m;p]. 
Proof.
  intros n m o p eq1 eq2.
  rewrite <- eq1, eq2.
  reflexivity.
Qed.

Theorem silly1': forall n m o p: nat,
  n = m -> [n;o] = [n;p] -> [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  rewrite <- eq1. apply eq2.
Qed.

Theorem silly2: forall n m o p: nat,
  n = m ->
  (forall q r: nat, q = r -> [q;o] = [r;p]) ->
  [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  apply eq2, eq1.
Qed.

Theorem silly2a: forall n m: nat,
  (n,n) = (m,m) ->
  (forall q r: nat, (q,q) = (r,r) -> [q] = [r]) ->
  [n] = [m].
Proof.
  intros n m eq1 eq2.
  apply eq2, eq1.
Qed.

(* Page 93 Exercise *)

Theorem silly_ex:
  (forall n: nat, evenb n = true -> oddb (S n) = true) ->
  oddb 3 = true -> evenb 4 = true.
Proof.
  intros eq1 eq2. apply eq2.
Qed.

(* Exercise ends *)

Theorem silly3_firsttry: forall n: nat,
  true = (n =? 5) -> (S (S n)) =? 7 = true.
Proof.
  intros n H. symmetry.
  apply H.
Qed.

(* Page 94 Exercise *)


Theorem rev_exercise: forall l1 l2: list nat,
  l1 = rev l2 -> l2 = rev l1.
Proof.
  intros l1 l2 eq1. rewrite -> eq1. 
  symmetry. apply rev_involutive.
Qed.

(* Exercise ends *)

Example trans_eq_example: forall a b c d e f: nat,
  [a;b] = [c;d] -> 
  [c;d] = [e;f] ->
  [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  rewrite -> eq1, eq2. reflexivity.
Qed.
 
Theorem trans_eq: forall (X: Type) (n m o: X),
  n = m -> m = o -> n = o.
Proof.
  intros X n m o eq1 eq2. rewrite -> eq1, eq2. reflexivity.
Qed.

Example trans_eq_example': forall a b c d e f: nat,
  [a;b] = [c;d] ->
  [c;d] = [e;f] ->
  [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2. 
  apply trans_eq with (m:=[c;d]).
  - apply eq1.
  - apply eq2.
Qed.

(* Page 95 Exercise *)

Example trans_eq_exercise:
  forall n m o p: nat,
  m = (minustwo o) ->
  (n + p) = m ->
  (n + p) = (minustwo o).
Proof.
  intros n m o p eq1 eq2.
  apply trans_eq with (m:=m).
  - apply eq2.
  - apply eq1.
Qed.

(* Exercise Ends *)

Theorem S_injective: forall n m: nat,
  S n = S m -> n = m.
Proof.
  intros n m H1.
  assert (H2: n = pred (S n)).
    { reflexivity. }
  rewrite H2. rewrite H1. reflexivity.
Qed.

Theorem S_injective': forall n m: nat,
  S n = S m -> n = m.
Proof.
  intros n m H.
  injection H. intros Hnm. apply Hnm.
Qed.

Theorem injection_ex1:
  forall n m o: nat,
  [n;m] = [o;o] -> n = m.
Proof.
  intros n m o H.
  injection H. intros H1 H2.
  rewrite H1, H2. reflexivity.
Qed.

Theorem injection_ex2:
  forall n m: nat,
  [n] = [m] -> n = m.
Proof.
  intros n m H.
  injection H as Hnm. apply Hnm.
Qed.

(* Page 97 Exercise *)

Example injection_ex3: forall (X: Type) (x y z: X) (l j: list X),
  x :: y :: l = z :: j ->
  y :: l = x :: j ->
  x = y.
Proof.
  intros X x y z l j H1 H2. injection H2.
  intros H2a. intros H2b.
  symmetry. apply H2b.
Qed.

(* Exercise Ends *)

Theorem eqb_0_l: forall n: nat,
  0 =? n = true -> n = 0.
Proof.
  intros n.
  destruct n as [| n'] eqn:E.
  - intros H. reflexivity.
  - simpl. intros H. discriminate H.
Qed.

Theorem discriminate_ex1: forall n: nat,
  S n = O -> 2 + 2 = 5.
Proof.
  intros n contra. discriminate contra.
Qed.

Theorem discriminate_ex2: forall n m: nat,
  false = true -> [n] = [m].
Proof.
  intros n m contra. discriminate contra.
Qed.

(* Page 98 Exercise *)

Example discriminate_ex3:
  forall (X: Type) (x y z: X) (l j: list X),
  x :: y :: l = [] -> x = z.
Proof.
  intros X x y z l j contra. discriminate contra.
Qed.

(* Exercise ends *)

Theorem f_equal:
  forall (A B: Type) (f: A -> B) (x y: A),
  x = y -> f x = f y.
Proof.
  intros A B f x y eq.
  rewrite eq. reflexivity.
Qed.

Theorem S_inj: forall (n m: nat) (b: bool),
  (S n) =? (S m) = b -> n =? m = b.
Proof.
  intros n m b H. simpl in H. apply H.
Qed.

Theorem silly3': forall n: nat,
  (n =? 5 = true -> (S (S n)) =? 7 = true) ->
  true = (n =? 5) ->
  true = ((S (S n)) =? 7).
Proof.
  intros n eq H. symmetry in H. apply eq in H. symmetry in H.
  apply H.
Qed.

Theorem plus_n_n_injective:
  forall n m: nat, n + n = m + m -> n = m.
Proof.
  intros n. induction n as [| n'].
  - simpl. intros m. destruct m as [| m'].
    + reflexivity.
    + discriminate.
  - intros m. destruct m as [| m'].
    + discriminate.
    + intros eq. 
      rewrite <- plus_n_Sm in eq. rewrite <- plus_n_Sm in eq.
      apply S_injective in eq.
      simpl in eq. apply S_injective in eq.
      apply IHn' in eq.
      rewrite eq. reflexivity.
Qed.

Theorem double_injective_FAILED:
  forall n m: nat, double n = double m -> n = m.
Proof.
  intros n m. induction n as [| n'].
  - simpl. intros eq. destruct m as [| m'] eqn:E.
    + reflexivity.
    + discriminate eq.
  - intros eq. destruct m as [| m'] eqn:E.
    + discriminate eq.
    + apply f_equal. Abort.

Theorem double_injective:
  forall n m: nat, double n = double m -> n = m.
Proof.
  intros n. induction n as [| n'].
  - simpl. intros m. destruct m as [| m'] eqn:E.
    + reflexivity.
    + discriminate.
  - simpl.
    intros m eq.
    destruct m as [| m'] eqn:E.
    + simpl. discriminate.
    + apply f_equal. apply IHn'. simpl in eq. injection eq.
      intros H. apply H.
Qed.

(* Page 102 Exercise *)

Theorem eqb_true: forall n m: nat,
  n =? m = true -> n = m.
Proof.
  intros n. induction n as [| n' IHn'].
  - intros m. destruct m as [| m'].
    + reflexivity.
    + discriminate.
  - intros m. simpl. destruct m as [| m'].
    + discriminate.
    + intros eq. apply IHn' in eq. apply f_equal, eq.
Qed.

(* Exercise Ends *)

Theorem double_injective_take2_FAILED:
  forall n m: nat, double n = double m -> n = m.
Proof.
  intros n m. induction m as [| m'].
  - simpl. intros eq. destruct n as [| n'] eqn:E.
    + reflexivity.
    + discriminate eq.
  - intros eq. destruct n as [| n'] eqn:E.
    + discriminate.
    + apply f_equal.
Abort.

Theorem double_injective_take2:
  forall n m: nat, double n = double m -> n = m.
Proof.
  intros n m.
  generalize dependent n.
  induction m as [| m' IHm'].
  - simpl. intros n eq. destruct n as [| n'] eqn:E.
    + reflexivity.
    + discriminate.
  - simpl. intros n eq. destruct n as [| n'] eqn:E.
    + discriminate.
    + apply f_equal, IHm'.
      simpl in eq. injection eq.
      intros H. apply H.
Qed.

(* Page 104 Exercise *)

Theorem nth_error_after_last:
  forall (n: nat) (X: Type) (l: list X),
  length l = n -> nth_error l n = None.
Proof.
  intros n X l.
  generalize dependent n.
  induction l as [| x l' IHl'].
  - simpl. intros n H. reflexivity.
  - intros n. destruct n as [| n']. simpl.
    + discriminate.
    + simpl. intros eq. injection eq. 
      intros eq1. apply IHl' in eq1. apply eq1.
Qed.

(* Exercise Ends *)

Definition square n := n * n.

Lemma square_mult:
  forall n m, square (n * m) = square n * square m.
Proof.
  intros n m.
  unfold square.
  rewrite mult_assoc.
  assert (H: n * m * n = n * n * m).
    { rewrite mult_comm. apply mult_assoc. }
  rewrite H. rewrite mult_assoc. reflexivity.
Qed.

Definition foo (x: nat) := 5.

Fact silly_fact_1: forall m, foo m + 1 = foo (m + 1) + 1.
Proof.
  intros m. 
  simpl. 
  reflexivity.
Qed.

Definition sillyfun (n: nat) : bool :=
  if n =? 3 then false
  else if n =? 5 then false
  else false.

Theorem sillyfun_false: forall n: nat,
  sillyfun n = false.
Proof.
  intros n. unfold sillyfun.
  destruct (n =? 3) eqn:E1.
  - reflexivity.
  - destruct (n =? 5) eqn:E2.
    + reflexivity.
    + reflexivity.
Qed.

(* Page 107 Exercise *)


      
    

(* Exercise Ends *)
