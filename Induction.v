Add LoadPath "/Users/lubis/Documents/study/software_foundations".
Require Import Basics.

Theorem plus_n_O_firsttry:
  forall n: nat, n = n + 0.
Proof. intros n. simpl. Abort.

Theorem plus_n_O_secondtry:
  forall n: nat, n = n + 0.
Proof. 
  intros n. destruct n as [| n'] eqn:E.
  - reflexivity.
  - simpl. Abort.

Theorem plus_n_O:
  forall n: nat, n = n + 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite <- IHn'. reflexivity.
Qed.

Theorem minus_diag: 
  forall n: nat, minus n n = 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem mult_0_r:
  forall n: nat, n * 0 = 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem plus_n_Sm:
  forall n m: nat, S (n + m) = n + (S m).
Proof.
  intros n m.
  induction n as [| n' IHn'].
  - destruct m as [| m'] eqn:Em.
    + reflexivity.
    + simpl. reflexivity.
  - simpl.
    rewrite -> IHn'.
    reflexivity.
Qed.

Theorem plus_comm:
  forall n m: nat, n + m = m + n.
Proof.
  intros n m.
  induction n as [| n' IHn'].
  - rewrite -> plus_O_n. 
    rewrite <- plus_n_O. 
    reflexivity.
  - simpl. 
    rewrite -> IHn'. 
    rewrite -> plus_n_Sm.
    reflexivity.
Qed.

Theorem plus_assoc:
  forall n m p: nat, n + (m + p) = (n + m) + p.
Proof.
  intros n m p.
  induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

Fixpoint double (n:nat) : nat :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma double_plus:
  forall n: nat, double n = n + n.
Proof.
  intros n. induction n as [| n IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'.
    rewrite -> plus_n_Sm.
    reflexivity.
Qed.

Fixpoint evenb (n:nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => evenb n'
  end.

Lemma negb_negb_bool:
  forall b: bool, negb (negb b) = b.
Proof.
  intros b. destruct b eqn:Eb.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Theorem evenb_S:
  forall n: nat, evenb (S n) = negb (evenb n).
Proof.
  intros n. induction n as [| n' IHn'].
  - simpl. reflexivity.
  - rewrite -> IHn'.
    simpl. rewrite -> negb_negb_bool.
    reflexivity.
Qed.

(* Destruct only split the proposition into the possible
   cases for that type, while induction assumes the proposition
   holds for smaller sizes. *)

Theorem mult_0_plus':
  forall n m: nat, (0 + n) * m = n * m.
Proof.
  intros n m.
  assert (H: 0 + n = n).
    { reflexivity. }
  rewrite -> H.
  reflexivity.
Qed.

Theorem plus_rearrange_firsttry:
  forall n m p q: nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  rewrite -> plus_comm.
Abort.

Theorem plus_rearrange:
  forall n m p q: nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: n + m = m + n).
    { rewrite -> plus_comm. reflexivity. }
  rewrite -> H.
  reflexivity.
Qed.

(* Exercise. Page 46 *)

Theorem plus_swap:
  forall n m p: nat, n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  rewrite -> plus_assoc.
  assert (H: n + m = m + n).
    { rewrite -> plus_comm. reflexivity. }
  rewrite -> H.
  rewrite <- plus_assoc.
  reflexivity.
Qed.

Theorem plus_swap':
  forall n m p: nat, n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  rewrite -> plus_assoc.
  replace (n + m) with (m + n).
  - rewrite <- plus_assoc. reflexivity.
  - rewrite -> plus_comm. reflexivity.
Qed.

Theorem mult_m_Sn:
  forall n m: nat, m * S n = m + m * n.
Proof.
  intros n m.
  induction m as [| m' IHm'].
  - reflexivity.
  - simpl. rewrite -> IHm'.
    rewrite plus_swap. reflexivity.
Qed.
 
Theorem mult_comm:
  forall m n: nat, m * n = n * m.
Proof.
  intros m n. induction n as [| n' IHn'].
  - rewrite -> mult_0_r. reflexivity.
  - simpl. rewrite <- IHn'.
    rewrite mult_m_Sn.
    reflexivity.
Qed.

Theorem lab_refl:
  forall n: nat, true = (n <=? n).
Proof.
  intros n. induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem zero_nbeq_S:
  forall n: nat, 0 =? (S n) = false.
Proof.
  intros n. simpl. reflexivity.
Qed.

Theorem andb_false_r:
  forall b: bool, andb b false = false.
Proof.
  intros b. destruct b eqn:Eb.
  - reflexivity.
  - reflexivity.
Qed.

Theorem plus_ble_compat_l:
  forall n m p: nat, n <=? m = true -> (p + n) <=? (p + m) = true.
Proof.
  intros n m p.
  intros H.
  induction p as [| p' IHp'].
  - simpl. rewrite -> H. reflexivity.
  - simpl. rewrite -> IHp'. reflexivity.
Qed.

Theorem mult_1_l:
  forall n: nat, 1 * n = n.
Proof.
  intros n. simpl. rewrite <- plus_n_O. reflexivity.
Qed.

Theorem all3_spec:
  forall b c: bool,
  orb (andb b c) (orb (negb b) (negb c)) = true.
Proof.
  intros b c.
  destruct b eqn:Eb.
  - destruct c eqn:Ec.
    + reflexivity.
    + reflexivity.
  - destruct c eqn:Ec.
    + reflexivity.
    + reflexivity.
Qed.

Theorem mult_plus_distr_r:
  forall n m p: nat,
  (n + m) * p =  (n * p) + (m * p).
Proof.
  intros n m p.
  induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. rewrite -> plus_assoc. reflexivity.
Qed.

Theorem mult_assoc:
  forall n m p: nat, n * (m * p) = (n * m) * p.
Proof.
  intros n m p.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'. rewrite <- mult_plus_distr_r.
    reflexivity.
Qed.
    
Theorem eqb_refl: forall n: nat, true = (n =? n).
Proof.
  intros n. induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem bin_to_nat_pres_incr:
  forall b: bin, bin_to_nat (incr b) = S (bin_to_nat b).
Proof.
  intros b.
  induction b as [|x'|y' IHb'].
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. rewrite -> IHb'.
    replace (S (bin_to_nat y') + 0) with (S (bin_to_nat y')).
    replace (S (S (bin_to_nat y' + (bin_to_nat y' + 0)))) with
            (S (bin_to_nat y') + S (bin_to_nat y')).
    reflexivity.
    assert (H1: bin_to_nat y' + 0 = bin_to_nat y').
      { rewrite -> plus_comm. simpl. reflexivity. }
    rewrite -> H1. 
    
    


(* Exercise ends. *)
