Inductive day : Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.

Definition next_weekday (d:day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => saturday
  | saturday => sunday
  | sunday => monday
  end.

Example test_next_weekday:
  (next_weekday (next_weekday sunday)) = tuesday.
Proof. simpl. reflexivity. Qed.

Inductive bool: Type :=
  | true
  | false.

Definition negb (b: bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Definition andb (b1: bool) (b2: bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Definition orb (b1: bool) (b2: bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.

Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).

Example test_orb1: (orb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb2: (orb false false) = false.
Proof. simpl. reflexivity. Qed.
Example test_orb3: false || false || true = true.
Proof. simpl. reflexivity. Qed. 

Example test_andb1: (andb true false) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb2: (andb true true) = true.
Proof. simpl. reflexivity. Qed.

(* Exercise. Page 20 ~ *)

Definition nandb (b1:bool) (b2:bool) : bool :=
  (negb (andb b1 b2)).

Example test_nandb1: (nandb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb2: (nandb false false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb3: (nandb true true) = false.
Proof. simpl. reflexivity. Qed.
Example test_nandb4: (nandb false true) = true.
Proof. simpl. reflexivity. Qed.

Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
  match b1 with
  | true => (andb b2 b3)
  | false => false
  end.

Example test_andb31:                 (andb3 true true true) = true.
Proof. simpl. reflexivity. Qed.
Example test_andb32:                 (andb3 false true true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb33:                 (andb3 true false true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb34:                 (andb3 true true false) = false.
Proof. simpl. reflexivity. Qed.

(* Exercise ends *)

Check true.

Inductive rgb : Type :=
  | red
  | green
  | blue.

Inductive color: Type :=
  | black
  | white
  | primary (p: rgb).

Definition monochrome (c:color) : bool :=
  match c with
  | white => true
  | black => true
  | primary q => false
  end.

Definition isgreen (c:color) : bool :=
  match c with
  | white => false
  | black => false
  | primary green => true
  | primary _ => false
  end.

Module NatPlayground.

Inductive nat: Type :=
  | zero
  | succ (n:nat).

Definition pred (n:nat) : nat :=
  match n with
  | zero => zero
  | succ n' => n'
  end.

End NatPlayground.

Definition minustwo (n:nat) : nat :=
  match n with
  | O => O
  | S O => O
  | S (S n') => n'
  end.

Module NatPlayground2.

Fixpoint plus (n:nat) (m:nat) : nat :=
  match n with
  | O => m
  | S n' => S (plus n' m)
  end.

Fixpoint mult (n:nat) (m:nat) : nat :=
  match n with
  | O => O
  | S n' => plus m (mult n' m)
  end.

Example test_mult1: (mult 3 3) = 9.
Proof. simpl. reflexivity. Qed.

Fixpoint minus (n m:nat) : nat :=
  match n, m with
  | O, _ => O
  | S _, O => n
  | S n', S m' => minus n' m'
  end.

End NatPlayground2.

Fixpoint factorial (n:nat) : nat :=
  match n with
  | O => S O
  | S n' => mult n (factorial n')
  end.

Example test_factorial1: (factorial 3) = 6.
Proof. simpl. reflexivity. Qed.
Example test_factorial2: (factorial 5) = (mult 10 12).
Proof. simpl. reflexivity. Qed.

Notation "x + y" := (plus x y)
                      (at level 50, left associativity)
                      : nat_scope.

Notation "x - y" := (minus x y)
                      (at level 50, left associativity)
                      : nat_scope.

Notation "x * y" := (mult x y)
                      (at level 40, left associativity)
                      : nat_scope.

Fixpoint eqb (n m: nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => eqb n' m'
            end
  end.

Fixpoint leb (n m: nat) : bool :=
  match n with
  | O => true
  | S n' => match m with
            | O => false
            | S m' => leb n' m'
            end
  end.

Example test_leb1: (leb 2 2) = true.
Proof. simpl. reflexivity. Qed.
Example test_leb2: (leb 2 3) = true.
Proof. simpl. reflexivity. Qed.
Example test_leb3: (leb 4 2) = false.
Proof. simpl. reflexivity. Qed.

Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.

Example test_leb3': (4 <=? 2) = false.
Proof. simpl. reflexivity. Qed.

(* Exercise. Page 29 *)

Definition ltb (n m: nat) : bool :=
  match (leb m n) with
  | true => false
  | false => true
  end.

Example test_ltb: (ltb 2 2) = false.
Proof. simpl. reflexivity. Qed.

(* Exercise ends *)

(* Exercise. Page 37 

Fixpoint reach2 (n: nat) : nat :=
  match n with
  | O => reach2 (S O)
  | S O => S (S O)
  | S (S n') => n
  end.

Compute (reach2 0).

Exercise ends. *)

(* Exercise. Page 39 *)

Inductive bin: Type :=
  | Z
  | A (n:bin)
  | B (n:bin).

Fixpoint incr (m:bin) : bin :=
  match m with
  | Z => B Z
  | A m' => B m'
  | B m' => A (incr m')
  end.

Example test_bin_incr1: (incr (B (B Z))) = A (A (B Z)).
Proof. simpl. reflexivity. Qed.
Example test_bin_incr2: (incr (A (B Z))) = B (B Z).
Proof. simpl. reflexivity. Qed.

Fixpoint bin_to_nat (m:bin) : nat :=
  match m with
  | Z => O
  | A m' => 2 * (bin_to_nat m')
  | B m' => 1 + 2 * (bin_to_nat m')
  end.

Example test_bin_to_nat1: (bin_to_nat (B (B Z))) = 3.
Proof. simpl. reflexivity. Qed.
Example test_bin_to_nat2: (bin_to_nat (incr (B (A (B Z))))) = 6.
Proof. simpl. reflexivity. Qed.

(* Exercise ends. *)

Theorem plus_O_n: 
  forall n: nat, 0 + n = n.
Proof. intros n. simpl. reflexivity. Qed.

Theorem plus_O_n':
  forall n: nat, 0 + n = n.
Proof. intros n. reflexivity. Qed.

Theorem plus_1_l:
  forall n: nat, 1 + n = S n.
Proof. 
  intros n.
  reflexivity.
Qed.

Theorem plus_id_example:
  forall n m: nat, n = m -> n + n = m + m.
Proof.
  intros n.
  intros m.
  intros H.
  rewrite -> H.
  reflexivity.
Qed.

Theorem plus_id_exercise:
  forall n m o: nat,
  n = m -> m = o -> n + m = m + o.
Proof.
  intros n m o.
  intros H1.
  intros H2.
  rewrite -> H1.
  rewrite -> H2.
  reflexivity.
Qed.

Theorem mult_0_plus:
  forall n m: nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  rewrite -> plus_O_n.
  reflexivity.
Qed.

Theorem mult_S_1:
  forall n m: nat,
  m = S n -> m * (1 + n) = m * m.
Proof.
  intros n m.
  intros M.
  rewrite -> M.
  rewrite <- plus_1_l.
  reflexivity.
Qed.

Theorem plus_1_neq_0_firsttry:
  forall n: nat,
  (n + 1) =? 0 = false.
Proof.
  intros n.
  simpl. Abort.

Theorem plus_1_neq_0:
  forall n: nat,
  (n + 1) =? 0 = false.
Proof.
  intros n.
  destruct n as [| n'] eqn:E.
  - reflexivity.
  - reflexivity.
Qed.

Theorem negb_involutive:
  forall b: bool,
  negb (negb b) = b.
Proof.
  intros b. destruct b eqn:E.
  - reflexivity.
  - reflexivity.
Qed.

Theorem andb_commutative:
  forall b c: bool,
  andb b c = andb c b.
  intros b c. destruct b eqn:Eb.
  - destruct c eqn:Ec.
    + reflexivity.
    + reflexivity.
  - destruct c eqn:Ec.
    + reflexivity.
    + reflexivity.
Qed.

(* Exercise. Page 36 *)

Theorem zero_nbeq_plus_1:
  forall n: nat, 0 =? (n + 1) = false.
Proof.
  intros n. destruct n as [| n'] eqn:E.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.
  
Theorem andb_true_elim2:
  forall b c: bool,
  andb b c = true -> c = true.
Proof.
  intros b c. destruct b eqn:Eb.
  - simpl.
    intros C. rewrite -> C.
    reflexivity.
  - simpl.
    intros F.
    destruct c eqn:Ec.
    + reflexivity.
    + rewrite -> F.
      reflexivity.
Qed.

(* Exercise ends. *)


(* Exercise. Page 38 *)

Theorem identity_fn_applied_twice:
  forall f: bool -> bool, 
  forall x: bool, f x = x -> forall b:bool, f (f b) = b.
Proof.
  intros f x FX b.
  destruct x, b. Abort.

Theorem andb_eq_orb:
  forall b c: bool, (andb b c = orb b c) -> b = c.
Proof.
  intros b c. destruct b eqn:Eb.
  - simpl.
    intros C. rewrite -> C. reflexivity.
  - simpl.
    intros F. rewrite -> F. reflexivity.
Qed.

(* Exercise ends. *)

