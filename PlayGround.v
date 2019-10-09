(* Type definition *)
Inductive day : Type := 
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.

(* Function definition *)
Definition next_weekday (d:day) : day :=
  match d with
  | monday    => tuesday
  | tuesday   => wednesday
  | wednesday => thursday
  | thursday  => friday
  | friday    => monday
  | saturday  => monday
  | sunday    => monday
  end.

(* Execute *)
Compute (next_weekday friday).
Compute (next_weekday (next_weekday saturday)).

(* Proposition *)
Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = tuesday.
(* Proof *)
Proof. simpl. reflexivity. Qed.

Inductive bool : Type :=
  | true
  | false.
Definition negb (b:bool): bool :=
  match b with
  | true => false
  | false => true
  end. 
Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.
Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.
Example test_orb1:  (orb true  false) = true.
Proof. simpl. reflexivity.  Qed.
Example test_orb2:  (orb false false) = false.
Proof. simpl. reflexivity.  Qed.
Example test_orb3:  (orb false true)  = true.
Proof. simpl. reflexivity.  Qed.
Example test_orb4:  (orb true  true)  = true.
Proof. simpl. reflexivity.  Qed.

Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y ).
Example test_orb5: false || false || true = true.
Proof. simpl. reflexivity. Qed.


(* nand *)
Definition nandb (b1:bool) (b2:bool) : bool :=
  negb(andb b1 b2).
Example test_nandb1:  (nandb true  false) = true.
Proof. simpl. reflexivity.  Qed.
Example test_nandb2:  (nandb false false) = true.
Proof. simpl. reflexivity.  Qed.
Example test_nandb3:  (nandb false true)  = true.
Proof. simpl. reflexivity.  Qed.
Example test_nandb4:  (nandb true  true)  = false.
Proof. simpl. reflexivity.  Qed.

Check (negb true).
Check negb.
Check orb.

Inductive rgb : Type :=
  | red
  | green
  | blue.

Inductive color : Type :=
  | black
  | white
  | primary (p : rgb).

Definition monochrome (c : color) : bool :=
match c with
| black => true
| white => true
| primary p => false
end.

Definition isred (c : color) : bool :=
match c with
| black => false
| white => false
| primary red => true
| primary _ => false
end.

Inductive bit : Type :=
  | B0
  | B1.

Inductive nybble : Type :=
  | bits (b0 b1 b2 b3 : bit).

Check (bits B1 B0 B1 B0).

(* Inductive nat : Type :=
  | O
  | S (n : nat).
Check 0.
Check (S O).
Check (S (S O)).
 *)
Definition pred (n : nat) : nat :=
match n with
| O => O
| S n' => n'
end.

Definition minustwo (n : nat) : nat :=
match n with
| O => O
| S O => O
| S (S n') => n'
end.
Check (S (S (S (S O)))).
Check S.
(* Compute (minustwo 4). *)
(* Check S(5). *)
Fixpoint evenb (n:nat) : bool :=
match n with
| O => true
| S O => false
| S (S n') => evenb n'
end.
Definition oddb (n:nat) : bool := negb (evenb n).
Example test_oddb1: (oddb (S O)) = true.
Proof. simpl. reflexivity. Qed.
Example test_oddb2:
(oddb (S (S (S (S O))))) = false.
Proof. simpl. reflexivity. Qed.
Fixpoint plus (n : nat) (m : nat) : nat :=
match n with
| O => m
| S n' => S (plus n' m)
end.
Fixpoint mult (n m : nat) : nat :=
match n with
| O => O
| S n' => plus m (mult n' m)
end.
Fixpoint minus (n m:nat) : nat :=
match n, m with
| O , _ => O
| S _ , O => n
| S n', S m' => minus n' m'
end.
Notation "x + y" :=
(plus x y)
(at level 50, left associativity)
: nat_scope.
Fixpoint eqb (n m : nat) : bool :=
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
Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' => match m with
            | O => false
            | S m' => leb n' m'
            end
  end.


Theorem plus_O_n : forall n:nat, 0 + n = n.




