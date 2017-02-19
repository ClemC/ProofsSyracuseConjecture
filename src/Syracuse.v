(* Definitions *)

(* Even *)
Fixpoint even n : bool :=
  match n with
    | 0 => true
    | 1 => false
    | S (S n') => even n'
  end.

(* Divide by 2 *)
Fixpoint div2 n :=
  match n with
  | 0 => 0
  | S 0 => 0
  | S (S n') => S (div2 n')
  end.

(* Pow *)
Fixpoint pow n m :=
  match m with
    | 0 => 1
    | S m => n * pow n m
  end.

(* Syracuse sequence *)
Fixpoint syr (n: nat) (u0: nat) := match n with
| 0 => u0
| S m => if even (syr m u0) then div2 (syr m u0) else 3 * (syr m u0) + 1
end.

(* ------------------------ *)
(* Trivial properties resolved by Coq core *)

Lemma plus_n_Sm : forall n m:nat, S (n + m) = n + S m.
Hint Resolve plus_n_Sm: core.

Lemma mult_n_Sm : forall n m:nat, n * m + n = n * S m.
Hint Resolve mult_n_Sm: core.

(* ------------------------ *)
(* Trivial properties *)
(* TODO : see Coq core to resolve *)
Lemma pow_2 : forall (n: nat), pow 2 (S n) = 2 * pow 2 n.
Proof.
intros.
tauto.
Qed.

Lemma plus_0: forall (n:nat), n + 0 = n.
Proof.
intros.
induction n.
simpl.
reflexivity.
simpl.
rewrite IHn.
reflexivity.
Qed.

Lemma plus_comm : forall (n:nat) (m:nat), n + m = m + n.
Proof.
intros.
induction n.
simpl.
induction m.
simpl.
reflexivity.
simpl.
elim IHm.
reflexivity.
induction m.
simpl.
rewrite plus_0.
reflexivity.
simpl.
rewrite IHn.
simpl.
rewrite plus_n_Sm.
reflexivity.
Qed.

Lemma plus2: forall (n:nat), n + 2 = S (S n).
Proof.
intros.
induction n.
simpl.
reflexivity.
simpl.
elim IHn.
trivial.
Qed.

Lemma nmult2 : forall (n:nat), 2 * S n = S (S (2 * n)).
Proof.
intros.
elim mult_n_Sm.
rewrite plus2.
reflexivity.
Qed.

Lemma succ_succ_n : forall (n: nat), (S n) + (S n + 0)= S (S (n + (n + 0))).
Proof.
intros.
rewrite plus_n_Sm.
rewrite plus_comm.
rewrite plus_0.
simpl.
rewrite plus_0.
reflexivity.
Qed.


Lemma pow_2_even : forall (n:nat), even (2 * n) = true.
Proof.
intros.
induction n.
simpl.
trivial.
rewrite nmult2.
simpl.
apply IHn.
Qed.

Lemma even_pow2n : forall (n: nat), even (pow 2 (S n)) = true.
Proof.
intros.
rewrite pow_2.
rewrite pow_2_even.
trivial.
Qed.

Lemma even_2n : forall (n:  nat), even (n + (n + 0)) = true.
Proof.
intros.
induction n.
simpl.
reflexivity.
rewrite succ_succ_n.
simpl.
apply IHn.
Qed.

Lemma div_mult2 : forall (n: nat), div2 (n + (n +0)) = n.
Proof.
intros.
induction n.
simpl.
reflexivity.
rewrite succ_succ_n.
simpl.
rewrite IHn.
reflexivity.
Qed.

Lemma syr_simpl1: forall (n:nat) (u0: nat), syr (S (S n)) (2 * u0) = if even (syr (S n) (2 * u0)) then div2 (syr (S n) (2 * u0)) else syr (S n) (2 * u0) + (syr (S n) (2 * u0) + (syr (S n) (2 * u0) + 0))  + 1.
Proof.
intros.
simpl.
reflexivity.
Qed.

(* ------------------------ *)
(* Invariance property *)
Lemma syr_inv2 : forall (n: nat) (u0: nat), syr n u0 = syr (S n) (2 * u0).
Proof.
intros.
induction n.
simpl.
rewrite even_2n.
rewrite div_mult2.
trivial.
simpl (syr (S n) u0).
rewrite syr_simpl1.
elim IHn.
elim (even (syr n u0)).
reflexivity.
reflexivity.
Qed.

(* ------------------------ *)
(* Syracuse restricted to 2^n numbers *)
Theorem syr_A1 : forall (m: nat), exists (n: nat), syr n (pow 2 m) = 1. 
Proof.
intros.
exists m.
induction m.
simpl.
trivial.
rewrite pow_2.
elim syr_inv2.
assumption.
Qed.