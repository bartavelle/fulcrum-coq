Require Import ZArith.
Require Import Omega.
Require Import List.
Require Import FunctionalExtensionality.

Import ListNotations.

Require Import listutils.
Require Import rollingsum.
Require Import seqi.

Definition fv (l : list Z) (i : nat) : Z :=
  Zabs(sum (firstn i l) - sum (skipn i l)).

Open Scope Z_scope.


Definition fulcrumRS (input : list Z) : list Z :=
  let sl := rollingSum input in
  let sr := rev (rollingSum (rev input)) in
  map (fun p => Zabs (fst p - snd p)) (combine sl sr)
.

Definition fulcrum (input : list Z) : option (nat * Z) :=
  minIndex_b (fulcrumRS input).

Example ex_fulcrumRS :
  let input := [5;-2;8;10;2;5] in
  fulcrumRS input = map (fun i => fv input i) (seqi (length input)).
Proof.
intros.
unfold fv.
unfold fulcrumRS.
simpl.
auto.
Qed.

Theorem fulcrumRS_correct : forall input,
  input <> nil ->
  fulcrumRS input = map (fun i => fv input i) (seqi (length input)).
Proof.
intros. unfold fv.
unfold fulcrumRS.
repeat (rewrite rollingSum_summ).
unfold seqi.
rewrite rev_length.
rewrite <- map_rev.
rewrite rev_seq.
rewrite map_map.
rewrite combine_map.
rewrite map_map.
apply map_eq.
intros.
apply in_seq in H0.
simpl.
replace (length input + 1 - x - 1)%nat with (length input - x)%nat by omega.
destruct (Nat.eq_dec x 0).
* subst. simpl.
  rewrite Nat.sub_0_r.
  rewrite <- rev_length.
  rewrite firstn_all.
  rewrite <- sum_rev.
  auto.
* assert(L: (length input > 0)%nat). { destruct input. contradiction. simpl. omega. }
  rewrite (first_skip_rev _ (length input - x)%nat).
  rewrite rev_involutive.
  rewrite <- sum_rev.
  rewrite rev_length.
  replace (length input - (length input - x))%nat with x by omega.
  auto.

  rewrite rev_length. omega.
Qed.

Theorem fulcrum_correct : forall l i v j,
   (j < length l)%nat -> fulcrum l = Some (i, v) -> fv l j >= fv l i.
Proof.
intros.
unfold fulcrum in H0.
rewrite fulcrumRS_correct in H0.
apply minIndex_b_map_seq in H0.
destruct H0.
apply H1.
omega.
destruct l. inversion H.
intro contra.
inversion contra.
Qed.
