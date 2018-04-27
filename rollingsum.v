Require Import ZArith.
Require Import Omega.
Require Import List.
Require Import FunctionalExtensionality.

Import ListNotations.

Require Import seqi.
Require Import listutils.

Open Scope Z_scope.

Fixpoint rollingSumH (n : Z) (lst : list Z) : list Z :=
  match lst with
  | nil => [n]
  | (x::xs) => n :: rollingSumH (x+n) xs
  end.

Definition rollingSum (input : list Z): list Z :=
  rollingSumH 0 input.

Lemma rollingSumH_n : forall l n,
  rollingSumH n l = map (fun x => x + n) (rollingSumH 0 l).
Proof.
induction l;intros;simpl in *;auto.
f_equal.
rewrite IHl.
rewrite  Z.add_0_r.
rewrite (IHl a).
rewrite map_map.
f_equal.
apply functional_extensionality.
intros.
omega.
Qed.

Example ex_rollingSum_summ :
  let l := [3;-5;8;3;9] in
  rollingSum l = map (fun i => sum (firstn i l)) (seq 0 (length l+1)).
Proof.
unfold rollingSum.
simpl.
auto.
Qed.

Example ex_rollingSumH_summ :
  let l := [3;-5;8;3;9] in
  let a := 7 in
  rollingSumH a l = map (fun i => sum (firstn i l) + a) (seq 0 (length l + 1)).
Proof.
simpl.
auto.
Qed.


Lemma rollingSumH_summ : forall a (l : list Z),
   rollingSumH a l = map (fun i => sum (firstn i l) + a) (seq 0 (length l + 1)).
Proof.
intros.
generalize dependent a.
induction l;intros;auto.
simpl rollingSumH.
rewrite IHl.
simpl. f_equal.
rewrite <- seq_shift.
rewrite map_map.
apply map_eq.
intros.
apply in_seq in H.
simpl.
omega.
Qed.

Lemma rollingSum_summ : forall l,
  rollingSum l = map (fun i => sum (firstn i l)) (seq 0 (length l + 1)).
Proof.
intros.
unfold rollingSum.
rewrite rollingSumH_summ.
apply map_eq;intros. omega.
Qed.

(* Close Scope Z_scope. *)