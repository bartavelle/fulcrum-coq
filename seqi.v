(* sequences and stuff *)

Require Import Omega.
Require Import List.
Require Import FunctionalExtensionality.

Require Import listutils.

Import ListNotations.

Definition seqi (n : nat) : list nat :=
  seq 0 (n + 1).

Example seqi_test: seqi 5 = [0;1;2;3;4;5].
Proof. unfold seqi. simpl. auto. Qed.

Lemma seqi_bound : forall n x, n > 0 -> In x (seqi n) <-> 0 <= x <= n.
Proof.
intros. unfold seqi.
pose proof (in_seq (n+1) 0 x).
simpl in H0.
destruct H0.
split;intros.
* destruct (H0 H2). omega.
* apply H1. omega.
Qed.

Example ex_rev_seq:
  let s := 25 in
  let l := 9 in
  rev (seq s l) = map (fun x => s*2 + l - x - 1) (seq s l).
Proof.
simpl.
auto.
Qed.

Example ex_seq_last:
  let s := 2 in
  let l := 7 in
  seq s (S l) = seq s l ++ [s + l].
Proof.
simpl.
auto.
Qed.

Theorem seqi_last: forall n,
  seqi (S n) = seqi n ++ [S n].
Proof.
intros.
unfold seqi.
replace (S n + 1) with (S (n+1)) by omega.
rewrite seq_last.
rewrite Nat.add_0_r.
replace (n + 1) with (S n) by omega.
auto.
Qed.

Theorem list_nth_eq: forall A (l1 : list A) l2,
  length l1 = length l2 ->
      l1 = l2 <-> (forall n def, n < length l1 -> nth n l1 def = nth n l2 def).
Proof.
intros.
split;intros.
* subst. auto.
* generalize dependent l2.
  induction l1;intros.
  + simpl in H. destruct l2;auto. inversion H.
  + destruct l2. inversion H.
    simpl in H. inversion H. clear H.
    f_equal.
    - pose proof (H0 0). simpl in H. apply (H a). omega.
    - apply IHl1;auto.
      intros.
      pose proof (H0 (S n)).
      simpl in H1.
      apply H1.
      omega.
Qed.

Theorem nth_replace_def {A} : forall n (l : list A) def1 def2,
  n < length l -> nth n l def1 = nth n l def2.
Proof.
induction n;intros.
* destruct l. inversion H. simpl. auto.
* destruct l. inversion H. simpl in *.
  apply IHn. omega.
Qed.

Theorem rev_seq: forall s l,
  rev (seq s l) = map (fun x => s*2 + l - x - 1) (seq s l).
Proof.
intros.
set (f := (fun x : nat => s * 2 + l - x - 1)).
apply list_nth_eq.
* rewrite rev_length.
  rewrite map_length.
  auto.
* intros.
  rewrite rev_length in H.
  rewrite rev_nth;auto.
  rewrite seq_length.
  destruct l. simpl. destruct n;auto.
  rewrite seq_nth;try omega.
  rewrite nth_replace_def with (def2 := f n).
  + rewrite map_nth.
    rewrite seq_length in H.
    rewrite seq_nth by omega.
    unfold f. omega.
  + rewrite map_length. auto.
Qed.

Theorem rev_seqi: forall n,
  rev (seqi n) = map (fun x => n - x) (seqi n).
Proof.
intros.
unfold seqi.
rewrite rev_seq.
apply map_eq.
intros.
apply in_seq in H.
omega.
Qed.

Lemma map_rev_seqi: forall A n (f : nat -> A),
  rev (map f (seqi n)) = map (fun x => f (n - x)) (seqi n).
Proof.
intros.
rewrite <- map_rev.
rewrite rev_seqi.
rewrite map_map.
auto.
Qed.

Theorem seqi_all: forall n i,
 i > 0 -> i <= n -> In i (seqi n).
Proof.
intros.
unfold seqi.
apply in_seq.
omega.
Qed.

Theorem map_seqi_all: forall A (f : nat -> A) n l,
  map f (seqi n) = l -> forall i, i <= n -> i > 0 -> In (f i) l.
Proof.
intros.
pose proof (seqi_all n i H1 H0).
subst.
apply in_map.
auto.
Qed.

Theorem index_map_seq : forall s l n k e f,
  indexN k e (map f (seq s l)) = Some n -> e = f (n + s - k).
Proof.
induction l;intros.
* simpl in H. inversion H.
* rewrite seq_last in H. rewrite map_app in H.
  simpl in H.
  pose proof (indexN_app2 _ _ _ _ _ H).
  destruct H0.
  + apply IHl. auto.
  + simpl in H0.
    destruct (f (l + s)%nat =? e)%Z eqn:F.
    - rewrite map_length in H0.
      rewrite seq_length in H0.
      inversion H0. clear H0.
      apply Z.eqb_eq in F.
      replace (k + l + s - k)%nat with (l + s) by omega.
      omega.
    - inversion H0.
Qed.

Definition minIndex_b (l : list Z) : option (nat * Z) :=
  match minimum l with
  | None => None
  | Some v => match indexN 0 v l with
              | None => None
              | Some n => Some (n,v)
              end
  end.

Lemma minIndex_b_map_seq : forall f n i v,
  minIndex_b (map f (seqi n)) = Some (i, v) ->
    v = f i /\ (forall (j : nat), (0 <= j <= n) -> (f j >= f i)%Z).
Proof.
intros. unfold minIndex_b in H.
unfold seqi in *.
replace (n + 1) with (S n) in H;try omega.
assert (minimum (map f (seq 0 (S n))) = Some v).
{
  simpl. simpl in H.
  destruct (f 0%nat =? minimumNE (f 0%nat) (map f (seq 1 n)))%Z eqn:F.
  * apply Z.eqb_eq in F. inversion H. auto.
  * destruct (indexN 1 (minimumNE (f 0) (map f (seq 1 n))) (map f (seq 1 n))).
    inversion H. auto. inversion H.
}
pose proof (minimum_correct _ _ H0). destruct H1.
simpl in H.
destruct (f 0%nat =? minimumNE (f 0%nat) (map f (seq 1 n)))%Z eqn:F.
* inversion H. subst. clear H.
  apply Z.eqb_eq in F. split;auto.
  intros. rewrite <- F in H2.
  apply Z.ge_le_iff.
  apply H2.
  apply in_map.
  apply in_seq.
  omega.
* assert (indexN 1 (minimumNE (f 0) (map f (seq 1 n))) (map f (seq 1 n)) = Some i).
  { destruct (indexN 1 (minimumNE (f 0) (map f (seq 1 n))) (map f (seq 1 n))).
    * inversion H. auto.
    * inversion H.
  }
  pose proof (index_map_seq _ _ _ _ _ _ H3).
  replace (i + 1 - 1) with i in H4;try omega.
  simpl in H0. inversion H0.
  split;auto.
  intros.
  rewrite H3 in H.
  apply Z.ge_le_iff.
  rewrite <- H4. rewrite H6.
  apply H2.
  apply in_map.
  apply in_seq.
  omega.
Qed.

