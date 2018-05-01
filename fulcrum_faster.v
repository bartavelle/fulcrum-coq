Require Import ZArith.
Require Import Omega.
Require Import List.
Require Import FunctionalExtensionality.

Import ListNotations.

Require Import listutils.
Require Import rollingsum.
Require Import seqi.

Definition fv (l : list Z) (i : nat) : Z :=
  Z.abs(sum (firstn i l) - sum (skipn i l)).

Open Scope Z_scope.

Lemma fv_step : forall x xs n,
  fv (x::xs) (S n) = Z.abs (x + sum (firstn n xs) - sum (skipn n xs)).
Proof.
intros.
unfold fv.
auto.
Qed.

Theorem fv_nil: forall n, fv [] n = 0.
Proof.
unfold fv. intros.
rewrite firstn_nil.
rewrite skipn_nil.
auto.
Qed.


Theorem fv_0: forall l, fv l 0 = Z.abs (sum l).
Proof.
intros.
unfold fv. simpl. rewrite Z.abs_opp. auto.
Qed.

Fixpoint fulcrum_inside (curl : Z) (curr : Z) (curn : nat)
                        (bestindex : nat) (bestdiff : Z)
                        (remaining : list Z) : (nat*Z) :=
  match remaining with
  | nil => (bestindex, bestdiff)
  | x::xs =>
     let newl := curl + x in
     let newr := curr - x in
     let curdiff := Z.abs (newl - newr) in
     let (nbestn, nbestd) := if curdiff <? bestdiff then (S curn, curdiff) else (bestindex, bestdiff) in
       fulcrum_inside newl newr (S curn) nbestn nbestd xs
  end.

Definition fulcrum (l : list Z) : nat * Z :=
  fulcrum_inside 0 (sum l) (0%nat) (0%nat) (Z.abs (sum l)) l.

Theorem fulcrum_inside_invariants:
  forall remaining curl curr curn bestindex bestdiff n v,
    fulcrum_inside curl curr curn bestindex bestdiff remaining = (n,v) ->
      (bestindex <= curn)%nat ->
      bestdiff <= Z.abs (curl - curr) ->
      (n >= bestindex)%nat /\ v <= bestdiff.
Proof.
induction remaining;intros.
* simpl in *. inversion H. subst. split;omega.
* simpl in H.
  destruct (Z.abs (curl + a - (curr - a)) <? bestdiff) eqn:F.
  + pose proof (IHremaining _ _ _ _ _ _ _ H).
    destruct H2; try omega.
    apply Z.ltb_lt in F.
    split; try omega.
  + pose proof (IHremaining _ _ _ _ _ _ _ H).
    destruct H2; try omega.
    apply Z.ltb_ge in F.
    omega.
Qed.

Inductive Model : list Z -> nat -> nat -> nat -> Z -> Prop :=
 | SimpleEnd : forall lst curbest v curn,
     v = fv lst curbest ->
     curn = length lst ->
     (curbest <= curn)%nat ->
     Model lst curn curbest curbest v
 | SimpleChange : forall lst n curbest best v,
     (n < length lst)%nat ->
     fv lst (S n) < fv lst curbest ->
     (curbest <= n)%nat ->
     Model lst (S n) (S n) best v -> Model lst n curbest best v
 | SimpleStay : forall lst n curbest best v,
     (n < length lst)%nat ->
     fv lst (S n) >= fv lst curbest ->
     (curbest <= n)%nat ->
     Model lst (S n) curbest best v -> Model lst n curbest best v
 .

Theorem Model_invariants:
  forall lst curbest curn n v,
    Model lst curn curbest n v ->
      (curbest <= curn /\ n >= curbest /\ curn <= length lst /\ curbest <= length lst /\ n <= length lst)%nat
                      /\ v = fv lst n.
Proof.
intros.
induction H.
* subst. repeat (split;try omega).
* repeat (split;try omega).
* repeat (split;try omega).
Qed.

Example test_hypo2:
  let lst := [3;7;-4;8;2] in
    forall n v,
    fulcrum_inside 0 (sum lst) 0 0 (Z.abs (sum lst)) lst = (n,v) <->
      Model lst 0 0 n v.
Proof.
simpl.
split;intros.
* inversion H. subst; clear H.
  apply SimpleChange;simpl;compute; try omega;auto.
  apply SimpleChange;simpl;compute; try omega;auto.
  apply SimpleStay;unfold fv;simpl;try omega.
  apply SimpleStay;unfold fv;simpl;try omega.
  apply SimpleStay;unfold fv;simpl;try omega.
  apply SimpleEnd; compute; auto.
* inversion H;subst. 1: { compute in H1. inversion H1. } 2: { compute in H1. contradiction. }
  inversion H3;subst. 1: { compute in H5. inversion H5. } 2: { compute in H5. contradiction. }
  inversion H7;subst. compute in H9. inversion H9. compute in H9. inversion H9.
  inversion H11;subst. compute in H13. inversion H13. compute in H13. inversion H13.
  inversion H15;subst. compute in H17. inversion H17. compute in H17. inversion H17.
  inversion H19;subst.
  + compute. auto.
  + simpl in H20. omega.
  + simpl in H20. omega.
Qed.

Theorem Model_equivalent :
  forall lst n v curn curbest,
    (curn <= length lst)%nat ->
    (n <= length lst)%nat ->
    (curbest <= curn)%nat ->
    fulcrum_inside (sum (firstn curn lst)) (sum (skipn curn lst)) curn curbest (fv lst curbest) (skipn curn lst) = (n,v) <->
      Model lst curn curbest n v.
Proof.
split;intros.
{ remember (skipn curn lst) as remaining.
  generalize dependent curn. generalize dependent v. 
  generalize dependent n. generalize dependent lst.
  generalize dependent curbest.
  induction remaining as [|x xs];intros;simpl in H0.
  * inversion H2. symmetry in Heqremaining.
    apply skipn_all_2 in Heqremaining.
    assert(curn = length lst). omega.
    apply SimpleEnd;auto.
    omega.
  * simpl in H2.
    replace (x + sum xs - x) with (sum xs) in *;try omega.
    destruct (Z.abs (sum (firstn curn lst) + x - sum xs) <? fv lst curbest) eqn:F.
    + apply Z.ltb_lt in F.
      destruct (curn =? length lst)%nat eqn:CN.
      - apply Nat.eqb_eq in CN.
        rewrite CN in Heqremaining.
        rewrite skipn_all in Heqremaining.
        inversion Heqremaining.
      - pose proof (firstn_skipn curn lst) as FN.
        assert(FN_a : firstn (S curn) lst = firstn curn lst ++ [x]). admit.
        assert(SN_a: skipn (S curn) lst = xs). admit.
        apply Nat.eqb_neq in CN.
        
        apply SimpleChange;try omega;auto.
        unfold fv at 1.
        rewrite SN_a.
        rewrite FN_a.
        rewrite <- sum_distributive.
        simpl. rewrite Z.add_0_r. auto.

        apply IHxs;auto;try omega.
        rewrite FN_a.
        rewrite <- sum_distributive.
        simpl. rewrite Z.add_0_r.
        replace (fv lst (S curn)) with (Z.abs (sum (firstn curn lst) + x - sum xs)).
        auto.
        unfold fv.
        rewrite FN_a.
        rewrite SN_a.
        rewrite <- sum_distributive.
        simpl. f_equal. omega.
   + admit.
} {

remember (skipn curn lst) as remaining eqn:REM.
remember (firstn curn lst) as processed eqn:PRO.
assert(PROREM: processed ++ remaining = lst). rewrite REM. rewrite PRO. apply firstn_skipn.

generalize dependent n.
generalize dependent v.
generalize dependent curbest.
generalize dependent curn.
generalize dependent lst.
generalize processed.
induction remaining;intros.
* admit.
* clear processed.
  destruct curn.
  + replace curbest with O in *;try omega.
    simpl.
    replace (a + sum remaining - a) with (sum remaining);try omega.
    inversion H2;subst.
    - rewrite app_length in H4.
      simpl in H4. omega.
    - simpl in PRO. simpl in REM. rewrite PRO in *. simpl in *. clear PRO. clear processed0.
      replace (Z.abs (a - sum remaining)) with (fv (a :: remaining) 1).
      apply Z.ltb_lt in H4.
      rewrite H4.
      replace a with (sum [a]) at 1.
      apply IHremaining;auto.
      simpl. rewrite Z.add_0_r. auto.
      rewrite fv_step. simpl. rewrite Z.add_0_r. auto.
    - admit.
  + inversion H2;subst.
    - rewrite H4 in REM.
      rewrite skipn_all in REM.
      inversion REM.
    - simpl.
      replace (Z.abs (sum processed0 + a - (a + sum remaining - a))) with (fv (processed0 ++ a :: remaining) (S (S curn))).
      apply Z.ltb_lt in H4.
      rewrite H4.
      replace (a + sum remaining - a) with (sum remaining) by omega.
      replace (sum processed0 + a) with (sum (processed0 ++ [a])).
      apply IHremaining;auto.
      rewrite <- app_assoc. auto.
      replace (S (S curn)) with (1 + S curn)%nat by omega.
      rewrite <- skipn_comp.
      rewrite <- REM. auto.
      admit.
      admit.
      admit.
    - admit.
Qed.


Theorem fulcrum_correct : forall i j l v,
   (j < length l)%nat -> fulcrum l = (i, v) -> fv l j >= fv l i.
Proof.

Qed.