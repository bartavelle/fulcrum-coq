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

Lemma sum_fv_artifacts: forall s l,
  s + sum l - s = sum l.
Proof. intros. omega. Qed.

Lemma skipnS {A} : forall lst (x : A) xs curn, x :: xs = skipn curn lst -> xs = skipn (S curn) lst.
Proof.
intros.
replace (S curn) with (1+curn)%nat by omega.
rewrite <- skipn_comp.
rewrite <- H.
auto.
Qed.

Lemma uncons_eq {A} : forall (x : A) xs ys,
   x::xs = x::ys <-> xs=ys.
Proof.
split;intros.
* inversion H. auto.
* f_equal. auto.
Qed.

Lemma firstnS {A} : forall lst (x : A) xs curn, x :: xs = skipn curn lst ->
     firstn (S curn) lst = firstn curn lst ++ [x].
Proof.
induction lst; intros.
* rewrite skipn_nil in H. inversion H.
* simpl. destruct curn.
  + simpl. simpl in H. inversion H. auto.
  + simpl firstn at 2. replace ((a :: firstn curn lst) ++ [x]) with (a:: (firstn curn lst ++ [x])) by auto.
    erewrite <- IHlst. auto.
    simpl in H. apply H.
Qed.

Theorem Model_equivalent :
  forall lst n v curn curbest,
    (curn <= length lst)%nat ->
    (n <= length lst)%nat ->
    (curbest <= curn)%nat ->
    fulcrum_inside (sum (firstn curn lst)) (sum (skipn curn lst)) curn curbest (fv lst curbest) (skipn curn lst) = (n,v) <->
      Model lst curn curbest n v.
Proof with auto.
split.
{ 
  (* induction is performed on [skipn curn lst] so that [curn] and [lst] advance in lockstep *)
  remember (skipn curn lst) as remaining.
  generalize dependent curn. generalize dependent v. 
  generalize dependent n. generalize dependent lst.
  generalize dependent curbest.
  induction remaining as [|x xs];intros;simpl in H0.
  * (* empty remaining list, we are in the SimpleEnd case *)
    inversion H2. symmetry in Heqremaining.
    apply skipn_all_2 in Heqremaining.
    assert(curn = length lst). omega.
    apply SimpleEnd;auto.
    omega.
  * (* some data is remaining, we are in a normal step *)
    simpl in H2.
    rewrite sum_fv_artifacts in H2.
    (* either the current diff is lower than the best diff, or it is not *)
    destruct (Z.abs (sum (firstn curn lst) + x - sum xs) <? fv lst curbest) eqn:F.
    + (* SimpleChange situation *)
      apply Z.ltb_lt in F.
      (* if curn = length lst, it means we are at the final step, which is not possible, so we prove otherwise *)
      destruct (curn =? length lst)%nat eqn:CN.
      - apply Nat.eqb_eq in CN.
        rewrite CN in Heqremaining.
        rewrite skipn_all in Heqremaining.
        inversion Heqremaining.
      - apply Nat.eqb_neq in CN.
        apply SimpleChange;try omega;auto.
        unfold fv at 1.
        rewrite (firstnS lst x xs);auto.
        rewrite <- (skipnS lst x xs);auto.
        rewrite <- sum_distributive.
        simpl. rewrite Z.add_0_r...
        { apply IHxs;auto;try omega.
          * apply (skipnS _ _ _ _ Heqremaining).
          * rewrite (firstnS lst x xs);auto.
            rewrite <- sum_distributive. simpl. rewrite Z.add_0_r.
            replace (fv lst (S curn)) with (Z.abs (sum (firstn curn lst) + x - sum xs));auto.
            unfold fv.
            rewrite (firstnS lst x xs);auto.
            rewrite <- (skipnS lst x xs);auto.
            rewrite <- sum_distributive.
            f_equal.
            simpl.
            omega.
        }
   + (* SimpleStay situation *)
      apply Z.ltb_ge in F.
      (* if curn = length lst, it means we are at the final step, which is not possible, so we prove otherwise *)
      destruct (curn =? length lst)%nat eqn:CN.
      - apply Nat.eqb_eq in CN.
        rewrite CN in Heqremaining.
        rewrite skipn_all in Heqremaining.
        inversion Heqremaining.
      - apply Nat.eqb_neq in CN.
        apply SimpleStay;try omega;auto.
        unfold fv at 1.
        rewrite (firstnS lst x xs);auto.
        rewrite <- (skipnS lst x xs);auto.
        rewrite <- sum_distributive.
        simpl. rewrite Z.add_0_r. omega.
        { apply IHxs;auto;try omega.
          * apply (skipnS _ _ _ _ Heqremaining).
          * rewrite (firstnS lst x xs);auto.
            rewrite <- sum_distributive. simpl. rewrite Z.add_0_r.
            replace (fv lst (S curn)) with (Z.abs (sum (firstn curn lst) + x - sum xs));auto.
            unfold fv.
            rewrite (firstnS lst x xs);auto.
            rewrite <- (skipnS lst x xs);auto.
            rewrite <- sum_distributive.
            f_equal.
            simpl.
            omega.
        }
} {

remember (skipn curn lst) as remaining eqn:REM.
remember (firstn curn lst) as processed eqn:PRO.
(*assert(PROREM: processed ++ remaining = lst). rewrite REM. rewrite PRO. apply firstn_skipn.*)

generalize dependent n.
generalize dependent v.
generalize dependent curbest.
generalize dependent curn.
generalize dependent lst.
generalize processed.
induction remaining;intros.
* simpl.
  symmetry in REM.
  apply skipn_all_2 in REM.
  assert(F: curn = length lst). omega.
  rewrite F in H2.
  inversion H2;subst;auto;omega.
* clear processed.
  destruct curn.
  + (* curn = 0 *)
    replace curbest with O in * by omega.
    simpl.
    rewrite sum_fv_artifacts.
    inversion H2;subst.
    - simpl in REM. rewrite <- REM in H4.
      inversion H4.
    - (* SimpleChange *)
      simpl in *.
      apply Z.ltb_lt in H4.
      replace (Z.abs (a - sum remaining)) with (fv lst 1).
      rewrite H4.
      replace a with (sum [a]) at 1 by (simpl;omega).
      apply IHremaining;auto;try (rewrite <- REM; auto).
      rewrite <- REM.
      rewrite fv_step. simpl. f_equal. omega.
    - (* SimpleKeep *)
      simpl in *.
      Search ( _ < _ )%Z.
      apply Z.ge_le in H4.
      apply Z.ltb_ge in H4.
      replace (Z.abs (a - sum remaining)) with (fv lst 1).
      rewrite H4.
      replace a with (sum [a]) at 1 by (simpl;omega).
      apply IHremaining;auto;try (rewrite <- REM; auto).
      rewrite <- REM.
      rewrite fv_step. simpl. f_equal. omega.
  + (* curn > 0 *)
    pose proof (firstn_skipn (S curn) lst) as APP.
    rewrite <- REM in APP.
    inversion H2;subst.
    - rewrite H4 in REM.
      rewrite skipn_all in REM.
      inversion REM.
    - (* SimpleChange *)
      unfold fulcrum_inside.
      fold fulcrum_inside.
      replace (Z.abs (sum (firstn (S curn) lst) + a - (sum (a::remaining) - a))) with (fv ((firstn (S curn) lst) ++ a :: remaining) (S (S curn))).
      rewrite APP.
      apply Z.ltb_lt in H4.
      rewrite H4.
      replace (sum (a::remaining) - a) with (sum remaining) by (simpl;omega).
      replace (sum (firstn (S curn) lst) + a) with (sum ((firstn (S curn) lst) ++ [a])).
      apply IHremaining;auto.
      eapply skipnS. apply REM.
      erewrite <- firstnS. auto. apply REM.
      rewrite <- sum_distributive. simpl sum at 2. omega.
      remember (firstn (S curn) lst) as processed eqn:PRO.
      assert(length processed = S curn).
      rewrite PRO.
      rewrite firstn_length.
      Search(Init.Nat.min).
      apply Nat.min_l. auto.
      (* :( *)
      unfold fv.
      erewrite firstnS. 2: { rewrite APP. apply REM. }
      erewrite <- skipnS. 2: {rewrite APP. apply REM. }
      rewrite firstn_app.
      rewrite <- H7 at 1.
      rewrite firstn_all.
      rewrite H7.
      rewrite Nat.sub_diag. simpl.
      f_equal.
      rewrite <- sum_distributive.
      rewrite <- sum_distributive.
      simpl.
      omega.
    - (* SimpleStay *)
      unfold fulcrum_inside.
      fold fulcrum_inside.
      replace (Z.abs (sum (firstn (S curn) lst) + a - (sum (a::remaining) - a))) with (fv ((firstn (S curn) lst) ++ a :: remaining) (S (S curn))).
      rewrite APP.
      apply Z.ge_le in H4.
      apply Z.ltb_ge in H4.
      rewrite H4.
      replace (sum (a::remaining) - a) with (sum remaining) by (simpl;omega).
      replace (sum (firstn (S curn) lst) + a) with (sum ((firstn (S curn) lst) ++ [a])).
      apply IHremaining;auto.
      eapply skipnS. apply REM.
      erewrite <- firstnS. auto. apply REM.
      rewrite <- sum_distributive. simpl sum at 2. omega.
      remember (firstn (S curn) lst) as processed eqn:PRO.
      assert(length processed = S curn).
      rewrite PRO.
      rewrite firstn_length.
      Search(Init.Nat.min).
      apply Nat.min_l. auto.
      (* :( *)
      unfold fv.
      erewrite firstnS. 2: { rewrite APP. apply REM. }
      erewrite <- skipnS. 2: {rewrite APP. apply REM. }
      rewrite firstn_app.
      rewrite <- H7 at 1.
      rewrite firstn_all.
      rewrite H7.
      rewrite Nat.sub_diag. simpl.
      f_equal.
      rewrite <- sum_distributive.
      rewrite <- sum_distributive.
      simpl.
      omega.
}
Qed.


Theorem fulcrum_correct : forall i j l v,
   (j < length l)%nat -> fulcrum l = (i, v) -> fv l j >= fv l i.
Proof.

Qed.