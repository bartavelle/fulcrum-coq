Require Import ZArith.
Require Import List.
Require Import Omega.
Import ListNotations.

Open Scope Z_scope.

(* sum function and associated lemmas *)
Fixpoint sum (lst : list Z) : Z :=
  match lst with
  | nil => 0
  | x::xs => x + sum xs
  end.

Lemma sum_distributive : forall l1 l2, sum l1 + sum l2 = sum (l1 ++ l2).
Proof.
induction l1;intros;simpl in *;auto.
rewrite <- IHl1.
omega.
Qed.

Lemma sum_append : forall l x, sum(l ++ x :: nil) = sum l + x.
Proof.
induction l;intros;simpl;auto.
- omega.
- rewrite IHl. omega.
Qed.

Lemma sum_hd : forall l a, sum (a :: l) = a + sum l.
Proof.
destruct l;intros;auto.
Qed.

Lemma sum_rev: forall l, sum l = sum (rev l).
Proof.
induction l; intros;auto.
simpl.
rewrite sum_append. omega.
Qed.

(* minimum index of a list of Z *)
Fixpoint minimumNE (cur : Z) (l : list Z) : Z :=
  match l with
  | nil => cur
  | x::xs =>
      let nxt := if cur <? x then cur else x
      in  minimumNE nxt xs
  end.

Definition minimum (l : list Z) : option Z :=
  match l with
  | nil => None
  | x::xs => Some (minimumNE x xs)
  end.

Lemma minimumNE_cur : forall cur l,
  minimumNE cur l <= cur.
Proof.
intros. generalize dependent cur.
induction l;intros.
* simpl. omega.
* simpl. destruct (Z_ge_lt_dec cur a).
 + assert (cur <? a = false). apply (Z.ltb_ge cur a). omega.
   rewrite H. pose proof (IHl a). omega.
 + assert (cur <? a = true). apply (Z.ltb_lt cur a). omega.
   rewrite H. apply IHl.
Qed.

Theorem minimumNE_correct : forall cur l e,
  minimumNE cur l = e -> In e (cur :: l) /\ (forall e', In e' (cur :: l) -> e <= e').
Proof.
intros. generalize dependent cur. generalize dependent e.
induction l;intros.
* simpl in H. split. constructor. auto. intros. inversion H0. subst. omega. inversion H1.
* simpl in H.
  destruct (Z_ge_lt_dec cur a).
  + replace (cur <? a) with false in H.
    pose proof (IHl _ _ H).
    destruct H0.
    split.
    - simpl. simpl in H0. auto.
    - intros. simpl in H1. simpl in H2.
      destruct H2.
      pose proof (minimumNE_cur a l). omega.
      apply H1. apply H2.
    - symmetry. apply (Z.ltb_ge). omega.
  + assert (cur <? a = true). apply (Z.ltb_lt). auto.
    rewrite H0 in H.
    pose proof (IHl _ _ H).
    destruct H1.
    split.
    - simpl. simpl in H1. destruct H1;auto.
    - intros. simpl in H2. simpl in H3.
      destruct H3.
        apply H2. auto.
      destruct H3.
        pose proof (minimumNE_cur cur l).
        omega.
        
        apply H2. auto.
Qed.

Theorem minimum_correct : forall l e,
  minimum l = Some e -> In e l /\ (forall e', In e' l -> e <= e').
Proof.
intros.
destruct l. inversion H.
apply minimumNE_correct. unfold minimum in H. inversion H. auto.
Qed.

Fixpoint indexN (n : nat) (e : Z) (l : list Z) : option nat :=
  match l with
  | nil => None
  | x::xs => if x =? e then Some n else indexN (S n) e xs
  end.

Definition indexOf (e : Z) (l : list Z) : option nat :=
  indexN 0%nat e l.

Lemma indexN_min : forall l k e n,
  indexN k e l = Some n -> (n >= k)%nat.
Proof.
induction l;intros.
* inversion H.
* simpl in H.
  destruct (Z.eq_dec a e).
  + subst. assert(e =? e = true). apply Z.eqb_eq. auto.
    rewrite H0 in H. inversion H. omega.
  + assert (a =? e = false). apply Z.eqb_neq. auto.
    rewrite H0 in H. pose proof (IHl _ _ _ H). omega.
Qed.

Theorem indexN_app : forall l1 l2 k e,
  indexN k e (l1 ++ l2) =
    match indexN k e l1 with
    | Some r => Some r
    | None => indexN (k+length l1) e l2
    end.
Proof.
induction l1;intros.
* simpl. rewrite Nat.add_0_r. auto.
* simpl. destruct (Z.eqb a e) eqn:F. auto.
  replace (k + S (length l1))%nat with (S k + length l1)%nat by omega.
  auto.
Qed.

Theorem indexN_app2 : forall l1 l2 k e r,
  indexN k e (l1 ++ l2) = Some r -> indexN k e l1 = Some r \/ indexN (k + length l1) e l2 = Some r.
Proof.
induction l1;intros.
* simpl in H. right. simpl. rewrite Nat.add_0_r. auto.
* simpl in H.
  simpl.
  destruct (Z.eqb a e) eqn:F. auto.
  replace (k + S (length l1))%nat with (S k + length l1)%nat by omega.
  apply IHl1.
  auto.
Qed.

Close Scope Z_scope.

(* extra firstn / skipn properties *)
(* map/combine properties *)
Theorem map_eq : forall A B (f : A -> B) (g : A -> B) (l : list A),
  map f l = map g l <-> (forall x, In x l -> f x = g x).
Proof.
split;intros.
- eapply ext_in_map. apply H. auto.
- apply map_ext_in.
  auto.
Qed.

Lemma combine_step : forall A B (x : A) xs (y:B) ys,
  combine (x::xs) (y::ys) = (x,y) :: combine xs ys.
Proof.
intros.
simpl. auto.
Qed.

Lemma combine_map: forall A B C (f : A -> B) (g : A -> C) l,
  combine (map f l) (map g l) = map (fun x => (f x, g x)) l.
Proof.
induction l;auto.
simpl. f_equal;auto.
Qed.


Theorem firstn_nil : forall A n, firstn n (nil : list A) = nil.
Proof.
destruct n;auto.
Qed.

Theorem skipn_nil : forall A n, skipn n (nil : list A) = nil.
Proof.
destruct n;auto.
Qed.

Theorem skipn_all_2 : forall A (l : list A) n,
 (n >= length l)%nat <-> skipn n l = nil.
Proof.
split.
{ generalize dependent n.

induction l;intros.
* apply skipn_nil.
* destruct n. inversion H.
  simpl in H.
  simpl.
  apply IHl.
  omega.
}
{ generalize dependent n.
induction l;intros.
* simpl. omega.
* destruct n. inversion H.
  simpl.
  simpl in H.
  pose proof (IHl _ H).
  omega.
}
Qed.

Theorem firstn_all_2 : forall A (l : list A) n,
 (n >= length l)%nat -> firstn n l = l.
Proof.
induction l;intros.
* apply firstn_nil.
* destruct n. inversion H.
  simpl in H.
  simpl.
  f_equal.
  apply IHl.
  omega.
Qed.


Lemma skipn_comp: forall A (l : list A) a b,
  skipn a (skipn b l) = skipn (a + b) l.
Proof.
induction l;intros.
* repeat (rewrite skipn_nil). auto.
* destruct b.
 + simpl. rewrite Nat.add_0_r. auto.
 + simpl.
   rewrite  Nat.add_succ_r.
   simpl.
   apply IHl.
Qed.