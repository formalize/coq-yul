From Coq Require Import Arith NArith.
Require FSet.

Section Towers.

Context {M: Type} {E: forall x y: M, {x = y} + {x <> y}} {SetOfM: Type} {C: FSet.class E SetOfM}.

Inductive bound_tower (s: SetOfM) (height: N) := 
| Nil (E: height = 0%N)
| Cons (head: SetOfM)
       (tail_height: N) (tail: bound_tower head tail_height)
       (Ok: FSet.is_subset head s = true)
       (HeightOk: height = N.succ tail_height).

(** A tower is a nonempty stack of sets in which each set is a subset of those above it,
    thus the top set is the largest.
    The height of a single-set ("flat") tower is 0.
 *)
Record t := {
  top: SetOfM;
  height: N;
  rest: bound_tower top height;
}.

Definition empty := 
{|
   top := FSet.empty;
   height := 0%N;
   rest := Nil FSet.empty 0%N eq_refl;
|}.

Definition singleton (s: SetOfM) := 
{|
   top := s;
   height := 0%N;
   rest := Nil s 0%N eq_refl;
|}.

Definition cons (s: SetOfM) (tower: t)
                 (ok: FSet.is_subset (top tower) s = true)
:= {|
     top := s;
     height := N.succ (height tower);
     rest := Cons _ _ (top tower) (height tower) (rest tower) ok eq_refl;
   |}.

Definition bound_tower_cast {smaller: SetOfM} {height: N}
                             (bt: bound_tower smaller height)
                             {larger: SetOfM}
                             (sub: FSet.is_subset smaller larger = true)
: bound_tower larger height
:= match bt with
   | Nil _ _ E => Nil larger _ E
   | Cons _ _ head tail_height tail Ok HOk =>
      Cons larger _ head tail_height tail (FSet.is_subset_trans Ok sub) HOk
   end.

Definition has (tower: t) (x: M)
:= FSet.has (top tower) x.

(** Add an element to the top set of the tower. *)
Definition add (tower: t) (x: M)
: t
:= let new_top := FSet.add (top tower) x
    in {| 
          top := new_top;
          rest := bound_tower_cast (rest tower) (FSet.add_subset x (top tower))
        |}.

Lemma add_has (x: M) (tower: t):
  has (add tower x) x = true.
Proof.
apply FSet.add_has.
Qed.

Definition dup (tower: t)
: t
:= {|
      top := top tower;
      rest := Cons (top tower) (N.succ (height tower))
                   (top tower)
                   (height tower)
                   (rest tower)
                   (FSet.is_subset_refl (top tower))
                   eq_refl;
    |}.

(* Removes the top level of the tower unless it's the only one. *)
Definition drop (tower: t)
: t
:= match rest tower as r return (_ = r -> _) with
   | Nil _ _ e => fun Q => tower
   | Cons _ _ head tail_height tail Ok HOk => fun _ =>
      {|
          top := head;
          height := tail_height;
          rest := tail;
       |}
   end eq_refl.

(* Removes the top level of the tower. *)
Definition drop' (tower: t) (ok: height tower <> 0%N)
: t
:= match rest tower as r return (_ = r -> _) with
   | Nil _ _ e => fun Q => False_rect _ (ok e)
   | Cons _ _ head tail_height tail Ok HOk => fun _ =>
      {|
          top := head;
          height := tail_height;
          rest := tail;
       |}
   end eq_refl. 

Lemma dup_drop (tower: t):
  drop (dup tower) = tower.
Proof.
destruct tower; trivial.
Qed.

Lemma dup_drop' (tower: t):
  drop' (dup tower) (N.neq_succ_0 _) = tower.
Proof.
destruct tower; trivial.
Qed.

Lemma drop'_height_succ (tower: t) (ok: height tower <> 0%N):
  height tower = N.succ (height (drop' tower ok)).
Proof.
unfold drop'. now destruct rest.
Qed.

Lemma drop_height (tower: t):
  height (drop tower) = N.pred (height tower).
Proof.
destruct tower as (top, height, rest). 
destruct rest; cbn; subst. { trivial. }
rewrite N.pred_succ. trivial.
Qed.

Lemma drop'_height (tower: t) (ok: height tower <> 0%N):
  height (drop' tower ok) = N.pred (height tower).
Proof.
rewrite (drop'_height_succ tower ok).
rewrite N.pred_succ.
trivial.
Qed.

Lemma dropn_helper1 (tower: t) (n: nat) (ok: n <= N.to_nat (height tower))
                     (k: nat) (e: n = S k):
  height tower <> 0%N.
Proof.
subst n. apply le_S_gt in ok. unfold gt in ok. apply Nat.lt_lt_0 in ok.
now destruct (height tower).
Qed.

Lemma dropn_helper2 (tower: t) (n: nat) (ok: n <= N.to_nat (height tower))
                           (k: nat) (e: n = S k):
 k <= N.to_nat (height (drop' tower (dropn_helper1 tower n ok k e))).
Proof.
subst n.
rewrite drop'_height.
destruct height; auto with arith.
clear M E SetOfM C tower.
apply le_S_n.
rewrite<- N2Nat.inj_succ.
now rewrite N.succ_pred.
Qed.

Fixpoint dropn (tower: t) (n: nat) (ok: n <= N.to_nat (height tower))
: t
:= match n as n' return (n = n' -> _) with
   | O => fun _ => tower
   | S k => fun e => 
      dropn (drop' tower
                   (dropn_helper1 tower n ok k e)) 
                   k 
                   (dropn_helper2 tower n ok k e)
   end eq_refl.

Lemma dropn_height (tower: t) (n: nat) (ok: n <= N.to_nat (height tower)):
  height (dropn tower n ok) = (height tower - N.of_nat n)%N.
Proof.
generalize tower ok. clear tower ok. induction n. { symmetry. apply N.sub_0_r. }
intros tower ok. cbn. rewrite IHn. rewrite drop'_height. 
remember (N.pred (height tower)) as m.
assert(Q: height tower = N.succ m).
{
  subst m. symmetry. apply N.succ_pred.
  now destruct height.
}
rewrite Q in *. clear Q.
assert (R: N.pos (Pos.of_succ_nat n) = N.succ (N.of_nat n)).
{ now destruct n. }
rewrite R. clear R.
symmetry. apply N.sub_succ.
Qed.

Lemma set_height_helper (x y: N):
  N.to_nat (y - x) <= N.to_nat y.
Proof.
rewrite nat_compare_le.
rewrite Nat2N.inj_compare.
repeat rewrite N2Nat.id.
apply N.le_sub_l.
Qed.

(* The tower is unchanged if the new height is too big. *)
Definition set_height (tower: t) (new_height: N)
:= dropn tower (N.to_nat (height tower - new_height)) (set_height_helper _ _).

Lemma set_height_ok (tower: t) (new_height: N) (ok: (new_height <= height tower)%N):
  height (set_height tower new_height) = new_height.
Proof.
unfold set_height. rewrite dropn_height.
rewrite N2Nat.id.
apply N.add_sub_eq_l.
now apply N.sub_add.
Qed.

(*********************************************************************************)


Fixpoint bound_tower_set_union {top: SetOfM} {height: N} (bt: bound_tower top height) (s: SetOfM)
: bound_tower (FSet.union top s) height
:= match bt with
   | Nil _ _ e => Nil _ _ e
   | Cons _ _ head tail_height tail Ok HOk =>
       Cons _ _ (FSet.union head s) tail_height (bound_tower_set_union tail s)
            (FSet.union_monotonic_l head top s Ok) HOk
   end.

(* XXX: can be generalized by mapping an arbitrary monotonic op onto the tower *)
(** Unite every level of the tower with the given set. *)
Definition set_union (tower: t) (s: SetOfM)
: t
:= {|
      top := FSet.union (top tower) s;
      height := height tower;
      rest := bound_tower_set_union (rest tower) s;
   |}.

Fixpoint bound_tower_set_inter {top: SetOfM} {height: N} (bt: bound_tower top height) (s: SetOfM)
: bound_tower (FSet.inter top s) height
:= match bt with
   | Nil _ _ e => Nil _ _ e
   | Cons _ _ head tail_height tail Ok HOk =>
       Cons _ _ (FSet.inter head s) tail_height (bound_tower_set_inter tail s)
            (FSet.inter_monotonic_l head top s Ok) HOk
   end.

(** Intersect every level of the tower with the given set. *)
Definition set_inter (tower: t) (s: SetOfM)
: t
:= {|
      top := FSet.inter (top tower) s;
      height := height tower;
      rest := bound_tower_set_inter (rest tower) s;
   |}.

(*********************************************************************************)

Fixpoint bound_tower_bottom {top: SetOfM} {height: N} (bt: bound_tower top height)
: SetOfM
:= match bt with
   | Nil _ _ e => top
   | Cons _ _ head tail_height tail Ok HOk =>
       bound_tower_bottom tail
   end.

Definition bottom (tower: t) := bound_tower_bottom (rest tower).

Lemma dup_bottom (tower: t):
  bottom (dup tower) = bottom tower.
Proof.
trivial.
Qed.

Lemma drop_bottom (tower: t):
  bottom (drop tower) = bottom tower.
Proof.
destruct tower as (top, height, bt). cbn.
now destruct bt.
Qed.

Program Fixpoint bound_tower_stack
  {upper_top: SetOfM} {upper_height: N} (bt_upper: bound_tower upper_top upper_height)
  {lower_top: SetOfM} {lower_height: N} (bt_lower: bound_tower lower_top lower_height)
  (ok: FSet.is_subset lower_top (bound_tower_bottom bt_upper) = true)
: bound_tower upper_top (N.succ (upper_height + lower_height))
:= match bt_upper with
   | Nil _ _ e => Cons _ _ lower_top lower_height bt_lower _ _
   | Cons _ _ head tail_height tail Ok HOk =>
       Cons _ _ head _ (bound_tower_stack tail bt_lower _) _ _
   end.
Next Obligation.
f_equal. apply N.add_succ_l.
Qed.

Definition stack (upper lower: t) 
                  (ok: FSet.is_subset (top lower) (bottom upper) = true)
: t
:= {|
      top := top upper;
      height := N.succ (height upper + height lower);
      rest := bound_tower_stack (rest upper) (rest lower) ok;
   |}.

Lemma stack_singleton (s: SetOfM) (tower: t)
                       (ok: FSet.is_subset (top tower) s = true):
  stack (singleton s) tower ok = cons s tower ok.
Proof.
trivial.
Qed.

Definition cons_union (s: SetOfM) (tower: t)
:= {|
     top := FSet.union (top tower) s;
     height := N.succ (height tower);
     rest := Cons _ _ (top tower) (height tower) (rest tower) 
                  (FSet.union_subset_l _ _)
                  eq_refl;
   |}.

End Towers.