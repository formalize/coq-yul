From Coq Require Import Arith NArith JMeq.
Require FSet Map.
Require Tower.

(* Two partial functions are Compat if they coincide on the intersection of their domains. *)
Definition Compat {Key Value: Type}
                   {KeyEqDec: forall x y: Key, {x = y} + {x <> y}}
                   {KeySet: Type}
                   {KeySetImpl: FSet.class KeyEqDec KeySet}
                   {s1 s2: KeySet}
                   (f1: forall key: Key, FSet.has s1 key = true -> Value)
                   (f2: forall key: Key, FSet.has s2 key = true -> Value)
:= forall key: Key,
     match FSet.has s1 key as z return _ = z -> _ with
     | false => fun _ => True
     | true => fun ok1 => match FSet.has s2 key as z return _ = z -> _ with
                          | false => fun _ => True
                          | true => fun ok2 => f1 key ok1 = f2 key ok2
                          end eq_refl
     end eq_refl.

Class class {Key: Type} {KeyEqDec: forall x y: Key, {x = y} + {x <> y}}
             {KeySet: Type} (KeySetImpl: FSet.class KeyEqDec KeySet) (Value: Type)
             (D: Tower.t -> Type)
             := {
  empty: D Tower.empty;

  lookup {t: Tower.t} (dict: D t)
         (key: Key) (ok: Tower.has t key = true)
  : Value;

  replace {t: Tower.t} (dict: D t)
          (key: Key) (ok: Tower.has t key = true)
          (new_value: Value)
  : D t;

  replace_ok {t: Tower.t} (dict: D t)
             (x: Key) (OkX: Tower.has t x = true)
             (new_value: Value)
             (y: Key)
             (OkY: Tower.has t y = true):
    lookup (replace dict x OkX new_value) y OkY =
      if KeyEqDec x y 
        then new_value
        else lookup dict y OkY;

  enter_scope {t: Tower.t} (dict: D t)
  : D (Tower.dup t);

  enter_scope_ok {t: Tower.t} (dict: D t):
    Compat (lookup dict) (lookup (enter_scope dict));

  leave_scope {t: Tower.t} (dict: D t) (can_pop: Tower.height t <> 0%N)
  : D (Tower.drop' t can_pop);

  leave_scope_ok {t: Tower.t} (dict: D t) (can_pop: Tower.height t <> 0%N):
    Compat (lookup dict) (lookup (leave_scope dict can_pop));

  insert {t: Tower.t} (dict: D t)
         (key: Key) (ok: Tower.has t key = false)
         (value: Value)
  : D (Tower.add t key);

  insert_inserts {t: Tower.t} (dict: D t) (key: Key) (ok: Tower.has t key = false) (value: Value):
    lookup (insert dict key ok value) key (Tower.add_has key t) = value;

  insert_ok {t: Tower.t} (dict: D t) (key: Key) (ok: Tower.has t key = false) (value: Value):
    Compat (lookup dict) (lookup (insert dict key ok value));
}.

(**************************************************************************************************)

Section DictImpl.

Context {Key: Type} {KeyEqDec: forall x y: Key, {x = y} + {x <> y}}
         {KeySet: Type} (KeySetImpl: FSet.class KeyEqDec KeySet) {Value: Type} {M: Type}
         (MapImpl: Map.class KeyEqDec Value M).

Definition bound_map (t: Tower.t)
:= { m: M | forall x, Tower.has t x = true -> Map.lookup m x <> None }.

Lemma bound_map_empty_spec (x: Key):
  Tower.has Tower.empty x = true -> Map.lookup Map.empty x <> None.
Proof.
intro H. exfalso. unfold Tower.has in H. cbn in H. 
rewrite FSet.empty_ok in H. discriminate.
Qed.

Definition bound_map_lookup (t: Tower.t)
                             (dict: bound_map t)
                             (key: Key)
                             (ok: Tower.has t key = true)
: Value
:= match Map.lookup (proj1_sig dict) key as z return _ = z -> _ with
   | Some x => fun _ => x
   | None => fun E => False_rect _ (proj2_sig dict key ok E)
   end eq_refl.

Lemma bound_map_some_lookup  (t: Tower.t)
                             (dict: bound_map t)
                             (key: Key)
                             (ok: Tower.has t key = true):
  Some (bound_map_lookup t dict key ok) = Map.lookup (proj1_sig dict) key.
Proof.
unfold bound_map_lookup.
remember (fun E => False_rect Value (proj2_sig dict key ok E)) as bad.
generalize bad. clear bad Heqbad.
remember (Map.lookup (proj1_sig dict) key) as l.
destruct l. { trivial. }
symmetry in Heql.
exfalso. exact (proj2_sig dict key ok Heql).
Qed.

Lemma bound_map_replace_spec (t: Tower.t) (dict: bound_map t)
               (key: Key) (ok: Tower.has t key = true)
               (new_value: Value)
               (x: Key)
               (T: Tower.has t x = true):
  Map.lookup (Map.insert (proj1_sig dict) key new_value) x <> None.
Proof.
rewrite Map.insert_ok.
destruct (KeyEqDec key x). { discriminate. }
exact (proj2_sig dict x T).
Qed.

Definition bound_map_replace (t: Tower.t) (dict: bound_map t)
               (key: Key) (ok: Tower.has t key = true)
               (new_value: Value)
: bound_map t
:= exist _ (Map.insert (proj1_sig dict) key new_value)
         (bound_map_replace_spec t dict key ok new_value).

Lemma bound_map_replace_ok (t: Tower.t) (dict: bound_map t) 
                            (x: Key) (OkX: Tower.has t x = true)
                            (new_value: Value)
                            (y: Key)
                            (OkY: Tower.has t y = true):
   bound_map_lookup t (bound_map_replace t dict x OkX new_value) y OkY 
    =
   if KeyEqDec x y
     then new_value
     else bound_map_lookup t dict y OkY.
Proof.
match goal with
|- ?lhs = ?rhs => enough (H: Some lhs = Some rhs)
end.
{ now inversion H. }
rewrite bound_map_some_lookup.
unfold bound_map_replace.
destruct KeyEqDec; cbn; rewrite Map.insert_ok; destruct KeyEqDec; try easy.
symmetry. apply bound_map_some_lookup.
Qed.

Definition bound_map_enter_scope {t: Tower.t} (dict: bound_map t)
: bound_map (Tower.dup t)
:= exist _ (proj1_sig dict) (proj2_sig dict).

Lemma bound_map_enter_scope_ok (t: Tower.t) (dict: bound_map t):
    Compat (bound_map_lookup t dict) (bound_map_lookup t (bound_map_enter_scope dict)).
Proof.
intro x.
remember (fun ok1 : FSet.has (Tower.top t) x = true =>
  (if FSet.has (Tower.top t) x as z return (FSet.has (Tower.top t) x = z -> Prop)
   then
    fun ok2 : FSet.has (Tower.top t) x = true =>
    bound_map_lookup t dict x ok1 = bound_map_lookup t (bound_map_enter_scope dict) x ok2
   else fun _ : FSet.has (Tower.top t) x = false => True) eq_refl) as Y.
assert (YY: forall ok1, Y ok1).
{
  intro ok1. subst Y.
  remember (fun ok2 : FSet.has (Tower.top t) x = true =>
  bound_map_lookup t dict x ok1 = bound_map_lookup t (bound_map_enter_scope dict) x ok2) as Z.
  assert (ZZ: forall (ok2: FSet.has (Tower.top t) x = true), Z ok2).
  {
    intro ok2. subst Z.
    match goal with
    |- ?lhs = ?rhs => enough (H: Some lhs = Some rhs)
    end. { now inversion H. }
    now repeat rewrite bound_map_some_lookup.
  }
  clear HeqZ.
  now destruct FSet.has.
}
clear HeqY.
now destruct FSet.has.
Qed.

Lemma bound_map_leave_scope_spec {t: Tower.t} (dict: bound_map t) (can_pop: Tower.height t <> 0%N)
                                 (x: Key):
  Tower.has (Tower.drop' t can_pop) x = true -> Map.lookup (proj1_sig dict) x <> None.
Proof.
intro H. apply (proj2_sig dict).
destruct t. cbn in *. unfold Tower.has in *. cbn in *.
destruct rest. { contradiction. }
cbn in *.
assert (Sub := FSet.is_subset_ok head top).
destruct Sub as (SubR, SubL). 
assert (W := SubR Ok x).
rewrite H in W.
cbn in W. exact W.
Qed.

Definition bound_map_leave_scope {t: Tower.t} (dict: bound_map t) (can_pop: Tower.height t <> 0%N)
: bound_map (Tower.drop' t can_pop)
:= exist _ (proj1_sig dict) (bound_map_leave_scope_spec dict can_pop).

Lemma bound_map_leave_scope_ok (t: Tower.t) (dict: bound_map t) (can_pop: Tower.height t <> 0%N):
    Compat (bound_map_lookup _ dict) (bound_map_lookup _ (bound_map_leave_scope dict can_pop)).
Proof.
intro x.
remember (fun ok1 : FSet.has (Tower.top t) x = true =>
  (if FSet.has (Tower.top (Tower.drop' t can_pop)) x as z
    return (FSet.has (Tower.top (Tower.drop' t can_pop)) x = z -> Prop)
   then
    fun ok2 : FSet.has (Tower.top (Tower.drop' t can_pop)) x = true =>
    bound_map_lookup t dict x ok1 =
    bound_map_lookup (Tower.drop' t can_pop) (bound_map_leave_scope dict can_pop) x ok2
   else fun _ : FSet.has (Tower.top (Tower.drop' t can_pop)) x = false => True) eq_refl) as B.
assert (BB: forall ok1, B ok1).
{
  intro ok1. subst B.
  remember (fun ok2 : FSet.has (Tower.top (Tower.drop' t can_pop)) x = true =>
  bound_map_lookup t dict x ok1 =
  bound_map_lookup (Tower.drop' t can_pop) (bound_map_leave_scope dict can_pop) x ok2) as C.
  assert (CC: forall ok2, C ok2).
  {
    intro ok2. subst C.
    match goal with
    |- ?lhs = ?rhs => enough (H: Some lhs = Some rhs)
    end. { now inversion H. }
    now repeat rewrite bound_map_some_lookup.
  }
  clear HeqC.
  now destruct (FSet.has (Tower.top (Tower.drop' t can_pop))).
}
clear HeqB.
now destruct FSet.has.
Qed.

Lemma bound_map_insert_spec {t: Tower.t} (dict: bound_map t)
                             (key: Key) (ok: Tower.has t key = false)
                             (value: Value)
                             (x: Key)
                             (T: Tower.has (Tower.add t key) x = true):
  Map.lookup (Map.insert (proj1_sig dict) key value) x <> None.
Proof.
rewrite Map.insert_ok.
unfold Tower.has in T. cbn in T.
rewrite FSet.add_ok in T.
destruct KeyEqDec. { discriminate. }
apply (proj2_sig dict). exact T.
Qed.

Definition bound_map_insert {t: Tower.t} (dict: bound_map t)
                             (key: Key) (ok: Tower.has t key = false)
                             (value: Value)
: bound_map (Tower.add t key)
:= exist _ (Map.insert (proj1_sig dict) key value)
         (bound_map_insert_spec dict key ok value).

Lemma bound_map_insert_inserts (t: Tower.t) (dict: bound_map t)
                                (key: Key) (ok: Tower.has t key = false)
                                (value: Value):
  bound_map_lookup (Tower.add t key)
                   (bound_map_insert dict key ok value)
                   key
                   (Tower.add_has key t)
   = 
  value.
Proof.
unfold bound_map_lookup. cbn.
remember (fun E => 
           False_rect Value (bound_map_insert_spec dict key ok value key (Tower.add_has key t) E)) as B.
generalize B. clear B HeqB.
rewrite Map.insert_ok.
now destruct KeyEqDec.
Qed.

Lemma bound_map_insert_ok (t: Tower.t) (dict: bound_map t)
                           (key: Key) (ok: Tower.has t key = false)
                           (value: Value):
  Compat (bound_map_lookup t dict)
         (bound_map_lookup (Tower.add t key)
            (bound_map_insert dict key ok value)).
Proof.
intro x.
remember (fun ok1 : FSet.has (Tower.top t) x = true =>
  (if FSet.has (Tower.top (Tower.add t key)) x as z
    return (FSet.has (Tower.top (Tower.add t key)) x = z -> Prop)
   then
    fun ok2 : FSet.has (Tower.top (Tower.add t key)) x = true =>
    bound_map_lookup t dict x ok1 =
    bound_map_lookup (Tower.add t key) (bound_map_insert dict key ok value) x ok2
   else fun _ : FSet.has (Tower.top (Tower.add t key)) x = false => True) eq_refl) as U.
assert (UU: forall H, U H).
{
  intro ok1. subst.
  remember (fun ok2 : FSet.has (Tower.top (Tower.add t key)) x = true =>
  bound_map_lookup t dict x ok1 =
  bound_map_lookup (Tower.add t key) (bound_map_insert dict key ok value) x ok2) as V.
  assert (VV: forall H, V H).
  {
    intro ok2. subst.
    match goal with
    |- ?lhs = ?rhs => enough (H: Some lhs = Some rhs)
    end. { now inversion H. }
    repeat rewrite bound_map_some_lookup.
    cbn.
    rewrite Map.insert_ok.
    destruct KeyEqDec; trivial.
    subst.
    unfold Tower.has in ok.
    rewrite ok in ok1.
    discriminate.
  }
  clear HeqV.
  now destruct (FSet.has (Tower.top (Tower.add t key))).
}
clear HeqU.
now destruct FSet.has.
Qed.

Definition bound_map_dict_impl
: class KeySetImpl Value bound_map
:= {|
      empty := exist _ Map.empty bound_map_empty_spec;
      lookup := bound_map_lookup;
      replace := bound_map_replace;
      replace_ok := bound_map_replace_ok; 
      enter_scope _ map := bound_map_enter_scope map;
      enter_scope_ok := bound_map_enter_scope_ok;
      leave_scope _ map := bound_map_leave_scope map;
      leave_scope_ok := bound_map_leave_scope_ok;
      insert _ map := bound_map_insert map;
      insert_inserts := bound_map_insert_inserts;
      insert_ok := bound_map_insert_ok;
   |}.

End DictImpl.

(**************************************************************************************************)

Section Dict.

Context {Key: Type} {KeyEqDec: forall x y: Key, {x = y} + {x <> y}}
         {KeySet: Type} {KeySetImpl: FSet.class KeyEqDec KeySet} {Value: Type}
         {D: Tower.t -> Type}
         {Dict: class KeySetImpl Value D}.

(* A simple case of dict_replace_ok, similar to dict_insert_inserts. *)
Lemma replace_replaces (t: Tower.t)
                        (d: D t)
                        (key: Key) (ok: Tower.has t key = true)
                        (value: Value):
    lookup (replace d key ok value) key ok = value.
Proof.
rewrite replace_ok. now destruct KeyEqDec.
Qed.

Program Fixpoint leave_scopes {t: Tower.t} (dict: D t) (n: nat) 
                                (ok: n <= N.to_nat (Tower.height t))
: D (Tower.dropn t n ok)
:= match n as n' return (n = n' -> _) with
   | O => fun e => 
      match _: t = Tower.dropn t n ok 
      in (_ = z) return D z with
      | eq_refl => dict
      end
   | S k => fun e =>
      match _: Tower.dropn (Tower.drop' t (Tower.dropn_helper1 t n ok k e))
                            k 
                            (Tower.dropn_helper2 t n ok k e) 
                = Tower.dropn t n ok
      in (_ = z) return D z with
      | eq_refl => leave_scopes (leave_scope dict _) k _
      end
   end eq_refl.

(**
  Leaves several scopes to arrive at the scope with the given nesting level.
  Doesn't change the dictionary if the new level is higher than the old.
 *)
Definition set_scope_level {t: Tower.t} (dict: D t) (new_height: N)
: D (Tower.set_height t new_height)
:= leave_scopes dict (N.to_nat (Tower.height t - new_height)) (Tower.set_height_helper _ _).

End Dict.
