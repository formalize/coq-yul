From Coq Require Import NArith Eqdep_dec.
Require FSet Tower Dict.

Record gas_schedule := {
  gs_break:    N;
  gs_continue: N;
  gs_leave:    N;
  (* do we still need this?
  (* 
     A fee to pay upfront for every statement. Blocks pay this fee one extra time upon entering.
     This simplifies the interpreter because stuff like {}{}{}{} or {{{{}}}} 
     can be unwound within the same induction by clock as everything else.
   *)
  gs_step:     N;
  *)
}.

Definition minimal_gas_schedule := {|
  gs_break := 1;
  gs_continue := 1;
  gs_leave := 1;
  (* gs_step := 1; *)
|}.

Class yul_config := {
  yc_type: Type;
  yc_type_eq_dec: forall x y: yc_type, {x = y} + {x <> y};
  yc_value: yc_type -> Type;
  yc_value_eq_dec: forall {t: yc_type} (x y: yc_value t), {x = y} + {x <> y};
  yc_cast_to_bool: forall t: yc_type, yc_value t -> bool;
  yc_zero_value: forall t: yc_type, yc_value t;

  yc_ident: Type;
  (* Something carried by every abort.
     Triggered by functions such as stop(), return(), revert(). 
   *)
  yc_ident_eq_dec: forall x y: yc_ident, {x = y} + {x <> y};
  yc_identset: Type;
  yc_identset_impl: FSet.class yc_ident_eq_dec yc_identset;

  yc_identmap: Type -> Tower.t -> Type;
  yc_identmap_impl (v: Type): Dict.class yc_identset_impl v (yc_identmap v);

  yc_abort_data: Type;
  yc_out_of_gas: yc_abort_data;

  yc_global_ctx: Type;

  yc_get_builtin_fun: 
    yc_ident -> option (
      (* the world before: *) yc_global_ctx -> (* inputs: *) list { t : yc_type & yc_value t } ->
        (* the world after: *) yc_global_ctx *
        (* outputs: *) list { t : yc_type & yc_value t } *
        (* maybe error: *) option yc_abort_data);

  yc_gas_schedule: gas_schedule;
}.

Definition yc_identtower {C: yul_config} := let _ := yc_identset_impl in Tower.t.
(* FIXME get rid of this *)
Record layered_dict {C: yul_config} (v: Type) := {
  layered_dict_domain: yc_identtower;
  layered_dict_map: yc_identmap v layered_dict_domain;
}.
Arguments layered_dict_domain {_ _}.
Arguments layered_dict_map {_ _}. 

Definition dynamic_value {C: yul_config} := { t : yc_type & yc_value t }.

Instance yc_identmap_dynamic_value_impl {C: yul_config}
: Dict.class yc_identset_impl dynamic_value (yc_identmap dynamic_value)
:= yc_identmap_impl dynamic_value.

Instance yc_identmap_type_impl {C: yul_config}
: Dict.class yc_identset_impl yc_type (yc_identmap yc_type)
:= yc_identmap_impl yc_type.

Program Definition dynamic_value_eq_dec {C: yul_config} (x y: dynamic_value)
: {x = y} + {x <> y}
:= match yc_type_eq_dec (projT1 x) (projT1 y) with
   | left e =>
       if yc_value_eq_dec (projT2 x)
                          (match eq_sym e in (_ = z) return yc_value z with
                           | eq_refl => projT2 y
                           end)
                 then left eq_refl
                 else right _
   | right ne => right _
   end.
Next Obligation.
destruct x as (t', x).
destruct y as (t, y).
cbn in *. subst. cbn in *. subst. trivial.
Qed.
Next Obligation.
destruct x as (t', x).
destruct y as (t, y).
intro E.
cbn in *.
assert (P := projT2_eq E). cbn in P. unfold projT1_eq in P. unfold f_equal in P.
subst t'. cbn in *.
assert (G: forall Q: t = projT1 (existT (fun t : yc_type => yc_value t) t y),
             eq_rect t (fun a : yc_type => yc_value a) x t Q <> y).
{
  intro Q. cbn in Q.
  assert (K: Q = eq_refl).
  {
    apply eq_proofs_unicity.
    intros a b.
    destruct (yc_type_eq_dec a b). { now left. } { now right. }
  }
  now subst Q.
}
now apply G in P.
Qed.
