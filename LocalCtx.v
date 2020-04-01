From Coq Require Import NArith.
Require Tower.
Require Dict.
Require Import Config UntypedAST DynError.

Record yul_fun {C: yul_config} := {
  fun_name: yc_ident;
  fun_inputs: list typename;
  fun_outputs: list typename;
  fun_body: block;

  (**
    The nesting level is the amount of block boundaries (curly braces)
    between the function definition and the global level.
    As an exception, for-loops have an apparently additional nesting level
    because logically the entire for-loop is within its initializer block.
   *)
  fun_nesting_level: N;
}.

Instance yc_identmap_fun_impl {C: yul_config}
: Dict.class yc_identset_impl yul_fun (yc_identmap yul_fun)
:= yc_identmap_impl yul_fun.

Record local_ctx {C: yul_config} := {
  loc_funs: layered_dict yul_fun;

  (* Local variables start at the outermost function definition or on the global level. *)
  loc_vars: layered_dict dynamic_value;
}.

Fixpoint bind_vars_to_values {C: yul_config}
                              (vars: list typename)
                              (init: list dynamic_value)
                              (dict: layered_dict dynamic_value)
: dynamic_error + layered_dict dynamic_value
:= match vars with
   | nil =>
      match init with
      | nil => inr dict
      | _ => inl DE_TooManyValues
      end
   | cons (vtype, vname) vtail =>
      match init with
      | nil => inl DE_TooFewValues
      | cons ihead itail =>
          match ihead with
          | existT _ itype ivalue =>
              if yc_type_eq_dec vtype itype then
                match Tower.has (layered_dict_domain dict) vname as z return (_ = z -> _) with
                | true => fun _ => inl DE_LocalNameShadowing
                | false => fun e =>
                      bind_vars_to_values vtail itail
                                          {| 
                                             layered_dict_map := Dict.insert (layered_dict_map dict)
                                                                             vname e ihead 
                                          |}
                end eq_refl
              else inl DE_VarTypeMismatch
         end
      end
   end.

Fixpoint rebind_vars_to_values {C: yul_config}
                                (names: list yc_ident)
                                (values: list dynamic_value)
                                (dict: layered_dict dynamic_value)
: dynamic_error + layered_dict dynamic_value
:= match names with
   | nil =>
      match values with
      | nil => inr dict
      | _ => inl DE_TooManyValues
      end
   | cons name ntail =>
      match values with
      | nil => inl DE_TooFewValues
      | cons vhead vtail =>
          match vhead with
          | existT _ vtype vvalue =>
                match Tower.has (layered_dict_domain dict) name as z return (_ = z -> _) with
                | false => fun _ => inl DE_CannotResolveVariable
                | true => fun e =>
                      let old_value := Dict.lookup (layered_dict_map dict) name e in
                      if yc_type_eq_dec vtype (projT1 old_value) then
                        rebind_vars_to_values ntail vtail
                                            {| 
                                               layered_dict_map := Dict.replace (layered_dict_map dict)
                                                                                name e vhead
                                            |}
                      else inl DE_VarTypeMismatch
                end eq_refl
         end
      end
   end.

Fixpoint bind_vars_to_zeros {C: yul_config}
                             (vars: list typename)
                             (dict: layered_dict dynamic_value)
: dynamic_error + layered_dict dynamic_value
:= match vars with
   | nil => inr dict
   | cons (type, name) tail =>
      match Tower.has (layered_dict_domain dict) name as z return (_ = z -> _) with
      | true => fun _ => inl DE_LocalNameShadowing
      | false => fun e =>
          bind_vars_to_zeros tail 
                             {|
                               layered_dict_map := Dict.insert (layered_dict_map dict)
                                                               name e
                                                               (existT _ type (yc_zero_value type))
                             |}
      end eq_refl
   end.

(**
  Make a new local context for entering a function.
  This could be called "creating a stack frame", but we don't model an explicit stack here.
 *)
Definition enter_fun {C: yul_config}
                      (loc: local_ctx)
                      (f: yul_fun)
                      (args: list dynamic_value)
: dynamic_error + local_ctx
:= match bind_vars_to_values (fun_inputs f) args {| layered_dict_map :=  Dict.empty |} with
   | inl err => inl err
   | inr args_dict =>
      match bind_vars_to_zeros (fun_outputs f) args_dict with
      | inl err => inl err
      | inr vars =>
          inr {|
                loc_funs :=
                  {| 
                     layered_dict_map := Dict.set_scope_level (layered_dict_map (loc_funs loc))
                                                              (fun_nesting_level f)
                  |};
                loc_vars := vars;
              |}
      end
   end.

Fixpoint get_vars_by_typenames {C: yul_config}
                                (tns: list typename)
                                (vars: layered_dict dynamic_value)
: dynamic_error + list dynamic_value
:= match tns with
   | nil => inr nil
   | cons (type, name) rest =>
       match Tower.has (layered_dict_domain vars) name as z return (_ = z -> _) with
       | false => fun _ => inl DE_InternalErrorOutputNotFound
       | true => fun found =>
           let first_result := Dict.lookup (layered_dict_map vars) name found in
           match get_vars_by_typenames rest vars with
           | inl err => inl err
           | inr rest_results => inr (cons first_result rest_results)
           end
       end eq_refl
   end.

(**
  Evacuate the output values from the "stack frame" before abandoning it.
 *)
Definition leave_fun {C: yul_config}
                      (loc: local_ctx)
                      (f: yul_fun)
: dynamic_error + list dynamic_value
:= get_vars_by_typenames (fun_outputs f) (loc_vars loc).

Definition loc_enter_scope {C: yul_config}
                            (loc: local_ctx)
: local_ctx
:= {|
     loc_funs := {| 
                    layered_dict_map := Dict.enter_scope (layered_dict_map (loc_funs loc))
                 |};
     loc_vars := {|
                    layered_dict_map := Dict.enter_scope (layered_dict_map (loc_vars loc));
                 |}
   |}.

(* This is a hack. Is it better to explicitly control fun/var nesting levels? *)
Definition loc_leave_scope {C: yul_config}
                            (loc: local_ctx)
: local_ctx
:= {|
     loc_funs := match N.eq_dec (Tower.height (layered_dict_domain (loc_funs loc))) 0 with
                 | right ne => 
                     {| 
                        layered_dict_map := Dict.leave_scope (layered_dict_map (loc_funs loc)) ne
                     |}
                 | left _ => loc_funs loc
                 end;
     loc_vars := match N.eq_dec (Tower.height (layered_dict_domain (loc_vars loc))) 0 with
                 | right ne => 
                     {| 
                        layered_dict_map := Dict.leave_scope (layered_dict_map (loc_vars loc)) ne
                     |}
                 | left _ => loc_vars loc
                 end
   |}.