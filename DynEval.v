From Coq Require Import Arith NArith.

Require FSet Tower Dict.
Require Import Config.
Require Import UntypedAST.
Require Import DynError.
Require Import LocalCtx.

Inductive mode {C: yul_config}
:= ModeRegular
 | ModeBreak
 | ModeContinue
 | ModeLeave (* called return in most languages *)
 | ModeAbort (abort: yc_abort_data).

Inductive stmt_eval_result {C: yul_config}
:= StmtEvalResult (new_glob: yc_global_ctx) (new_loc: local_ctx) (mode: mode).
Arguments StmtEvalResult {_}.

Inductive expr_eval_result {C: yul_config}
:= ExprEvalSuccess (new_glob: yc_global_ctx)
                   (new_loc: local_ctx)
                   (values: list dynamic_value)
 | ExprEvalAbort (new_glob: yc_global_ctx)
                 (new_loc: local_ctx)
                 (abort: yc_abort_data).

Class dynamic_eval_config {C: yul_config}:= {
  wrap_dynamic_error: dynamic_error -> yc_abort_data;
}.

(**
    Prepend a newly computed result to a tuple of computed values.
    The newly computed result must contain exactly one value,
    otherwise [DE_ExactlyOneValueExpected] will be "thrown".
 *)
Definition cons_eval_results {C: yul_config} {D: dynamic_eval_config}
                              (head: expr_eval_result)
                              (tail: list dynamic_value)
: expr_eval_result
:= match head with
   | ExprEvalAbort _ _ _ => head
   | ExprEvalSuccess glob loc values =>
      match values as values' return (values = values' -> _) with
      | (v :: nil)%list => fun E =>
        ExprEvalSuccess glob loc
                        (v :: tail)%list
      | _ => fun _ =>
        ExprEvalAbort glob loc (wrap_dynamic_error DE_ExactlyOneValueExpected)
      end eq_refl
   end.

(** Add all the function declarations in the given statement list to the dictionary.
    Check that none of the functions shadows builtins or existing functions.
 *)
Fixpoint bind_funs {C: yul_config}
                    (funs: layered_dict yul_fun) 
                    (decls: list stmt)
                    (nesting_level: N)
: dynamic_error + layered_dict yul_fun
:= match decls with
   | nil => inr funs
   | (FunDef name inputs outputs body :: tail)%list =>
       match yc_get_builtin_fun name with
       | Some _ => inl DE_BuiltinFunctionShadowing
       | None =>
          match Tower.has (layered_dict_domain funs) name as z return (_ = z -> _) with
          | true => fun _ => inl DE_LocalFunctionShadowing
          | false => fun e =>
             bind_funs {|
                           layered_dict_map :=
                              Dict.insert (layered_dict_map funs)
                              name e
                              {|
                                fun_name := name;
                                fun_inputs := inputs;
                                fun_outputs := outputs;
                                fun_body := body;
                                fun_nesting_level := nesting_level;
                              |}
                       |}
                       tail
                       nesting_level
          end eq_refl
       end
   | (_ :: tail)%list => (* ignore statements that are not function declarations *)
        bind_funs funs tail nesting_level
   end.

(* This is a fueled big-step semantics without Ethereum gas metering.
 * Throws yc_out_of_gas if it runs out of fuel.
 * Note that the fuel controls Coq's recursion depth rather than time.
 *)
Fixpoint eval_stmt {C: yul_config} {D: dynamic_eval_config}
       (glob: yc_global_ctx)
       (loc: local_ctx)
       (nesting_level: N)
       (s: stmt)
       (fuel: nat)
{struct fuel}
: stmt_eval_result
:= match fuel with
   | O => StmtEvalResult glob loc (ModeAbort yc_out_of_gas)
   | S remaining_fuel =>
      match s with
      | FunDef _ _ _ _ => StmtEvalResult glob loc ModeRegular (* do nothing *)
      | Break    => StmtEvalResult glob loc ModeBreak
      | Continue => StmtEvalResult glob loc ModeContinue
      | Leave    => StmtEvalResult glob loc ModeLeave
      | BlockStmt block => eval_block glob loc nesting_level block remaining_fuel
      | VarDef vars None =>
          match bind_vars_to_zeros vars (loc_vars loc) with
          | inl err => StmtEvalResult glob loc (ModeAbort (wrap_dynamic_error err))
          | inr new_loc_vars =>
                StmtEvalResult glob 
                               {|
                                  loc_funs := loc_funs loc;
                                  loc_vars := new_loc_vars;
                                |}
                               ModeRegular
          end
      | VarDef vars (Some init) =>
          match eval_expr glob loc init remaining_fuel with
          | ExprEvalSuccess  new_glob new_loc values => 
              match bind_vars_to_values vars values (loc_vars loc) with
              | inl err => StmtEvalResult glob loc (ModeAbort (wrap_dynamic_error err))
              | inr new_loc_vars =>
                    StmtEvalResult glob 
                                   {|
                                      loc_funs := loc_funs loc;
                                      loc_vars := new_loc_vars;
                                    |}
                                   ModeRegular
              end
          | ExprEvalAbort    new_glob new_loc abort =>
              StmtEvalResult new_glob new_loc (ModeAbort abort)
          end
      | Assign vars expr =>
          match eval_expr glob loc expr remaining_fuel with
          | ExprEvalAbort    glob' loc' abort =>
              StmtEvalResult glob' loc' (ModeAbort abort)
          | ExprEvalSuccess  glob' loc' values =>
              match rebind_vars_to_values vars values (loc_vars loc') with
              | inl err => StmtEvalResult glob' loc' (ModeAbort (wrap_dynamic_error err))
              | inr new_loc_vars =>
                  StmtEvalResult glob'
                                 {|
                                    loc_funs := loc_funs loc;
                                    loc_vars := new_loc_vars;
                                 |}
                                 ModeRegular
             end
          end
      | Expr expr =>
          match eval_expr glob loc expr remaining_fuel with
          | ExprEvalSuccess  new_glob new_loc values => 
              StmtEvalResult new_glob new_loc ModeRegular
          | ExprEvalAbort    new_glob new_loc abort =>
              StmtEvalResult new_glob new_loc (ModeAbort abort)
          end
      | If cond body =>
          match eval_expr glob loc cond remaining_fuel with
          | ExprEvalAbort    new_glob new_loc abort =>
              StmtEvalResult new_glob new_loc (ModeAbort abort)
          | ExprEvalSuccess  new_glob new_loc (value :: nil) =>
              if yc_cast_to_bool (projT1 value) (projT2 value)
                then eval_block new_glob new_loc nesting_level body remaining_fuel
                else StmtEvalResult new_glob new_loc ModeRegular
          | ExprEvalSuccess  new_glob new_loc _ =>
              StmtEvalResult new_glob new_loc 
                             (ModeAbort (wrap_dynamic_error DE_ExactlyOneValueExpected))
          end
      | Switch expr cases default =>
          match eval_expr glob loc expr remaining_fuel with
          | ExprEvalAbort    new_glob new_loc abort =>
              StmtEvalResult new_glob new_loc (ModeAbort abort)
          | ExprEvalSuccess  new_glob new_loc (value :: nil) =>
              eval_switch new_glob new_loc nesting_level value cases default remaining_fuel
          | ExprEvalSuccess  new_glob new_loc _ =>
              StmtEvalResult new_glob new_loc 
                             (ModeAbort (wrap_dynamic_error DE_ExactlyOneValueExpected))
          end
      | For (Block init_statements) cond after body =>
          let new_level := N.succ nesting_level in
          let new_scope := loc_enter_scope loc in
          match bind_funs (loc_funs new_scope) init_statements new_level with
          | inl err => StmtEvalResult glob loc (ModeAbort (wrap_dynamic_error err))
          | inr funs =>
              (* run init *)
              match eval_stmt_list glob 
                     {|
                         loc_funs := funs;
                         loc_vars := loc_vars new_scope;
                     |}
                     new_level init_statements remaining_fuel 
              with
              | StmtEvalResult glob' loc' (ModeAbort abort) =>
                  StmtEvalResult glob' (loc_leave_scope loc') (ModeAbort abort)
              | StmtEvalResult glob' loc' ModeLeave =>
                  StmtEvalResult glob' (loc_leave_scope loc') ModeLeave
              | StmtEvalResult glob' loc' ModeBreak =>
                  StmtEvalResult glob' (loc_leave_scope loc') ModeRegular
              | StmtEvalResult glob' loc' _ (* regular or continue *) =>
                  (* run the rest of the loop inside the init block *)
                  match eval_loop glob' loc' new_level cond after body remaining_fuel with
                  | StmtEvalResult glob'' loc'' mode =>
                      StmtEvalResult glob'' (loc_leave_scope loc'') mode
                  end
              end
          end
      end
   end
with eval_block {C: yul_config} {D: dynamic_eval_config}
                (glob: yc_global_ctx)
                (loc: local_ctx)
                (nesting_level: N)
                (block: block)
                (fuel: nat)
{struct fuel}
: stmt_eval_result
:= match fuel with
   | O => StmtEvalResult glob loc (ModeAbort yc_out_of_gas)
   | S remaining_fuel =>
      match block with
      | Block statements =>
          let new_level := N.succ nesting_level in
          let new_scope := loc_enter_scope loc in
          match bind_funs (loc_funs new_scope) statements new_level with
          | inl err => StmtEvalResult glob loc (ModeAbort (wrap_dynamic_error err))
          | inr funs => match eval_stmt_list glob
                               {|
                                   loc_funs := funs;
                                   loc_vars := loc_vars new_scope;
                               |}
                               new_level statements remaining_fuel
                        with
                        | StmtEvalResult glob' loc' mode =>
                            StmtEvalResult glob' (loc_leave_scope loc') mode
                        end
          end
      end
   end
with eval_stmt_list {C: yul_config} {D: dynamic_eval_config}
                    (glob: yc_global_ctx)
                    (loc: local_ctx)
                    (nesting_level: N)
                    (stmts: list stmt)
                    (fuel: nat)
{struct fuel}
: stmt_eval_result
:= match fuel with
   | O => StmtEvalResult glob loc (ModeAbort yc_out_of_gas)
   | S remaining_fuel =>
     match stmts with
     | nil => StmtEvalResult glob loc ModeRegular
     | cons first rest =>
         let after_first := eval_stmt glob loc nesting_level first remaining_fuel in
         match after_first with
         | StmtEvalResult glob' loc' ModeRegular =>
            eval_stmt_list glob' loc' nesting_level rest remaining_fuel
         | _ => after_first
         end
     end
   end
with eval_expr {C: yul_config} {D: dynamic_eval_config}
               (glob: yc_global_ctx)
               (loc: local_ctx)
               (e: expr)
               (fuel: nat)
{struct fuel}
: expr_eval_result
:= match fuel with
   | O => ExprEvalAbort glob loc yc_out_of_gas
   | S remaining_fuel =>
      match e with
      | Const type val => ExprEvalSuccess glob loc (existT _ type val :: nil)%list
      | Ident id =>
          match Tower.has (layered_dict_domain (loc_vars loc)) id as z return (_ = z -> _) with
          | false => fun _ => ExprEvalAbort glob loc
                                            (wrap_dynamic_error DE_CannotResolveVariable)
          | true => fun found =>
             ExprEvalSuccess glob loc
                             (Dict.lookup (layered_dict_map (loc_vars loc)) id found :: nil)%list
          end eq_refl
      | FunCall name args =>
          match eval_args glob loc args remaining_fuel with
          | ExprEvalAbort glob' loc' err' => ExprEvalAbort glob' loc' err'
          | ExprEvalSuccess glob' loc' values =>
            match yc_get_builtin_fun name with
            | Some builtin => (* invoke a built-in function *)
                match builtin glob values with
                | (glob'', _, Some err) => ExprEvalAbort glob'' loc' err
                | (glob'', outputs, None) => ExprEvalSuccess glob'' loc' outputs
                end
            | None =>
                match Tower.has (layered_dict_domain (loc_funs loc)) name as z return (_ = z -> _) with
                | false => fun _ => ExprEvalAbort glob' loc' 
                                                  (wrap_dynamic_error DE_CannotResolveFunction)
                | true => fun found =>
                    let f := Dict.lookup (layered_dict_map (loc_funs loc)) name found in
                    match enter_fun loc' f values with
                    | inl err => ExprEvalAbort glob' loc' (wrap_dynamic_error err)
                    | inr f_loc =>
                          match eval_block glob' f_loc 
                                            (fun_nesting_level f)
                                            (fun_body f)
                                            remaining_fuel
                          with
                          | StmtEvalResult glob'' _ (ModeAbort abort) =>
                              ExprEvalAbort glob'' loc' abort
                          | StmtEvalResult glob'' _ ModeBreak =>
                              ExprEvalAbort glob'' loc' (wrap_dynamic_error DE_UnexpectedBreak)
                          | StmtEvalResult glob'' _ ModeContinue =>
                              ExprEvalAbort glob'' loc' (wrap_dynamic_error DE_UnexpectedContinue)
                          | StmtEvalResult glob'' f_loc' _ =>
                              match leave_fun f_loc' f with
                              | inl err => ExprEvalAbort glob'' loc' (wrap_dynamic_error err)
                              | inr outputs => ExprEvalSuccess glob'' loc' outputs
                              end
                          end
                    end
                end eq_refl
            end
         end
      end
  end
with eval_args {C: yul_config} {D: dynamic_eval_config}
       (glob: yc_global_ctx)
       (loc: local_ctx)
       (args: list expr)
       (fuel: nat)
{struct fuel}
: expr_eval_result
:= match fuel with
   | O => ExprEvalAbort glob loc yc_out_of_gas
   | S remaining_fuel =>
      match args with
      | nil => ExprEvalSuccess glob loc nil
      | cons head tail =>
          (* Arguments are evaluated right-to-left. *)
          let tail_result := eval_args glob loc tail remaining_fuel in
          match tail_result with
          | ExprEvalAbort _ _ _ => tail_result
          | ExprEvalSuccess glob' loc' tail =>
              cons_eval_results (eval_expr glob' loc' head remaining_fuel)
                                tail
          end
      end
  end
with eval_switch {C: yul_config} {D: dynamic_eval_config}
                 (glob: yc_global_ctx)
                 (loc: local_ctx)
                 (nesting_level: N)
                 (value: dynamic_value)
                 (cases: list case)
                 (default: option block)
                 (fuel: nat)
{struct fuel}
: stmt_eval_result
:= match fuel with
   | O => StmtEvalResult glob loc (ModeAbort yc_out_of_gas)
   | S remaining_fuel =>
      match cases with
      | nil =>
          match default with
          | None => StmtEvalResult glob loc ModeRegular (* do nothing *)
          | Some block => eval_block glob loc nesting_level block remaining_fuel
          end
      | cons (Case ctype cvalue body) tail =>
          if dynamic_value_eq_dec value (existT yc_value ctype cvalue)
              then eval_block glob loc nesting_level body remaining_fuel
              else eval_switch glob loc nesting_level value tail default remaining_fuel
      end
  end
(* eval_loop runs a for loop without its init block. *)
with eval_loop {C: yul_config} {D: dynamic_eval_config}
               (glob: yc_global_ctx)
               (loc: local_ctx)
               (nesting_level: N)
               (cond: expr)
               (after: block)
               (body: block)
               (fuel: nat)
{struct fuel}
: stmt_eval_result
:= match fuel with
   | O => StmtEvalResult glob loc (ModeAbort yc_out_of_gas)
   | S remaining_fuel =>
          match eval_expr glob loc cond remaining_fuel with
          | ExprEvalAbort    new_glob new_loc abort =>
              StmtEvalResult new_glob new_loc (ModeAbort abort)
          | ExprEvalSuccess  new_glob new_loc (value :: nil) =>
              if yc_cast_to_bool (projT1 value) (projT2 value) then
                (* run the `body' block *) 
                match eval_block new_glob new_loc nesting_level body remaining_fuel with
                | StmtEvalResult glob' loc' (ModeAbort abort) =>
                    StmtEvalResult glob' loc' (ModeAbort abort)
                | StmtEvalResult glob' loc' ModeLeave =>
                    StmtEvalResult glob' loc' ModeLeave
                | StmtEvalResult glob' loc' ModeBreak =>
                    StmtEvalResult glob' loc' ModeRegular
                | StmtEvalResult glob' loc' _ (* continue or regular *) =>
                    (* run the `after' block *)
                    match eval_block glob' loc' nesting_level after remaining_fuel with
                    | StmtEvalResult glob'' loc'' (ModeAbort abort) =>
                        StmtEvalResult glob'' loc'' (ModeAbort abort)
                    | StmtEvalResult glob'' loc'' ModeLeave =>
                        StmtEvalResult glob'' loc'' ModeLeave
                    | StmtEvalResult glob'' loc'' ModeBreak =>
                        StmtEvalResult glob'' loc'' ModeRegular
                    | StmtEvalResult glob'' loc'' _ (* continue or regular *) =>
                        (* loop *)
                        eval_loop glob'' loc'' nesting_level cond after body remaining_fuel
                    end
                end
              else StmtEvalResult new_glob new_loc ModeRegular
          | ExprEvalSuccess  new_glob new_loc _ =>
              StmtEvalResult new_glob new_loc 
                             (ModeAbort (wrap_dynamic_error DE_ExactlyOneValueExpected))
          end
   end.

(** Evaluate a global-level block. *)
Definition eval {C: yul_config} {D: dynamic_eval_config}
                 (glob: yc_global_ctx)
                 (block: block)
                 (fuel: nat)
: yc_global_ctx * option yc_abort_data
:= match eval_block glob 
                    {| (* empty local context: *)
                        loc_funs := {| layered_dict_map := Dict.empty |};
                        loc_vars := {| layered_dict_map := Dict.empty |};
                    |}
                    (* nesting level: *) 0%N
                    block
                    fuel
   with
   | StmtEvalResult new_glob _ ModeRegular   => (new_glob, None)
   | StmtEvalResult new_glob _ ModeLeave     => (new_glob, None)
   | StmtEvalResult new_glob _ ModeBreak     => (new_glob, Some (wrap_dynamic_error DE_UnexpectedBreak))
   | StmtEvalResult new_glob _ ModeContinue  => (new_glob, Some (wrap_dynamic_error DE_UnexpectedContinue))
   | StmtEvalResult new_glob _ (ModeAbort a) => (new_glob, Some a)
   end.