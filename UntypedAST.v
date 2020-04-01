Require Import Config.

Inductive expr {C: yul_config}
:= FunCall (name: yc_ident) (args: list expr) 
 | Ident (name: yc_ident)
 | Const (t: yc_type) (val: yc_value t).

Definition typename {C: yul_config}: Type := yc_type * yc_ident.

Inductive stmt {C: yul_config}
:= BlockStmt (s: block)
 | FunDef (name: yc_ident) (inputs outputs: list typename) (body: block)
 | VarDef (vars: list typename) (init: option expr)
 | Assign (lhs: list yc_ident) (rhs: expr) 
 | If (cond: expr) (body: block)
 | Expr (e: expr)
 | Switch (e: expr) (cases: list case) (default: option block)
 | For (init: block) (cond: expr) (after: block) (body: block)
 | Break
 | Continue
 | Leave
with case {C: yul_config} := Case (t: yc_type) (val: yc_value t) (body: block)
with block {C: yul_config} := Block (body: list stmt).