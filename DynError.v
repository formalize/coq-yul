(**
  An error that can occur during dynamic evaluation.
  This only includes errors that become impossible with static typing.
 *)
Inductive dynamic_error 
(** A function is called with extra arguments
    or a variable declaration with an initializer has too few variables. *)
:= DE_TooManyValues
(** A function is called with not enough arguments
    or an variable declaration with an initializer has too many variables. *)
 | DE_TooFewValues
(** A function is called with an argument of a unexpected type
    or an initializer of a variable returns a value of a wrong type. *)
 | DE_VarTypeMismatch
(** There are two local variables (that includes inputs or outputs) with the same name. *)
 | DE_LocalNameShadowing
(** An expression has returned multiple values in the context in which only one was expected. *)
 | DE_ExactlyOneValueExpected
(** A function is declared with the same name as one of the built-in functions. *)
 | DE_BuiltinFunctionShadowing
(** A function is declared with the same name as a function visible from its location. *)
 | DE_LocalFunctionShadowing
 | DE_CannotResolveFunction
 | DE_CannotResolveVariable
 | DE_InternalErrorOutputNotFound
 | DE_UnexpectedBreak
 | DE_UnexpectedContinue.
