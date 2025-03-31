(*** * Init code
Initialize the Rocq prover *)

(*** ** Declare and open scopes *)

Declare Scope core_scope.
Delimit Scope core_scope with core.

Declare Scope function_scope.
Delimit Scope function_scope with function.
Bind Scope function_scope with Funclass.

Declare Scope type_scope.
Delimit Scope type_scope with type.
Bind Scope type_scope with Sortclass.

Open Scope core_scope.
Open Scope function_scope.
Open Scope type_scope.

(*** ** Import tactics *)

From Stdlib Require Export Ltac.

(*** ** Set universe polymorphism *)

#[global] Set Universe Polymorphism.
