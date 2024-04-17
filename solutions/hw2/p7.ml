(** Arithmetic operators *)
type aop = Add | Sub | Mul

(** Arithmetic expressions *)
type aexp =
  | Int of int  (** integer constant *)
  | Aop of aop * aexp * aexp  (** arithmetic op *)
  | Var of string  (** variable *)

(** Comparison ops  *)
type comp = 
| Eq (** equal *)
| Geq (** greater than or equal to *)
| Gt (* greater than *)
| Lt  (** less than *)
| Leq (** less than or equal to *)
| Neq (** not equal *)

(** Boolean expressions (which can appear in conditions *)
type bexp =
(* boolean constant *)
| Bool of bool
(* integer comparison *)
| Comp of comp * aexp * aexp
| Not of bexp (* negation *)
| And of bexp * bexp (* conjunction *)
| Or of bexp * bexp (* disjunction *)

(** Statements *)
type stmt =
(* assignment, aka memory write *)
| Assign of string * aexp
(* conditional *)
| If of bexp * stmt * stmt
(* while-loop *)
| While of bexp * stmt
(* sequence of statements *)
| Seq of stmt * stmt


let rec subst (o: string) (n: string) (exp: aexp) : aexp =
  match exp with
  | Int i -> Int i
  | Var v -> 
    (if String.equal v o then
      Var n
    else
      Var v)
  | Aop (aop, exp1, exp2) -> Aop (aop, (subst o n exp1), (subst o n exp2))