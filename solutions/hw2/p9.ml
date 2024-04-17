(** Arithmetic operators *)
type 'a array = Arr of (int * 'a) list
type aop = Add | Sub | Mul

(** Arithmetic expressions *)
type aexp =
  | Int of int  (** integer constant *)
  | Aop of aop * aexp * aexp  (** arithmetic op *)
  | Var of string  (** variable *)
  | Select of aexp * aexp (** array read *)
  | Store of aexp * aexp * aexp (** array write *)

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

(* 
x = a[i] * a[j]

Reads:
Path ("a", [Var "i"])
Path ("a", [Var "j"])

AST:
Assign (
  "x",
  Aop (
    Mul,
    Select (Var "a", Var "i"),
    Select (Var "a", Var "j")
  )
)
*)

(* 
y = a[a[i]] 

Reads:
Path ("a", [Select (Var "a", Var "i")])

AST:
Assign (
  "y", 
  Select (
    Var "a",
    Select (
      Var "a",
      Var "i"
    )
  )
)
*)

(* 
a[x - y] = z

Writes:
Path ("a", [Aop (Sub, Var "x", Var "y"])

AST:
Assign (
  "a",
  Store (
    Var "a",
    Aop (Sub, Var "x", Var "y"),
    Var "z"
  )
)
*)

(*  
a[i + j] = a[i] + a[j];

Write:
Path ("a", [Aop (Add, Var "i", Var "j"])

AST:
Assign (
  "a",
  Store (
    Var "a",
    Aop (Add, Var "i", Var "j"),
    Aop (Add, (Select (Var "a", Var "i")), (Select (Var "a", Var "j")))
  )
)
*)

(*  
a[a[i]] = y

Writes:
Path ("a", [Select (Var "a", Var "i")])

AST:
Assign (
  "a",
  Store (
    Var "a",
    (Select (Var "a", Var "i")),
    Var "y"
  )
)
*)

(* 
a[a[i] + a[j]] = a[a[i] * a[j]]

Reads:
Path ("a", [Aop (Mul, (Select (Var "a", Var "i")), (Select (Var "a", Var "i")))])

Writes:
Path ("a", [Aop (Add, (Select (Var "a", Var "i")), (Select (Var "a", Var "j")))])


AST:
Assign (
  "a",
  Store (
    Var "a",
    Aop (Add, (Select (Var "a", Var "i")), (Select (Var "a", Var "j"))),
    Select (
      Var "a",
      Aop (Mul, (Select (Var "a", Var "i")), (Select (Var "a", Var "j")))
    )
  )
)
*)

(*
a[i][j]
AST:
Select ((Select (Var "a", Var "i")), Var "j")
*)

(* 
a[i][j] = 1
Store (
  Var "a", 
  Var "i", 
  Store (
    (Select (Var "a", Var "i")),
    Var "j",
    Int 1
  )
)
*)

(* 
a[i][j] = a[j][i]

Reads:
Path ("a", [Var "j"; Var "i"])

Writes:
Path ("a", [Var "i"; Var "j"])

AST:
Assign (
  "a",
  Store (
    Var "a", 
    Var "i", 
    Store (
      (Select (Var "a", Var "i")),
      Var "j",
      (Select (Select (Var "a", Var "j"), Var "i"))
    )
  )
)
*)

(* 
a[i][j][k] = a[k][j][i]

Reads:
Path ("a", [Var "k"; Var "j"; Var "i"])

Writes:
Path ("a", [Var "i"; Var "j"; Var "k"])

AST:
Assign (
  "a",
  Store (
    Var "a", 
    Var "i", 
    Store (
      (Select (Var "a", Var "i")),
      Var "j",
      Store(
        (Select (Select (Var "a", Var "i"), Var "j")),
        Var "k",
        (Select (Select (Select (Var "a", Var "k"), Var "j"), Var "i"))
      )
    )
  )
)
*)