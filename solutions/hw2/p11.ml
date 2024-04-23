open P9
open P10
type value =
  | VInt of int
  | VArr of value array

type heap = Heap of (string * value) list

(* lookup and insert are heap operations *)
let lookup (k: string) (d: heap) : value option=
  match d with
  | Heap t ->
    try
      let (_, value) = List.find (fun (i, _) -> String.equal i k) t in Some value
    with Not_found -> failwith (Printf.sprintf "No variable %s found" k)
  
let insert (k: string) (v: value) (h: heap) : heap = 
  match h with
  | Heap [] -> Heap [(k, v)]
  | Heap t -> Heap ((k, v) :: t)

(* select and store are array operations similar to insert and lookup *)
let select (a: 'a array) (ind: int) : 'a =
  match a with 
  | Arr t -> 
    try 
      let (_, value) = List.find (fun (i, _) -> i = ind) t in value
    with Not_found -> failwith "Array index out of bounds"

let store (a: 'a array) (ind: int) (value: 'a) : 'a array =
  match a with
  | Arr [] -> Arr [(ind, value)]
  (*  *)
  | Arr (x::_ as t) -> Arr ((ind, value)::t)

let calculate_aop (aop: aop) (i1: int) (i2: int) : int =
  match aop with
  | Add -> i1 + i2
  | Sub -> i1 - i2
  | Mul -> i1 * i2

let rec eval_aexp (h: heap) (exp: aexp) : value = 
  match exp with 
  | Int i -> VInt i
  | Var v -> (match (lookup v h) with
    | None -> failwith (Printf.sprintf "No variable %s found" v)
    | Some i -> i)
  | Aop (aop, exp1, exp2) -> 
    (match (eval_aexp h exp1), (eval_aexp h exp2) with
    | VInt i1, VInt i2 -> VInt (calculate_aop aop i1 i2)
    | _, _ -> failwith "Cannot perform arithmetic operations on array.")
  | Select (ae1, ae2) -> 
    (match eval_aexp h ae1 with
    | VArr a-> 
      (match eval_aexp h ae2 with
      | VInt idx -> select a idx
      | _ -> failwith "Cannot select a non-integer value")
    | _ -> failwith "Cannot select from non-array")
  | Store (ae1, ae2, ae3) -> 
    (match eval_aexp h ae1 with
    | VArr a -> 
      (match (eval_aexp h ae2), (eval_aexp h ae3) with
      | VInt idx, VInt value -> VArr (store a idx (VInt value))
      | _, _ -> failwith "Cannot store a non-integer value")
    | _ -> failwith "Cannot store into non-array")

let calculate_comp (comp: comp) (i1: int) (i2: int) : bool = 
  match comp with 
  | Eq -> (i1 = i2)
  | Geq -> (i1 >= i2)
  | Gt -> (i1 > i2)
  | Lt -> (i1 < i2)
  | Leq -> (i1 <= i2)
  | Neq -> (i1 <> i2)
 
let rec eval_bexp (h: heap) (exp: bexp) : bool = 
  match exp with
  | Bool b -> b
  | Comp (com, exp1, exp2) -> 
    (match (eval_aexp h exp1), (eval_aexp h exp2) with
    | VInt i1, VInt i2 -> calculate_comp com i1 i2
    | _, _ -> failwith "Cannot compare non-integer values"
    )
  | Not exp1 -> not (eval_bexp h exp1)
  | And (exp1, exp2) -> (eval_bexp h exp1) && (eval_bexp h exp2)
  | Or (exp1, exp2) -> (eval_bexp h exp1) || (eval_bexp h exp2)

let rec eval_stmt (h: heap) (stmt: stmt) : heap = 
  match stmt with 
  | Assign (s, aexp) -> (insert s (eval_aexp h aexp) h)
  | If (bexp, stmt1, stmt2) ->
    if (eval_bexp h bexp) then
      (eval_stmt h stmt1)
    else
      (eval_stmt h stmt2)
  | While (bexp, stmt1) -> 
    if (eval_bexp h bexp) then
      (eval_stmt (eval_stmt h stmt1) (While (bexp, stmt1)))
    else
      h
  | Seq (stmt1, stmt2) -> (eval_stmt (eval_stmt h stmt1) stmt2)

(* AST for Computing nth fibonnaci number *)
(*
Seq (
  Assign ("fib", Store(Var "fib", Int 0, Int 1)),
  Seq (
    Assign ("fib", Store(Var "fib", Int 1, Int 1)), 
    Seq (
      Assign ("n", Int 10),
      Seq (
        Assign ("i", Int 2),
        While (
          Comp (Lt, Var "i", Var "n"),
          Seq (
            Assign (
              "fib", 
              Store (
                Var "fib", 
                Var "i", 
                Aop (
                  Add, 
                  (Select (Var "fib", Aop (Sub, Var "i", Int 1))), 
                  (Select (Var "fib", Aop (Sub, Var "i", Int 2)))
                )
              )
            ),
            Assign ("i", Aop (Add, Var "i", Int 1))
          )
        )
      )
    )
  )
)
*)

let h1 = Heap [("fib", VArr (Arr []))]

let a1 = Arr [(0, VInt 3); (1, VInt 2); (2, VInt 5)]
let a2 = Arr []
let a3 = Arr [(0, VInt (-1));]
let a4 = Arr [(0, VInt 7); (1, VInt (-10)); (2, VInt 10)]

let a = Arr [(0, VArr a1); (1, VArr a2); (2, VArr a3); (3, VArr a4)]
let va = VArr a
let h2 = Heap [("a", va)]

