open P7
type heap = Heap of (string * int) list

(* let rec lookup (k: 'k) (d: heap) : int option =
  match d with
  | Heap [] -> None
  | Heap ((l, j)::t) ->
    if String.equal l k then
      Some j
    else
      lookup k (Heap t) *)

let lookup (k: string) (d: heap) : int option=
match d with
| Heap t ->
  try
    let (_, value) = List.find (fun (i, _) -> String.equal i k) t in Some value
  with Not_found -> None

let insert (k: string) (v: int) (h: heap) : heap = 
  match h with
  | Heap [] -> Heap [(k, v)]
  | Heap t -> Heap ((k, v) :: t)

let calculate_aop (aop: aop) (i1: int) (i2: int) : int =
  match aop with
  | Add -> i1 + i2
  | Sub -> i1 - i2
  | Mul -> i1 * i2

let rec eval_aexp (h: heap) (exp: aexp) : int = 
  match exp with 
  | Int i -> i
  | Var v -> 
    (match (lookup v h) with
    | None -> failwith (Printf.sprintf "No variable %s found" v)
    | Some i -> i)
  | Aop (aop, exp1, exp2) -> (calculate_aop aop (eval_aexp h exp1) (eval_aexp h exp2))

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
  | Comp (com, exp1, exp2) -> (calculate_comp com (eval_aexp h exp1) (eval_aexp h exp2))
  | Not exp1 ->  (not (eval_bexp h exp1))
  | And (exp1, exp2) -> ((eval_bexp h exp1) && (eval_bexp h exp2))
  | Or (exp1, exp2) -> ((eval_bexp h exp1) || (eval_bexp h exp2))

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
  Assign ("x", Int 0),
  Seq (
    Assign ("y", Int 1), 
    Seq (
      Assign ("n", Int 10),
      While (
        Comp (Gt, Var "n", Int 0),
        Seq (
          Assign ("sum", Aop (Add, Var "x", Var "y")),
          Seq (
            Assign ("x", Var "y"),
            Seq (
              Assign ("y", Var "sum"),
              Assign ("n", Aop (Sub, Var "n", Int 1))
            )
          )
        )
      )
    )
  )
)
*)
