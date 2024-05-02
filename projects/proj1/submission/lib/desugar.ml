open Base
open Lang

(** Convert a memory read of a [path] to a combination of [Var] and [Select] *)
let rec read_from_path (p : path) : aexp =
  match p with
  | { var; indices = ind_list} -> 
    (match (List.rev ind_list) with
    | [] -> Var var
    | [i] -> (Select {arr = Var var; idx = i})
    | i::t -> Select {arr = (read_from_path {var; indices = (List.rev t)}); idx = i}
    )

(** Convert an assignment to a [path] to a variable assignment
    using [Select] and [Store]. *)
let rec write_aux (var: string) (ind_list: aexp list) (aexp: aexp) (read_path: aexp list) : aexp =
  match ind_list with
  | [] -> aexp
  | [i] -> (Store {arr = read_from_path {var; indices=read_path}; idx = i; value = aexp})
  | i::t -> (Store {
                arr = read_from_path {var; indices = read_path};
                idx = i;
                value = (write_aux var t aexp (read_path @ [i]))
                })

let write_to_path (lhs : path) (rhs : aexp) : stmt =
  match lhs with
  | { var; indices = [] } -> Assign { lhs = var; rhs }
  | {var; indices=ind_list} -> Assign {lhs = var; rhs = (write_aux var ind_list rhs [])}
