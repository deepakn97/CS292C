open P9
type path = Path of string * aexp list

let rec read_from_path (p: path) : aexp =
  match p with 
  | Path (v, ind_list) -> 
    (match (List.rev ind_list) with
    | [] -> failwith "Empty path"
    | [i] -> (Select (Var v, i))
    | i::t -> Select ((read_from_path (Path (v, (List.rev t))), i))
    )

let write_to_path (p: path) (aexp: aexp) : stmt =
  let rec aux (v: string) (ind_list: aexp list) (aexp: aexp) (read_path: aexp list) : aexp =
    match ind_list with
    | [] -> failwith "Empty Path"
    | [i] -> (Store (Var v, i, aexp))
    | i::t -> (Store ((read_from_path (Path (v, read_path @ [i]))), (aux v t aexp (read_path @ [i])), aexp))
  in
  match p with
  | Path (v, []) -> Assign (v, aexp)
  | Path (v, [i]) -> Assign (v, Store(Var v, i, aexp))
  | Path (v, i::t) -> Assign (v, Store(Var v, i, aux v (i::t) aexp []))

