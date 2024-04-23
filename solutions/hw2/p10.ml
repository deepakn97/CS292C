open P9
type path = Path of string * aexp list

let rec read_from_path (p: path) : aexp =
  match p with 
  | Path (v, ind_list) -> 
    (match (List.rev ind_list) with
    | [] -> Var v
    | [i] -> (Select (Var v, i))
    | i::t -> Select ((read_from_path (Path (v, (List.rev t))), i))
    )

let write_to_path (p: path) (aexp: aexp) : stmt =
  let rec aux (v: string) (ind_list: aexp list) (aexp: aexp) (read_path: aexp list) : aexp =
    match ind_list with
    | [] -> aexp
    | [i] -> (Store (read_from_path (Path (v, read_path)), i, aexp))
    | i::t -> (Store (
                (read_from_path (Path (v, read_path))), 
                i,
                (aux v t aexp (read_path @ [i]))
                ))
  in
  match p with
  | Path (v, t) -> Assign (v, aux v t aexp [])

