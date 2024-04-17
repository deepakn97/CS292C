open P4
type 'a array = Arr of (int * 'a) list

let empty : 'a array = 
  Arr []
let insert (k: 'k) (v: 'v) (d: ('k * 'v) list) : ('k * 'v) list = 
  (k, v) :: d

let rec lookup (equal: 'k -> 'k -> bool) (k: 'k) (d: ('k * 'v) list) : 'v option =
  match d with
  | [] -> None
  | (l, j)::t ->
    if equal l k then
      Some j
    else
      lookup equal k t

let select (a: 'a array) (ind: int) : 'a option =
  match a with 
  | Arr [] -> None
  | Arr (x::_ as t) -> lookup Int.equal ind t

let store (a: 'a array) (ind: int) (value: 'a) : 'a array =
  match a with
  | Arr [] -> Arr [(ind, value)]
  (*  *)
  | Arr (x::_ as t) -> Arr (insert ind value t)

let of_list (l: 'a list) : 'a array =
  let d = List.mapi (fun i x -> (i, x)) l in
  Arr d

let unique (a: (int * 'a) list) : (int * 'a) list =
  List.sort_uniq (fun (i, _) (j, _) -> compare i j) a

let to_list (a: 'a array) : 'a list =
  match a with
  | Arr [] -> []
  | Arr l -> List.map snd (unique l)
