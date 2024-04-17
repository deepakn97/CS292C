let insert (k: 'k) (v: 'v) (d: ('k * 'v) list) : ('k * 'v) list = 
  (k, v) :: d
let rec mem (equal: 'k -> 'k -> bool) (k: 'k) (d: ('k * 'v) list) : bool =
  match d with
  | [] -> false
  | (l, j)::t ->
    if equal l k then
      true
    else
      false || (mem equal k t)

let rec lookup (equal: 'k -> 'k -> bool) (k: 'k) (d: ('k * 'v) list) : 'v option =
  match d with
  | [] -> None
  | (l, j)::t ->
    if equal l k then
      Some j
    else
      lookup equal k t

let rec remove_key (equal: 'k -> 'k -> bool) (k: 'k) (d: ('k * 'v) list) : ('k * 'v) list =
  match d with
  | [] -> []
  | (l, j)::t ->
    if equal l k then
      remove_key equal k t
    else
      (l, j) :: (remove_key equal k t)

let rec remove_value (pred: 'v -> bool) (d: ('k * 'v) list) : ('k * 'v) list =
  match d with
  | [] -> []
  | (l, j)::t ->
    if pred j then
      remove_value pred t
    else
      (l, j) :: (remove_value pred t)

let dedup (equal: 'k -> 'k -> bool) (d: ('k * 'v) list) : ('k * 'v) list = 
  let rec dedup_helper (equal: 'k -> 'k -> bool) (d: ('k * 'v) list) (acc: ('k * 'v) list) =
    match d with 
    | [] -> (List.rev acc)
    | (l, j)::t -> 
      if (mem equal l acc) then
        dedup_helper equal t acc
      else
        dedup_helper equal t ((l,j)::acc)
  in
  dedup_helper equal d []
