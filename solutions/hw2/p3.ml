let merge (l: 'a option list) : 'a list option =
  let rec merge_helper (acc: 'a list) (l: 'a option list) = 
    match l with
    | [] -> Some (List.rev acc)
    | None::_ -> None
    | Some x::t -> merge_helper (x::acc) t
  in
  merge_helper [] l
  
let tc1 = merge [Some 1; Some 1; Some 2; Some 3; Some 3; Some 4]
let tc2 = merge [Some "a"; Some "b"; None; Some "c"]
let tc3 = merge []

let () =
  match tc1 with
  | None -> print_endline "None"
  | Some l -> List.iter (Printf.printf "%d ") l

let () = Printf.printf "\n"

let () =
  match tc2 with
  | None -> print_endline "None"
  | Some l -> List.iter (Printf.printf "%s ") l

let () = Printf.printf "\n"

let () =
  match tc3 with
  | None -> print_endline "None"
  | Some l -> List.iter (Printf.printf "%s ") l