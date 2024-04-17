let rec compress (equal: 'a -> 'a -> bool) (l: 'a list) : 'a list = 
  match l with
  | [] -> []
  | [x] -> [x]
  | x::(y::_ as t) ->
    if equal x y then
      compress equal t 
    else
      x::(compress equal t)

(* Use the compress function with a list of integers *)
let int_list_1= compress Int.equal [1; 1; 2; 3; 3; 4]
let str_list_1 = compress String.equal ["a"; "a"; "a"; "a"; "b"; "c"; "c"; "a"; "a"; "d"; "e"; "e"; "e"; "e"]

let str_list_2 = compress String.equal ["a"; "b"; "b"; "a"; "c"]

(* Print the result *)
let () =
  List.iter (Printf.printf "%d ") int_list_1

let ()= 
  List.iter (Printf.printf "%s ") str_list_1