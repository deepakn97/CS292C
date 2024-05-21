open Base

type status = Sat | Unsat | Unit of Lit.t | Unresolved

let status (nu : Eval.t) (c : Clause.t) : status =
  match
    List.partition3_map (Set.to_list c) ~f:(fun l ->
        match Eval.lit nu l with
        | Some false -> (* false *) `Fst l
        | None -> (* unassigned *) `Snd l
        | Some true -> (* true *) `Trd l)
  with
  | fl, ul, tl -> 
    (
      let total = List.length (Set.to_list c) in
      let false_l, true_l, unassigned_l = List.length fl, List.length tl, List.length ul in
      if true_l > 0 then Sat
      else (
        if false_l = total then Unsat
        else (
          if (unassigned_l = 1) && (false_l = total - 1) then Unit (List.hd_exn ul)
          else Unresolved
        )
      ) 
      (* if not (List.is_empty tl) then Sat
      else (
        if (List.is_empty ul) && (List.is_empty tl) then Unsat
        else (
          if (List.is_empty tl) && (List.length fl = 1) then Unit (List.hd_exn fl)
          else Unresolved
        )
      ) *)
    )

type result = Unsat of Clause.t | Unknown | Sat

let rec run_bcp (level: int) (a: Assign.t) (cs: Clause.t list) : result * Assign.t = 
  match Utils.partition4_map cs ~f:(fun c ->
      match status a.nu c with
      | Sat -> `P1 c
      | Unsat -> `P2 c
      | Unit l -> `P3 (l,c)
      | Unresolved -> `P4 c)
  with 
  | sat, unsat, unitc, unresolved -> (
    (* Logs.debug(fun m -> m "Level: %a\nEntry Clauses:\n" Int.pp level);
    List.iter cs ~f:(fun clause ->
      Logs.debug (fun m -> m "%a" Clause.pp clause)
    );
    Logs.debug(fun m -> m "Satisfied Clauses:\n");
    List.iter sat ~f:(fun clause ->
      Logs.debug (fun m -> m "%a" Clause.pp clause)
    );
    Logs.debug (fun m -> m ">>>>>>>>>>>>>>");
    Logs.debug(fun m -> m "Unsatisfied Clauses:\n");
    List.iter unsat ~f:(fun clause ->
      Logs.debug (fun m -> m "%a" Clause.pp clause)
    );
    Logs.debug (fun m -> m ">>>>>>>>>>>>>>");
    Logs.debug(fun m -> m "Unit Clauses:\n");
    List.iter unitc ~f:(fun clause ->
      Logs.debug (fun m -> m "Literal: %a Clause: %a" Lit.pp (fst clause) Clause.pp (snd clause))
    );
    Logs.debug (fun m -> m ">>>>>>>>>>>>>>");
    Logs.debug(fun m -> m "Unresolved Clauses:\n");
    List.iter unresolved ~f:(fun clause ->
      Logs.debug (fun m -> m "%a" Clause.pp clause)
    );
    Logs.debug (fun m -> m ">>>>>>>>>>>>>>"); *)
    if not (List.is_empty unsat) then
      Unsat (List.hd_exn unsat), a
    else (
      if not (List.is_empty unitc) then (
        let l, c = List.hd_exn unitc in
        let new_assign = Assign.assign_implied a level c l in
        run_bcp level new_assign (unresolved @ (List.map ~f:snd unitc))
      )
      else (
        if not (List.is_empty unresolved) then (Unknown, a)
        else (Sat, a)
        )
      )
    )

let run (level : int) (a : Assign.t) (cs : Clause.t list) : result * Assign.t =
  (* let res, new_assign = run_bcp level a cs in
  match res with
  | Sat -> Sat, new_assign
  | Unsat c -> Unsat c, new_assign
  | Unknown -> Unknown, new_assign *)
  run_bcp level a cs