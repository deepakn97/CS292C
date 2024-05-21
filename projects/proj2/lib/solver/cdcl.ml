(** Conflict-driven clause learning (CDCL) solver *)

open Base

exception Solver_error

(* Make a solver given a CNF problem description *)
module Make (Problem : sig
  val desc : Description.t
end) =
struct
  (* The set of all variables *)
  let vars = Formula.vars Problem.desc.f

  (** The number of variables *)
  let num_vars = Set.length vars

  (** Restart threshold *)
  let restart_threshold = ref 1

  (** Restart increment strategy: multiply the threshold by 2 each time *)
  let restart_inc n = n * 2

  (** Restart count *)
  let restart_count = ref 0

  (** All original clauses in the CNF problem *)
  let cs : Formula.t = Problem.desc.f

  (** Set of all original clauses *)
  let cset = Set.of_list (module Clause) cs

  (** Allow the same number of conflicts as the number of original clauses. Feel
      free to change this parameter. *)
  let _CAPACITY = (List.length cs) * 10

  (** A FIFO queue of capacity [_CAPACITY] to hold conflicts. When a new
      conflict is learned but the queue is at its capacity, the oldest conflict
      will be evicted. *)
  let conflicts = Queue.create ~capacity:_CAPACITY ()

  (** List of learned lemmas, each of which is a (conflict clause, proof) pair *)
  let lemmas : Script.Lemma.t list ref = ref []

  (** Learn the given conflict *)
  let learn_conflict (s : State.t) (c : Clause.t) (proof : Proof.t) : unit =
    if not (Queue.mem conflicts c ~equal:Clause.equal || Set.mem cset c) then (
      (* Logs.debug (fun m -> m "Learning conflict: %a" Clause.pp c); *)
      Heuristics.record_conflict s.h c;
      Int.incr restart_count;
      lemmas := Script.Lemma.make c proof :: !lemmas;
      while Queue.length conflicts >= _CAPACITY do
        ignore @@ Queue.dequeue_exn conflicts
      done;
      Queue.enqueue conflicts c)
    else Logs.debug (fun m -> m "Discarding conflict: %a" Clause.pp c)

  (** Return the current list of conflicts *)
  let curr_conflicts () = Queue.to_list conflicts

  let rec run_bcp_different (level: int) (a: Assign.t) (cs: Clause.t list) : Bcp.result * Assign.t * (Clause.t list) =
    let rec process_clauses (a: Assign.t) (remaining: Clause.t list) (unresolved: Clause.t list) : Bcp.result * Assign.t * (Clause.t list) =
      match remaining with
      | [] -> 
          if List.is_empty unresolved then (Sat, a, [])
          else (Unknown, a, unresolved)
      | c :: cs_tail ->
          match Bcp.status a.nu c with
          | Sat -> 
              process_clauses a cs_tail unresolved  (* Discard SAT clause and continue *)
          | Unsat -> 
              (Unsat c, a, unresolved @ cs_tail)  (* Return UNSAT clause and all remaining and unresolved clauses *)
          | Unit l -> 
              let new_assign = Assign.assign_implied a level c l in
              run_bcp_different level new_assign (unresolved @ cs_tail)  (* Run BCP again with new assignment and all unresolved clauses *)
          | Unresolved -> 
              process_clauses a cs_tail (c :: unresolved)  (* Add to unresolved and continue *)
    in
    process_clauses a cs []

  let rec run_bcp (level: int) (a: Assign.t) (cs: Clause.t list) : Bcp.result * Assign.t * (Clause.t list) = 
    match Utils.partition4_map cs ~f:(fun c ->
        match Bcp.status a.nu c with
        | Sat -> `P1 c
        | Unsat -> `P2 c
        | Unit l -> `P3 (l,c)
        | Unresolved -> `P4 c)
    with 
    | sat, unsat, unitc, unresolved -> (
      if not (List.is_empty unsat) then
        Unsat (List.hd_exn unsat), a, (unsat @ unresolved @ (List.map ~f:snd unitc))
      else (
        if not (List.is_empty unitc) then (
          let l, c = List.hd_exn unitc in
          let new_assign = Assign.assign_implied a level c l in
          run_bcp level new_assign (unresolved @ (List.map ~f:snd unitc))
        )
        else (
          if not (List.is_empty unresolved) then (Unknown, a, unresolved)
          else (Sat, a, [])
          )
        )
      )

  let contains_var (c: Clause.t) (l: Lit.t) : bool =
    Clause.contains c l || Clause.contains c (Lit.negate l)
  
  let get_clause_lits (c: Clause.t) : Lit.t list =
    let clause_vars = Set.to_list (Clause.vars c) in
    (* Logs.debug (fun m ->
      m "Clause Vars: %a" Fmt.(vbox @@ list Var.pp) clause_vars); *)
    List.map clause_vars ~f:(fun v -> (if Clause.contains c (Lit.make_pos v) then (Lit.make_pos v) else (Lit.make_neg v)))
  
  (* this can be optimized by only checking the variables in the clause and not all implied literals *)
  (*  *)
  let get_antecedent (a: Assign.t) (l: Lit.t) : Clause.t option =
    let ante = Assign.antecedent a l in
    match ante with 
    | None -> Assign.antecedent a (Lit.negate l)
    | Some ant -> Some ant

  let xi_optimized (c: Clause.t) (implied: Lit.t list) (a: Assign.t) (level: int) : (Lit.t * Clause.t) option = 
    let clause_lits = get_clause_lits c in
    (* Logs.debug (fun m ->
      m "Clause lits: %a" Fmt.(vbox @@ list Lit.pp) clause_lits); *)
    (* Logs.debug (fun m ->
      m "Clause literals and their antecedents: %a" Fmt.(vbox @@ list (fun fmt l ->
        let antecedent = get_antecedent a l in
        match antecedent with
        | None -> Fmt.pf fmt "Literal %a has no antecedent." Lit.pp l
        | Some ant -> Fmt.pf fmt "Literal %a has antecedent: %a" Lit.pp l Clause.pp ant
      )) clause_lits
    ); *)
    let lit = List.find clause_lits ~f:(fun l -> 
      (Assign.level_exn a l = level) && Option.is_some (get_antecedent a l)) in
    match lit with
    | None -> None
    (* if l was found than it always has an antecedent *)
    | Some l -> Some (l, Option.value_exn (get_antecedent a l))


  (* return all variables which follow this. Because we are resolving based on only one literal. So we don't need to continue calculating xi always. *)
  let xi (c: Clause.t) (implied: Lit.t list) (a: Assign.t) (level: int) : (Lit.t * Clause.t) option =
    let level_lits = List.filter implied ~f:(fun lit -> Assign.level_exn a lit = level) in
    let lit = List.find level_lits ~f:(fun lit -> contains_var c lit) in
    match lit with
    | None -> None
    | Some l -> (
      let ante = Option.value_exn (get_antecedent a l) in 
      if Clause.contains c l then Some (l, ante)
      else Some ((Lit.negate l), ante)
    )
  
  let sigma (c: Clause.t) (level: int) (literals: Lit.t list) (a: Assign.t): int =
    List.length (List.filter literals ~f:(fun lit -> (contains_var c lit) && (Assign.level_exn a lit) = level))
  

  let rec calc_omega (idx: int) (c: Clause.t) (level: int) (implied: Lit.t list) (decision: Lit.t) (a: Assign.t) : Clause.t =
    (* Logs.debug (fun m -> m ">>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>"); *)
    (* Logs.debug (fun m -> m "Decision literal: %a" Lit.pp decision); *)
    (* Logs.debug (fun m -> m "Implied literals: %a" Fmt.(vbox @@ list Lit.pp) implied); *)
    let sigma_val = sigma c level (decision::implied) a in
    (* Logs.debug (fun m -> m "Decision level: %d; idx: %d -> %a" level idx Clause.pp c); *)
    (* Logs.debug (fun m -> m "Sigma value: %d" sigma_val); *)
    if sigma_val = 1 then c
    else (
      let selected = xi c implied a level in
      (* check if the list is still empty then return the current clause *)
      match selected with 
      | None -> c
      | Some (l, ante) -> (
        let curr_omega = Clause.resolve_exn c l ante in 
        calc_omega (idx+1) curr_omega level implied decision a
      )
    )

  let calc_beta (omega: Clause.t) (a: Assign.t) : int =
    let delta = List.map (Set.to_list (Clause.vars omega)) ~f:(fun v -> Assign.level_exn a (Lit.make_pos v)) in
    (* Logs.debug (fun m -> m "Delta for each variable: %a" Fmt.(vbox @@ list int) delta); *)
    (* if there is only one non-zero delta, then backtrack to that level instead of the second last *)
    match delta with
    | [l] -> 0
    | _ -> let sorted_deltas = List.sort delta ~compare:Int.compare in Option.value_exn (List.nth sorted_deltas (List.length sorted_deltas -2))
    (* let non_zero_deltas = List.filter delta ~f:(fun x -> x <> 0) in
    match non_zero_deltas with
      | [] -> 0
      | [single_level] -> single_level
      | _ -> (
        let sorted_deltas = List.sort delta ~compare:Int.compare in
        Option.value_exn (List.nth sorted_deltas (List.length sorted_deltas - 2))
      ) *)

  (** [analyze level a unsat] analyzes the unsatisfiable clause [unsat],
      returning a conflict to learn, and a resolution proof of the conflict *)
  let analyze (level : int) (a : Assign.t) (unsat : Clause.t) :
      Clause.t * Proof.t * int =
    (* Logs.debug (fun m ->
        m "analyze: level = %d, unsat clause = %a" level Clause.pp unsat); *)
    (* retrieve the decision and the trail of implied literals *)
    let { implied; decision } : Assign.Trail.t = Assign.trail_exn a level in
    let conflict = calc_omega 1 unsat level implied decision a in
    let beta = calc_beta conflict a in
    let proof =
      Todo.part 3 "Cdcl.analyze: proof" ~dummy:(Proof.fact Clause.empty)
    in
    (conflict, proof, beta)

  exception Backtrack of int
  exception Restart

  (** [check_result ()] restarts the solver by raising [Restart] if the number
      of learned conflicts in the current run exceeds the threshold. *)
  let check_restart () : unit =
    if !restart_count >= !restart_threshold then (
      Logs.info (fun m ->
          m "Reached threshold: %d. Restarting..." !restart_threshold);
      restart_threshold := restart_inc !restart_threshold;
      restart_count := 0;
      raise Restart)

  (* let rec solve' (s0: State.t) (unr: Clause.t list) : State.t * (Clause.t list) = *)

  let rec solve_optimized (s0 : State.t) (cs: Clause.t list) : State.t =
    (* Logs.debug (fun m -> m ">>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>"); *)
    (* Logs.debug (fun m -> m "Input state: %a" State.pp s0); *)
    (* Logs.debug (fun m -> m "Learned conflicts:"); *)
    (* Logs.debug (fun m ->
        m "%a" Fmt.(vbox @@ list Clause.pp) (curr_conflicts ())); *)

    check_restart ();

    let r, a, unr = run_bcp s0.level s0.a (cs @ curr_conflicts ()) in
    (* update the assignment in the solver state *)
    let s = { s0 with a } in
    (* Logs.debug (fun m -> m "<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<"); *)
    (* Logs.debug (fun m -> m "State after unit-prop: %a" State.pp s); *)

    match r with
    | Sat ->
        (* Logs.debug (fun m -> m "BCP: SAT"); *)
        s
    | Unsat c ->
        (* Logs.debug (fun m -> m "BCP: Found unsat clause: %a" Clause.pp c); *)
        let c, proof, beta = analyze s.level s.a c in
        (* Logs.debug (fun m -> m "Beta: %d" beta); *)
        learn_conflict s c proof;
        (* Logs.debug (fun m -> m "Unsat Backtrack: Backtracking to level %d from level %d" beta s.level); *)
        raise (Backtrack beta)
    | Unknown ->
        (* Logs.debug (fun m -> m "BCP: Unknown"); *)
        let decision =
          (* pick a literal that hasn't been assigned *)
          (* NOTE: you might want to replace this with [Heuristics.next_unassigned]
             for debugging purposes to eliminate randomness *)
          Heuristics.best_unassigned vars s.a s.h
          |> Option.value_exn ~error:(Error.of_string "No unassigned variable")
        in
        let new_state = State.decide s decision in
        let rec rec_backtrack (state: State.t) (clauses: Clause.t list) (current_level : int) =
          try
            solve_optimized state clauses
          with
          | Backtrack b' when b' = current_level -> 
            (* Logs.debug (fun m -> m "Handling multiple backtracks at level %d" b'); *)
            rec_backtrack state clauses b' (* let it retry multiple times as the same level *)
          | Backtrack b' -> 
            raise (Backtrack b') (* Propogate different level backtrack*)
          | Restart -> raise Restart
        in
        try
          (* Logs.debug (fun m -> m  "Branching of %a" Lit.pp decision); *)
          rec_backtrack new_state unr new_state.level
        with
        | Backtrack b -> 
          if b = 0 && s.level = 0 then
            solve_optimized s0 cs
          else
            raise (Backtrack b)
        | Restart -> raise Restart
  let rec solve (s0 : State.t) : State.t =
    solve_optimized s0 cs
    (* Logs.debug (fun m -> m ">>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>");
    Logs.debug (fun m -> m "Input state: %a" State.pp s0);
    Logs.debug (fun m -> m "Learned conflicts:");
    Logs.debug (fun m ->
        m "%a" Fmt.(vbox @@ list Clause.pp) (curr_conflicts ()));

    check_restart ();

    let r, a, unr = run_bcp s0.level s0.a (unresolved @ curr_conflicts ()) in
    (* update the assignment in the solver state *)
    let s = { s0 with a } in
    (* Logs.debug (fun m -> m "<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<"); *)
    (* Logs.debug (fun m -> m "State after unit-prop: %a" State.pp s); *)

    match r with
    | Sat ->
        Logs.debug (fun m -> m "BCP: SAT");
        s
    | Unsat c ->
        Logs.debug (fun m -> m "BCP: Found unsat clause: %a" Clause.pp c);
        let c, proof, beta = analyze s.level s.a c in
        Logs.debug (fun m -> m "Beta: %d" beta);
        learn_conflict s c proof;
        Logs.debug (fun m -> m "Unsat Backtrack: Backtracking to level %d from level %d" beta s.level);
        raise (Backtrack beta)
    | Unknown ->
        Logs.debug (fun m -> m "BCP: Unknown");
        let decision =
          (* pick a literal that hasn't been assigned *)
          (* NOTE: you might want to replace this with [Heuristics.next_unassigned]
             for debugging purposes to eliminate randomness *)
          Heuristics.best_unassigned vars s.a s.h
          |> Option.value_exn ~error:(Error.of_string "No unassigned variable")
        in
        let new_state = State.decide s decision in
        let rec backtrack_same_level (current_level : int) =
          try
            solve new_state
          with
          | Backtrack b' when b' = current_level -> 
            Logs.debug (fun m -> m "Handling multiple backtracks at level %d" b');
            backtrack_same_level b' (* let it retry multiple times as the same level *)
          | Backtrack b' -> 
            raise (Backtrack b') (* Propogate different level backtrack*)
          | Restart -> raise Restart
        in
        try
          Logs.debug (fun m -> m  "Branching of %a" Lit.pp decision);
          solve new_state
        with
        | Backtrack b -> 
          if b = new_state.level then
            backtrack_same_level b
          else (
            if b = s.level then
              solve s0
            else
              raise (Backtrack b)
          )
        | Restart -> raise Restart *)


  let rec run () : Solution.t =
    let s = State.init in
    try
      let s' = solve s in
      SATISFIABLE s'.a.nu
    with
    | Backtrack _ ->
        (* backtracked to the initial level, so unsat overall *)
        (* Logs.debug (fun m -> m "Backtracked to the initial level"); *)
        (* produce a proof script consisting of all learned lemmas,
           followed by the proof of the empty clause *)
        UNSATISFIABLE (Script.make (List.rev !lemmas) (Proof.fact Clause.empty)
        )
    | Restart ->
        (* restart the solver *)
        run ()

  (** Solving result *)
  let result = run ()
end

(** Run CDCL algorithm *)
let run (desc : Description.t) : Solution.t =
  (* create a solver module and run the solver *)
  let module Solver = Make (struct
    let desc = desc
  end) in
  Solver.result
