open Base

(** Substitutions *)
module Subst = struct
  open Lang

  (** [aexp x e c] substitutes all occurrences of [x] in [c] with [e] *)
  let rec aexp (x : string) (e : aexp) (c : aexp) : aexp =
    match c with 
    | Int n -> Int n
    | Aop (op, a, b) -> Aop (op, aexp x e a, aexp x e b)
    | Var v -> if String.equal x v then e else Var v
    | Select r -> Select {arr = (aexp x e r.arr); idx = (aexp x e r.idx)}
    | Store r -> Store {arr = (aexp x e r.arr); idx = (aexp x e r.idx); value = (aexp x e r.value)}

  (** [bexp x e c] substitutes all occurrences of [x] in [c] with [e] *)
  let rec bexp (x : string) (e : aexp) (c : bexp) : bexp =
    match c with
    | Bool b -> Bool b
    | Comp (op, a, b) -> Comp (op, aexp x e a, aexp x e b)
    | Not b -> Not (bexp x e b)
    | And (b1, b2) -> And (bexp x e b1, bexp x e b2)
    | Or (b1, b2) -> Or (bexp x e b1, bexp x e b2)

  (** [formula x e f] substitutes all occurrences of [x] in [f] with [e] *)
  let rec formula (x : string) (e : aexp) (f : formula) : formula =
    match f with
    | FBool b -> FBool b
    | FComp (op, a, b) -> FComp (op, aexp x e a, aexp x e b)
    | FNot b -> FNot (formula x e b)
    | FConn (op, a, b) -> FConn (op, formula x e a, formula x e b)
    | FQ (q, a, b) -> 
      (* only substitute if x is equal to a *)
      if String.equal x a then FQ(q, a, b) else FQ(q, a, (formula x e b))
end

module Subst_multiple = struct
  open Lang
  (** [aexp (x, e) c] substitutes all occurrences of [x] in [c] with [e] *)
  let rec aexp (mapping: (string * aexp) list) (c : aexp) : aexp =
    match c with 
    | Int n -> Int n
    | Aop (op, a, b) -> Aop (op, aexp mapping a, aexp mapping b)
    | Var v -> (match List.find_map mapping ~f:(fun (x, e) -> if String.equal x v then Some e else None) with
                | Some e -> e
                | None -> Var v)
    | Select r -> Select {arr = (aexp mapping r.arr); idx = (aexp mapping r.idx)}
    | Store r -> Store {arr = (aexp mapping r.arr); idx = (aexp mapping r.idx); value = (aexp mapping r.value)}

  (** [bexp (x, e) c] substitutes all occurrences of [x] in [c] with [e] *)
  let rec bexp (mapping: (string * aexp) list) (c : bexp) : bexp =
    match c with
    | Bool b -> Bool b
    | Comp (op, a, b) -> Comp (op, aexp mapping a, aexp mapping b)
    | Not b -> Not (bexp mapping b)
    | And (b1, b2) -> And (bexp mapping b1, bexp mapping b2)
    | Or (b1, b2) -> Or (bexp mapping b1, bexp mapping b2)

  (** [formula (x, e) f] substitutes all occurrences of [x] in [f] with [e] *)
  let rec formula (mapping: (string * aexp) list) (f : formula) : formula =
    match f with
    | FBool b -> FBool b
    | FComp (op, a, b) -> FComp (op, aexp mapping a, aexp mapping b)
    | FNot b -> FNot (formula mapping b)
    | FConn (op, a, b) -> FConn (op, formula mapping a, formula mapping b)
    | FQ (q, a, b) ->
      (
        (* remove all the values which are equal to the variables present in quantifier *)
        let updated_mapping = List.filter mapping ~f:(fun (x, _) -> not (String.equal x a)) in
        FQ(q, a, formula updated_mapping b)
      )
end

(** Lift a [bexp] into a [formula] *)
let rec bexp_to_formula (b : Lang.bexp) : Lang.formula =
  match b with 
  | Bool b -> FBool b
  | Comp (op, a, b) -> FComp (op, a, b)
  | Not b -> FNot (bexp_to_formula b)
  | And (b1, b2) -> FConn (And, (bexp_to_formula b1), (bexp_to_formula b2))
  | Or (b1, b2) -> FConn (Or, (bexp_to_formula b1), (bexp_to_formula b2))

let rec find_vars_aexp (a: Lang.aexp) : string list =
  match a with
  | Int _ -> []
  | Var x -> [x]
  | Aop (_, a, b) -> find_vars_aexp a @ find_vars_aexp b
  | Select r -> find_vars_aexp r.arr @ find_vars_aexp r.idx
  | Store r -> find_vars_aexp r.arr @ find_vars_aexp r.idx @ find_vars_aexp r.value

let rec find_vars_formula (f: Lang.formula) : string list =
  match f with
  | FBool _ -> []
  | FComp (_, a, b) -> find_vars_aexp a @ find_vars_aexp b
  | FNot f -> find_vars_formula f
  | FConn (_, a, b) -> find_vars_formula a @ find_vars_formula b
  | FQ (_, a, b) -> [a] @ (find_vars_formula b)

(** Make a verifier for a method in a difny program *)
module Make (S : sig
  val prog : Lang.prog
  (** ambient program *)

  val meth : Lang.meth
  (** method to verify *)
end) =
struct
  open Lang

  (** [INTERNAL] Mutable reference (i.e. pointer) to the current gamma *)
  let gamma_ref = ref (S.meth.locals @ S.meth.params)

  (** [INTERNAL] Retrieve the current gamma *)
  let gamma () = !gamma_ref

  (** Update gamma to map a new variable with its type *)
  let add_gamma (x : string) (t : ty) : unit = gamma_ref := (x, t) :: !gamma_ref

  let find_meth (callee_name: string) : meth =
    List.find S.prog ~f:(fun m -> String.equal m.id callee_name)
    |> Option.value_exn ~message:(Fmt.str "Method %s not found in program." callee_name)

  (** [INTERNAL] Counter to generate fresh variables *)
  let counter = ref 0

  (** Generate a fresh variable using the hint, and record its type in gamma *)
  let fresh_var (t : ty) ~(hint : string) =
    let i = !counter in
    counter := !counter + 1;
    let x = Fmt.str "$%s_%d" hint i in
    add_gamma x t;
    x

  (** Compute the list of modified variables in a statement *)
  let rec modified (s : stmt) : string list =
    match s with
    | Assign { lhs; rhs } -> [lhs]
    | If { cond; thn; els } -> (modified_block thn) @ (modified_block els)
    | While { cond; inv; body } -> (modified_block body)
    (* Todo: revisit this *)
    | Call { lhs; callee; args } -> [lhs]
    | Havoc x -> [x]
    | Assume _ -> []
    | Assert _ -> []
    | Print _ -> []

  (** Compute the list of unique modified variables in a sequence of statements *)
  and modified_block (stmts : block) : string list =
    (* for each stmt, compute the list of modified variabls ("map"),
       and then concatenate all lists together ("concat") *)
    let xs = List.concat_map ~f:modified stmts in
    (* deduplicate and sort the list *)
    List.dedup_and_sort ~compare:String.compare xs

  (** Compile a statement into a sequence of guarded commands *)
  let rec compile (c : stmt) : gcom list =
    match c with
    | Assign { lhs; rhs } -> 
      (
        let lhs_type = Utils.ty_exn (gamma ()) ~of_:lhs in
        let tmp = fresh_var lhs_type ~hint:lhs in
        [Assume (FComp (Eq, Var tmp, Var lhs)); 
        Havoc lhs; 
        Assume (FComp (Eq, Var lhs, (Subst.aexp lhs (Var tmp) rhs)))]
      )
    (* (assume b; compile(c1)) [] (assume -b; compile(c2)) *)
    | If { cond; thn; els} -> 
      (
        let thn_stmt_list = List.fold_left ~f:(fun acc s -> acc @ (compile s)) ~init:[] thn in
        let els_stmt_list = List.fold_left ~f:(fun acc s -> acc @ (compile s)) ~init:[] els in
        [Choose (
          Seq ((Assume (bexp_to_formula cond))::thn_stmt_list), 
          Seq ((Assume (FNot (bexp_to_formula cond)))::els_stmt_list)
        )]
      )
    | While { cond; inv; body } -> 
      (
        let wp_body_list = List.fold_left ~f:(fun acc s -> acc @ (compile s)) ~init:[] body in
        let inv_assert_list = List.fold_left ~f:(fun acc s -> (Assert s)::acc) ~init:[] inv in
        let inv_assume_list = List.fold_left ~f:(fun acc s -> (Assume s)::acc) ~init:[] inv in
        let modified_variables = modified_block body in
        let havoc_variables = List.fold_left ~f:(fun acc s -> (Havoc s)::acc) ~init:[] modified_variables in
        let choose1 = Seq ((Assume (bexp_to_formula cond)::wp_body_list) @ inv_assert_list @ [Assume (FBool false)]) in
        let choose2 = Seq [Assume (FNot (bexp_to_formula cond))] in
        inv_assert_list @ havoc_variables @ inv_assume_list @ [Choose (choose1, choose2)]
      )
      (* Doesn't support recursion yet *)
      (* here args are the actual values of the parameters *)
      (* so if we have a requires statement, we need to assert that the current args are supporting the requires statement *)
      (* Here we can treat args as assignment operation and then assert all these variables *)
      (* and then we can assume the postconditions for lhs *)
    | Call { lhs; callee; args } -> 
      (
        let callee_meth = find_meth callee in
        (* Implementation 3 *)
        (* havoc all params *)
        (* get all used variables in the preconditions *)
        (* let used_vars_precondition = List.dedup_and_sort ~compare:String.compare (List.concat_map ~f:find_vars_formula callee_meth.requires) in
        let used_vars_postcondition = List.dedup_and_sort ~compare:String.compare (List.concat_map ~f:find_vars_formula callee_meth.ensures) in
        let fresh_used_vars_mapping_precondition = List.map ~f:(fun x -> (x, Var (fresh_var (Utils.ty_exn (gamma ()) ~of_:x) ~hint:x))) used_vars_precondition in
        let fresh_used_vars_mapping_postcondition = List.map ~f:(fun x -> (x, Var (fresh_var (Utils.ty_exn (gamma ()) ~of_:x) ~hint:x))) used_vars_postcondition in
        let fresh_used_vars_mapping_total = fresh_used_vars_mapping_precondition @ fresh_used_vars_mapping_postcondition in
        (* assume y0 = y *)
        let assume_used_vars_precondition = List.map ~f:(fun (x, fresh_arg) -> Assume (FComp (Eq, fresh_arg, Var x))) fresh_used_vars_mapping_precondition in
        let assume_used_vars_postcondition = List.map ~f:(fun (x, fresh_arg) -> Assume (FComp (Eq, fresh_arg, Var x))) fresh_used_vars_mapping_postcondition in
        (* now substite the tmp values of these vars in all the preconditions and postconditions *)

        let subst_fresh_vars_precondition = List.map ~f:(fun f -> Subst_multiple.formula fresh_used_vars_mapping f) callee_meth.requires in
        let subst_fresh_vars_postcondition = List.map ~f:(fun f -> Subst_multiple.formula fresh_used_vars_mapping f) callee_meth.ensures in
        (* now the precondition is r == y0 + 1 *)
        (* now substitute the return value in postconditions with lhs *)
        let subst_return_postcondition = List.map ~f:(fun f -> Subst.formula (fst callee_meth.returns) (Var lhs) f) subst_fresh_vars_postcondition in
        (* now the postcondition is y == y0 + 1. remember to call havoc before this, so that it can be converted to y1 = y0 + 1 *)
        let assert_preconditions = List.map ~f:(fun f -> Assert f) subst_fresh_vars_precondition in
        let assume_postconditions = List.map ~f:(fun f -> Assume f) subst_return_postcondition in
        assume_used_vars @ assert_preconditions @ [Havoc lhs] @ assume_postconditions *)

        (* Old Implementation starts *)
        
        let params_args_mapping = List.map2_exn ~f:(fun (x, _) arg -> (x, arg)) callee_meth.params args in
        (* subst pre-conditions with args *)
        let subst_args_preconditions = List.map ~f:(fun f -> Subst_multiple.formula params_args_mapping f) callee_meth.requires in
        (* now the precondition is r == y + 1 *)
        (* assert pre-conditions *)
        let assert_preconditions = List.map ~f:(fun f -> Assert f) subst_args_preconditions in
        (* add the callee_meth.returns param to gamma so that we can havoc that variable *)
        let return_param = fresh_var (snd callee_meth.returns) ~hint:(fst callee_meth.returns) in
        (* subst post-conditions with appropriate args and new return variable *)
        let subst_args_postconditions = List.map ~f:(fun f -> Subst_multiple.formula (params_args_mapping @ [((fst callee_meth.returns), Var return_param)]) f) callee_meth.ensures in
        (* let assume_return_param =  *)
        (* assert post-conditions *)
        (* let used_vars = List.dedup_and_sort ~compare:String.compare (List.concat_map ~f:find_vars_formula subst_args_postconditions) in
        let havoc_params = List.map ~f:(fun x -> Havoc x) used_vars in *)
        let assume_postconditions = List.map ~f:(fun f -> Assume f) subst_args_postconditions in
        (* final sequence of commands *)
        (* assert_preconditions @ (compile (Assign { lhs = lhs; rhs = Var return_param })) @ assume_postconditions *)

        assert_preconditions @ assume_postconditions @  (compile (Assign { lhs = lhs; rhs = Var return_param }))
        (* return_param = r0 *)
        (* Assume min0 = min
        havoc min
        Assume min = r0
        assume r0 >= (0-y) && r0 <= (0-x)
        assume r0 >= (0-y) || r0 <= (0-x)
        assert 0-min <= x && 0-min <= y
        as *)
        (* Old Implementation ends *)
      )
    | Havoc x -> [ Havoc x ]
    | Assume f -> [ Assume f ]
    | Assert f -> [ Assert f ]
    | Print _ -> []

  (** For each statement in a block, compile it into a list of guarded 
      commands ("map"), and then concatenate the result ("concat") *)
  and compile_block : block -> gcom list = List.concat_map ~f:compile

  (** Compute weakest-pre given a guarded command and a post formula *)
  let rec wp (g : gcom) (f : formula) : formula =
    match g with
    | Assume f' -> FConn (Imply, f', f)
    | Assert f' -> FConn (And, f', f)
    | Havoc x -> Subst.formula x (Var (fresh_var (Utils.ty_exn (gamma ()) ~of_:x) ~hint:x)) f
    | Seq cs -> 
      (
        match cs with
        | [] -> f
        | x::xs -> wp x (wp_seq xs f)
      )
    | Choose (c1, c2) -> (FConn (And, wp c1 f, wp c2 f))

  (** Propagate the post-condition backwards through a sequence of guarded
      commands using [wp] *)
  and wp_seq (gs : gcom list) (phi : formula) : formula =
    List.fold_right ~init:phi ~f:wp gs

  (** Verify the method passed in to this module *)
  let result : unit =
    (* print method id and content *)
    Logs.debug (fun m -> m "Verifying method %s:" S.meth.id);
    Logs.debug (fun m -> m "%a" Pretty.meth S.meth);
    (* logic for loops is that we first assert the pre-conditions to prove that the conditions hold on entry, then havoc the variables that are modified, assume the preconditions and then compile the body, then we assert the postconditions*)

    (* let havoc_params = List.map ~f:(fun (x, _) -> Havoc x) S.meth.params in *)
    (* let modified_variables = modified_block S.meth.body in
    let havoc_params = List.map ~f:(fun x -> Havoc x) modified_variables in *)
    (* let assert_preconditions = List.map ~f:(fun s -> Assert s) S.meth.requires in *)
    let assume_preconditions = List.map ~f:(fun s -> Assume s) S.meth.requires in

    (* Logs.debug (fun m -> m "Assert Pre-conditions Callee:");
    Logs.debug (fun m -> m "%a" Fmt.(vbox (list Pretty.gcom)) assert_preconditions); *)
    Logs.debug (fun m -> m "Assume Pre-conditions Callee:");
    Logs.debug (fun m -> m "%a" Fmt.(vbox (list Pretty.gcom)) assume_preconditions);
    (* then compile the body of the method into gc *)
    let body_gs =
      compile_block (S.meth.body)
    in

    Logs.debug (fun m -> m "Body Callee:");
    Logs.debug (fun m -> m "%a" Fmt.(vbox (list Pretty.gcom)) body_gs);

    let assert_postconditions = List.map ~f:(fun s -> Assert (Subst.formula (fst S.meth.returns) S.meth.ret s)) S.meth.ensures in

    Logs.debug (fun m -> m "Post-conditions Callee:");
    Logs.debug (fun m -> m "%a" Fmt.(vbox (list Pretty.gcom)) assert_postconditions);

    let gs = assume_preconditions @ body_gs @ assert_postconditions in
    Logs.debug (fun m -> m "Guarded commands:");
    Logs.debug (fun m -> m "%a" Fmt.(vbox (list Pretty.gcom)) gs);

    (* compute verification condition (VC) using weakest-precondition *)
    let vc = wp_seq gs (FBool true) in
    Logs.debug (fun m -> m "Verification condition:");
    Logs.debug (fun m -> m "%a" Pretty.formula vc);

    (* check if the VC is valid under the current gamma *)
    let status = Smt.check_validity (gamma ()) vc in
    match status with
    | Smt.Valid -> Logs.app (fun m -> m "%s: verified" S.meth.id)
    | Smt.Invalid cex ->
        Logs.app (fun m -> m "%s: not verified" S.meth.id);
        Logs.app (fun m -> m "Counterexample:");
        Logs.app (fun m -> m "%s" cex)
    | Smt.Unknown -> Logs.app (fun m -> m "%s: unknown" S.meth.id)
  (* this function doesn't return anything, so it implicitly
     returns the unit value "()" *)
end

(** Public function for verifying a difny method *)
let go (prog : Lang.prog) (meth : Lang.meth) : unit =
  (* construct a verifier module (verification happens during module construction) *)
  let module Verifier = Make (struct
    let prog = prog
    let meth = meth
  end) in
  (* retrieve the result, which is just a unit value *)
  Verifier.result
