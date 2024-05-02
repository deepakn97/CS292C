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
      (
        match e with
        | Var c -> if String.equal x a then FQ (q, c, formula x e b) else FQ (q, a, formula x e b)
        | _ -> FQ (q, a, formula x e b)
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
    (* Here lhs is being modified along with all the variables in the body *)
    (* args will be added to the modified list if the callee method is same as method to verify. Because that is a case of recursion. Todo.at_level 5 *)
    (* | Call { lhs; callee; args } -> 
      (
        let callee_meth = find_meth callee in
        (* since this is the caller implementation of this, we don't need to add the internal args to the modified variables *)
        let modified_vars = modified_block callee_meth.body in
        [lhs] @ modified_vars
      ) *)
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
        (* subst pre-conditions with args *)
        (* we need to replace all the func params with their temp variables in the args aexp before passing to the function *)
        (* here we are substituing the instances of input params for current method in all the args with fresh params *)
        (* we need to find all the current method variables which are being used in args and substitute only them with fresh params*)
        let used_vars = List.dedup_and_sort ~compare:String.compare (List.concat_map ~f:find_vars_aexp args) in
        let fresh_params_mapping = List.map ~f:(fun x -> (x, fresh_var (Utils.ty_exn (gamma ()) ~of_:x) ~hint:x)) used_vars in
        let rec subst_fresh_params_arg (arg: aexp) (mapping: (string * string) list): aexp = 
          match mapping with
          | [] -> arg
          | (param, fresh_param)::xs -> Subst.aexp param (Var fresh_param) (subst_fresh_params_arg arg xs)
        in
        (* now we want to create a mapping between callee params and fresh args (caller params replaced with fresh variables) *)
        let subst_args = List.map ~f:(fun arg -> subst_fresh_params_arg arg fresh_params_mapping) args in
        (* before we can use the fresh params, we have to assume the values *)
        (* let assume_fresh_params = List.map2_exn ~f:(fun (x, t) fresh_arg -> Assume (FComp (Eq, Var fresh_arg, Var x))) S.meth.params fresh_params in *)
        let assume_fresh_params = List.map ~f:(fun (x, fresh_arg) -> Assume (FComp (Eq, Var fresh_arg, Var x))) fresh_params_mapping in
        let havoc_params = List.map ~f:(fun (x, _) -> Havoc x) fresh_params_mapping in
        (* this function substitutes occurances of all params with their values in a given formula *)
        let rec subst_param_arg (cond: formula) (mapping: (string * aexp) list): formula = 
          match mapping with
          | [] -> cond
          | (param, arg)::xs -> Subst.formula param arg (subst_param_arg cond xs)
        in
        let callee_params_args_mapping = List.map2_exn ~f:(fun (x, t) arg -> (x, arg)) callee_meth.params subst_args in
        let subst_preconditions = List.map ~f:(fun f -> Assert (subst_param_arg f callee_params_args_mapping)) callee_meth.requires in
        (* subst post-conditions with lhs *)
        let (return_param, _) = callee_meth.returns in
        (* substitute all the params with their new aexp values in the postconditions *)
        let subst_args_postconditions = List.map ~f:(fun f -> subst_param_arg f callee_params_args_mapping) callee_meth.ensures in
        (* now substitute the return param of the callee with lhs, because we want to assert the postcondition on that *)
        let subst_postconditions = List.map ~f:(fun f -> Assume (Subst.formula return_param (Var lhs) f)) subst_args_postconditions in
        
        Logs.debug (fun m -> m "Assuming fresh params:");
        Logs.debug (fun m -> m "%a" Fmt.(vbox (list Pretty.gcom)) assume_fresh_params);
        Logs.debug (fun m -> m "Havoc params:");
        Logs.debug (fun m -> m "%a" Fmt.(vbox (list Pretty.gcom)) havoc_params);
        Logs.debug (fun m -> m "Subst preconditions:");
        Logs.debug (fun m -> m "%a" Fmt.(vbox (list Pretty.gcom)) subst_preconditions);
        Logs.debug (fun m -> m "Subst postconditions:");
        Logs.debug (fun m -> m "%a" Fmt.(vbox (list Pretty.gcom)) subst_postconditions);
        assume_fresh_params @ havoc_params @ subst_preconditions @ subst_postconditions
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

    (* let param_strings = List.dedup_and_sort ~compare:String.compare ((List.map ~f:(fun (x, _) -> x) S.meth.params)) in
    (* add return parameter in the mapping *)
    let fresh_params_mapping = (List.map ~f:(fun x -> (x, fresh_var (Utils.ty_exn (gamma ()) ~of_:x) ~hint:x)) param_strings) in
    (* substitute all the params with fresh variables in the return statement *)
    let subst_params_return_statement = List.fold_left ~f:(fun acc (x, t) -> Subst.aexp x (Var t) acc) ~init:S.meth.ret fresh_params_mapping in
    (* before we can use the fresh params, we have to assume the values *)
    (* let assume_fresh_params = List.map2_exn ~f:(fun (x, t) fresh_arg -> Assume (FComp (Eq, Var fresh_arg, Var x))) S.meth.params fresh_params in *)
    let assume_fresh_params = List.map ~f:(fun (x, fresh_arg) -> Assume (FComp (Eq, Var fresh_arg, Var x))) fresh_params_mapping in
    let havoc_params = List.map ~f:(fun (x, _) -> Havoc x) fresh_params_mapping in
    (* this function substitutes occurances of all params with their values in a given formula *)
    let rec subst_formula_params (cond: formula) (mapping: (string * string) list): formula = 
      match mapping with
      | [] -> cond
      | (param, fresh_param)::xs -> Subst.formula param (Var fresh_param) (subst_formula_params cond xs)
    in
    (* substitute the method params with fresh variables in the preconditions *)
    let pre_gs = List.map ~f:(fun f -> Assume (subst_formula_params f fresh_params_mapping)) S.meth.requires in

    (* substitute all input params in postconditions *)
    let subst_params_postconditions = List.map ~f:(fun f -> subst_formula_params f fresh_params_mapping) S.meth.ensures in
    (* substitute the return param with the new return statement in the postconditions *)
    let subst_return_param_postconditions = List.map ~f:(fun f -> Subst.formula (fst S.meth.returns) subst_params_return_statement f) subst_params_postconditions in
    (* assert the postconditions *)
    let post_gs = List.map ~f:(fun f -> Assert f) subst_return_param_postconditions in *)

    (* compile method to guarded commands *)
    (* here we have to convert the method into a list of statements *)
    (* This is where the callee implementation will go*)
    (* Here we have to assume pre-conditions and assert postconditions *)
    (* first compile pre-conditions into gc *)
    let pre_gs = List.map ~f:(fun s -> Assume s) S.meth.requires in

    Logs.debug (fun m -> m "Pre-conditions Callee:");
    Logs.debug (fun m -> m "%a" Fmt.(vbox (list Pretty.gcom)) pre_gs);
    (* then compile the body of the method into gc *)
    let body_gs =
      compile_block (S.meth.body)
    in

    Logs.debug (fun m -> m "Body Callee:");
    Logs.debug (fun m -> m "%a" Fmt.(vbox (list Pretty.gcom)) body_gs);

    let post_gs = List.map ~f:(fun s -> Assert (Subst.formula (fst S.meth.returns) S.meth.ret s)) S.meth.ensures in

    Logs.debug (fun m -> m "Post-conditions Callee:");
    Logs.debug (fun m -> m "%a" Fmt.(vbox (list Pretty.gcom)) post_gs);
    let gs = pre_gs @ body_gs @ post_gs in
    (* compile post-conditions as assert statements *)
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
