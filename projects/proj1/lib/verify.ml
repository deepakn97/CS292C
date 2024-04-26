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
    | Call { lhs; callee; args } -> Todo.at_level 3 ~msg:"Verify.modified: Call"
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
    (* NOTE: How do we determine if lhs is integer or array? This is needed for fresh_var. *)
    | Assign { lhs; rhs } -> 
      (
        let tmp = fresh_var TInt ~hint:lhs in
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
    | Call { lhs; callee; args } -> Todo.at_level 3 ~msg:"Verify.compile: Call"
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
    | Havoc x -> Subst.formula x (Var (fresh_var TInt ~hint:x)) f
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

    (* compile method to guarded commands *)
    (* here we have to convert the method into a list of statements *)
    let gs =
      compile_block (Todo.at_level 2 ~msg:"compile_block" ~dummy:S.meth.body)
    in
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
