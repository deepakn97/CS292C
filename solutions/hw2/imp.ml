open Base

(** Arithmetic ops *)
type aop = Add | Sub | Mul | Div | Mod

(** Arithmetic expressions *)
type aexp =
  | Int of int  (** integer constant *)
  | Aop of aop * aexp * aexp  (** arithmetic op *)
  | Var of string  (** variable *)
  | Select of { arr : aexp; idx : aexp }  (** McCarthy's array read *)
  | Store of { arr : aexp; idx : aexp; value : aexp }
      (** McCarthy's array write *)

type path = { var : string; indices : aexp list }
(** Variable / array access path expression *)

let var_of_path (p : path) : string =
  match p.indices with
  | [] -> p.var
  | _ -> failwith Fmt.(str "var_of_path: %s is not a variable" p.var)

(** Comparison ops  *)
type comp = Eq | Neq | Lt | Leq | Gt | Geq

(** Boolean expressions *)
type bexp =
  (* boolean constant *)
  | Bool of bool
  (* integer comparison *)
  | Comp of comp * aexp * aexp
  (* negation *)
  | Not of bexp
  (* conjunction *)
  | And of bexp * bexp
  (* disjunction *)
  | Or of bexp * bexp

(** Quantifiers *)
type quantifier = Forall | Exists

(** Logical connectives *)
type connective = And | Or | Imply | Iff

(** First-order logic formulas *)
type formula =
  | FBool of bool  (** boolean constant *)
  | FComp of comp * aexp * aexp  (** integer comparison *)
  | FQ of quantifier * string * formula
      (** first-order quantification over an integer variable *)
  | FNot of formula  (** negation of a formula *)
  | FConn of connective * formula * formula  (** logical connective *)

(** Commands *)
type com =
  (* assignment, aka memory write *)
  | Assign of { lhs : string; rhs : aexp }
  (* conditional *)
  | If of { cond : bexp; thn : block; els : block }
  (* while-loop *)
  | While of { cond : bexp; inv : formula list; body : block }
  (* assume *)
  | Assume of formula
  (* assert *)
  | Assert of formula
  (* havoc *)
  | Havoc of string
  (* print *)
  | Print of aexp
  (* function call *)
  | Call of { lhs : string; callee : string; args : aexp list }

and block = com list
(** A block is a sequence of commands *)

(** Type *)
type ty = TInt  (** integer type *) | TArr of ty  (** array type *)

type gamma = (string * ty) list
(** gamma maps variables to their types *)

exception Unbound

let ty (gamma : gamma) ~of_:(x : string) : ty option =
  List.Assoc.find gamma x ~equal:String.equal

let ty_exn (gamma : gamma) ~of_:(x : string) : ty =
  match ty gamma ~of_:x with
  | Some t -> t
  | None ->
      Logs.err (fun m -> m "Unbound variable %s" x);
      raise Unbound

type meth = {
  id : string;  (** method name *)
  params : gamma;  (** method parameters *)
  returns : string * ty;  (** return identifier and type *)
  requires : formula list;  (** preconditions *)
  ensures : formula list;  (** postconditions *)
  locals : gamma;  (** local variables *)
  body : block;  (** method body *)
  ret : aexp;  (** return value *)
}
(** Method *)

type prog = meth list
(** Program *)

(** Helper functions to build IMP expressions and formulas *)
module Syntax = struct
  let var x = { var = x; indices = [] }
  let ( ! ) acc = Var acc
  let i n = Int n
  let ( + ) e1 e2 = Aop (Add, e1, e2)
  let ( - ) e1 e2 = Aop (Sub, e1, e2)
  let ( * ) e1 e2 = Aop (Mul, e1, e2)
  let ( / ) e1 e2 = Aop (Div, e1, e2)
  let ( % ) e1 e2 = Aop (Mod, e1, e2)
  let select arr idx = Select { arr; idx }
  let store arr idx value = Store { arr; idx; value }

  module Bexp = struct
    let true_ = Bool true
    let false_ = Bool false
    let ( == ) e1 e2 = Comp (Eq, e1, e2)
    let ( != ) e1 e2 = Comp (Neq, e1, e2)
    let ( < ) e1 e2 = Comp (Lt, e1, e2)
    let ( <= ) e1 e2 = Comp (Leq, e1, e2)
    let ( > ) e1 e2 = Comp (Gt, e1, e2)
    let ( >= ) e1 e2 = Comp (Geq, e1, e2)
    let ( && ) b1 b2 : bexp = And (b1, b2)
    let ( || ) b1 b2 : bexp = Or (b1, b2)
    let not b = Not b
  end

  module Formula = struct
    let forall x f = FQ (Forall, x, f)
    let exists x f = FQ (Exists, x, f)
    let true_ = FBool true
    let false_ = FBool false
    let ( && ) f1 f2 = FConn (And, f1, f2)
    let ( || ) f1 f2 = FConn (Or, f1, f2)
    let ( ==> ) f1 f2 = FConn (Imply, f1, f2)
    let ( <=> ) f1 f2 = FConn (Iff, f1, f2)
    let not f = FNot f
    let ( == ) e1 e2 = FComp (Eq, e1, e2)
    let ( != ) e1 e2 = FComp (Neq, e1, e2)
    let ( < ) e1 e2 = FComp (Lt, e1, e2)
    let ( <= ) e1 e2 = FComp (Leq, e1, e2)
    let ( > ) e1 e2 = FComp (Gt, e1, e2)
    let ( >= ) e1 e2 = FComp (Geq, e1, e2)
  end

  let ( := ) lhs rhs = Assign { lhs; rhs }
  let havoc x = Havoc x
end

(** Pretty printers. You don't need to understand how these work. *)
module Pretty = struct
  open Fmt

  let aop : aop t =
    using
      (function
        | Add -> "+" | Sub -> "-" | Mul -> "*" | Div -> "/" | Mod -> "%")
      string

  let rec aexp : aexp t =
    let is_complex = function Aop _ -> true | _ -> false in
    (* parenthesized *)
    let p ppf e = if is_complex e then parens aexp ppf e else aexp ppf e in
    fun ppf -> function
      | Int n -> int ppf n
      | Aop (op, e1, e2) -> pf ppf "@[%a %a %a@]" p e1 aop op p e2
      | Var x -> pf ppf "%s" x
      | Select { arr; idx } -> pf ppf "select(@[%a, %a@])" aexp arr aexp idx
      | Store { arr; idx; value } ->
          pf ppf "store(@[%a,@ %a,@ %a@])" aexp arr aexp idx aexp value

  and path : path t =
   fun ppf { var; indices } ->
    pf ppf "@[<h>%a%a@]" string var (list (brackets aexp)) indices

  let comp : comp t =
    using
      (function
        | Eq -> "=="
        | Neq -> "!="
        | Lt -> "<"
        | Leq -> "<="
        | Gt -> ">"
        | Geq -> ">=")
      string

  let connective : connective t =
    using
      (function And -> "&&" | Or -> "||" | Imply -> "==>" | Iff -> "<=>")
      string

  let rec bexp : bexp t =
    let is_complex : bexp -> bool = function
      | And _ | Or _ -> true
      | _ -> false
    in
    let p ppf b = if is_complex b then parens bexp ppf b else bexp ppf b in
    fun ppf -> function
      | Bool b -> bool ppf b
      | Comp (op, e1, e2) -> pf ppf "@[%a %a %a@]" aexp e1 comp op aexp e2
      | Not b -> pf ppf "!%a" p b
      | And (b1, b2) -> pf ppf "@[%a && %a@]" p b1 p b2
      | Or (b1, b2) -> pf ppf "@[%a || %a@]" p b1 p b2

  let quantifier : quantifier t =
    using (function Forall -> "forall" | Exists -> "exists") string

  let connective : connective t =
    using
      (function And -> "&&" | Or -> "||" | Imply -> "==>" | Iff -> "<=>")
      string

  let rec formula : formula t =
    let is_complex = function FQ _ | FConn _ -> true | _ -> false in
    let p ppf f =
      if is_complex f then parens formula ppf f else formula ppf f
    in
    fun ppf -> function
      | FBool b -> bool ppf b
      | FComp (o, e1, e2) -> pf ppf "@[%a %a@ %a@]" aexp e1 comp o aexp e2
      | FQ (q, x, f) -> pf ppf "@[<2>%a %s ::@ %a@]" quantifier q x formula f
      | FNot f -> pf ppf "!%a" (parens formula) f
      | FConn (op, f1, f2) -> pf ppf "%a %a@ %a" p f1 connective op p f2

  let rec com : com t =
    let invariant ppf f = pf ppf "  @[<2>invariant %a@]" formula f in
    fun ppf -> function
      | Assign { lhs; rhs } -> pf ppf "%s := %a;" lhs aexp rhs
      | If { cond; thn; els } ->
          pf ppf "if %a %a else %a" bexp cond block thn block els
      | While { cond; inv = []; body } ->
          pf ppf "while (%a)@ %a" bexp cond block body
      | While { cond; inv; body } ->
          pf ppf "while (%a)@\n%a %a" bexp cond
            (vbox (list invariant))
            inv block body
      | Assume f -> pf ppf "assume %a;" formula f
      | Assert f -> pf ppf "assert %a;" formula f
      | Havoc x -> pf ppf "%s := *;" x
      | Print e -> pf ppf "print(@[%a@]);" aexp e
      | Call { lhs; callee; args } ->
          pf ppf "%s := %s(@[%a@]);" lhs callee (list ~sep:comma aexp) args

  and block ppf coms = pf ppf "{@   @[<v>%a@]@ }" (list ~sep:cut com) coms

  let rec ty : ty t =
   fun ppf -> function
    | TInt -> string ppf "int"
    | TArr t -> pf ppf "array<%a>" ty t

  let meth : meth t =
    let param = pair ~sep:(any ": ") string ty in
    let local ppf (x, t) = pf ppf "var %s: %a;@ " x ty t in
    let pp_returns ppf (x, t) = pf ppf "returns (%s: %a)" x ty t in
    let pp_requires ppf f = pf ppf "requires %a@ " formula f in
    let pp_ensures ppf f = pf ppf "ensures %a@ " formula f in
    let pp_ret ppf e = pf ppf "return %a;" aexp e in
    fun ppf { id; params; returns; requires; ensures; locals; body; ret } ->
      pf ppf "method %s(%a) %a@\n  @[<v>%a%a@]@\n{@   @[<hv>%a%a@ %a@]@\n}@\n"
        id
        (* params *)
        (hvbox @@ list ~sep:comma param)
        params (* returns *)
        pp_returns returns
        (* requires *)
        (list ~sep:nop pp_requires)
        requires
        (* ensures *)
        (list ~sep:nop pp_ensures)
        ensures (* locals *)
        (list ~sep:nop local) locals (* body *)
        (list com) body (* return *)
        pp_ret ret

  let prog : prog t = vbox @@ list ~sep:(cut ++ cut) meth
end