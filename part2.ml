type const =
  | Unit
  | Int of int
  | Bool of bool
  | Name of string

type cmd =
  | Push of const
  | Pop of int
  | Add of int
  | Sub of int
  | Mul of int
  | Div of int
  | Trace of int
  | And 
  | Or 
  | Not 
  | Equal
  | Lte 
  | Local
  | Global 
  | Lookup
  | BeginEnd of cmds
  | IfElse of (cmds * cmds)


and cmds = cmd list

type env = (string * value) list

and value =
  | VUnit
  | VInt of int
  | VBool of bool
  | VName of string

type stack = value list

type log = string list

let string_of_value v =
  match v with
  | VUnit -> "()"
  | VInt i -> string_of_int i
  | VBool b ->
    if b then
      "True"
    else
      "False"
  | VName a -> a

let debug v =
  match v with
  | VUnit -> "VUnit"
  | VInt i -> string_of_int i
  | VBool b ->
    if b then
      "V(True)"
    else
      "V(False)"
  | VName a -> a

let rec addn n ls =
  if n < 0 then
    None
  else if n = 0 then
    Some (0, ls)
  else
    match ls with
    | VInt x :: ls -> (
      match addn (n - 1) ls with
      | Some (y, ls) -> Some (x + y, ls)
      | None -> None)
    | _ -> None

let subn n ls =
  if n < 0 then
    None
  else if n = 0 then
    Some (0, ls)
  else
    match ls with
    | VInt x :: ls -> (
      match addn (n - 1) ls with
      | Some (y, ls) -> Some (x - y, ls)
      | None -> None)
    | _ -> None

let rec muln n ls =
  if n < 0 then
    None
  else if n = 0 then
    Some (1, ls)
  else
    match ls with
    | VInt x :: ls -> (
      match muln (n - 1) ls with
      | Some (y, ls) -> Some (x * y, ls)
      | None -> None)
    | _ -> None

let rec divn n ls =
  if n < 0 then
    None
  else if n = 0 then
    Some (1, ls)
  else
    match ls with
    | VInt x :: ls -> (
      match muln (n - 1) ls with
      | Some (0, ls) -> None
      | Some (y, ls) -> Some (x / y, ls)
      | None -> None)
    | _ -> None

let rec popn n ls =
  if n < 0 then
    None
  else if n = 0 then
    Some ls
  else
    match ls with
    | _ :: ls -> (
      match popn (n - 1) ls with
      | Some ls -> Some ls
      | None -> None)
    | _ -> None

let rec tracen n ls =
  if n < 0 then
    None
  else if n = 0 then
    Some ([], ls)
  else
    match ls with
    | v :: ls -> (
      match tracen (n - 1) ls with
      | Some (log, ls) -> Some (string_of_value v :: log, ls)
      | None -> None)
    | _ -> None

let localn (st:stack) (env_local:env): (stack option*env) =
  if List.length(st) < 2 then (None,env_local)
  else match st with
  |VName a::rest->(
    match rest with 
    |VInt i::st' -> (Some (VUnit::st'),((a,VInt i)::env_local))
    |VBool b::st' -> (Some(VUnit::st'),((a,VBool b)::env_local))
    |VName c ::st' -> (Some(VUnit::st'),((a,VName c)::env_local))
    |VUnit ::st'-> (Some(VUnit::st'),((a,VUnit)::env_local))
    |_ -> (None,env_local))
  |_-> (None,env_local)

let globaln (st:stack) (env_global:env): (stack option*env) =
    if List.length(st) < 2 then (None,env_global)
    else match st with
    |VName a::rest->(
      match rest with 
      |VInt i::st' -> (Some (VUnit::st'),((a,VInt i)::env_global))
      |VBool b::st' -> (Some(VUnit::st'),((a,VBool b)::env_global))
      |VName c ::st' -> (Some(VUnit::st'),((a,VName c)::env_global))
      |VUnit ::st'-> (Some(VUnit::st'),((a,VUnit)::env_global))
      |_ -> (None,env_global))
    |_-> (None,env_global)

let fst (a,b) = a
let snd (a,b) = b
let lookupn (st:stack) (env_global:env) (env_local:env): stack option =
    if List.length(st) == 0 then None
    else match st with
    |VName a :: rest -> (if ((List.filter (fun x -> if fst x = a then true else false ) env_global)!= []
                           &&(List.filter(fun x -> if fst x = a then true else false) env_local)!=[]) 
                           then Some(snd(List.nth (List.filter(fun x -> if fst x = a then true else false) env_local) 0)::rest)
                           else if ((List.filter (fun x -> if fst x = a then true else false ) env_global)!= []
                           &&(List.filter(fun x -> if fst x = a then true else false) env_local) ==[])
                           then Some(snd(List.nth (List.filter(fun x -> if fst x = a then true else false) env_global) 0)::rest)
                           else if ((List.filter (fun x -> if fst x = a then true else false ) env_global)== []
                           &&(List.filter(fun x -> if fst x = a then true else false) env_local) !=[])
                           then Some(snd(List.nth (List.filter(fun x -> if fst x = a then true else false) env_local) 0)::rest)
                           else None
    )
    | _ -> None

    
let rec eval (env_local:env) (env_global:env) (st : stack) (log : log) (cmds : cmds) : env * env * log * stack option =
  match cmds with
  | Push cst :: cmds -> (
    match cst with
    | Unit -> eval env_local env_global (VUnit :: st) log cmds
    | Int i -> eval env_local env_global (VInt i :: st) log cmds
    | Bool b -> eval env_local env_global (VBool b :: st) log cmds
    | Name a -> eval env_local env_global (VName a ::st) log cmds)
  | Pop n :: cmds -> (
    match popn n st with
    | Some st -> eval env_local env_global st log cmds
    | _ -> (env_local,env_global,log, None))
  | Add n :: cmds -> (
    match addn n st with
    | Some (x, st) -> eval env_local env_global (VInt x :: st) log cmds
    | _ -> (env_local,env_global,log, None))
  | Sub n :: cmds -> (
    match subn n st with
    | Some (x, st) -> eval env_local env_global (VInt x :: st) log cmds
    | _ -> (env_local,env_global,log, None))
  | Mul n :: cmds -> (
    match muln n st with
    | Some (x, st) -> eval env_local env_global (VInt x :: st) log cmds
    | _ -> (env_local,env_global,log, None))
  | Div n :: cmds -> (
    match divn n st with
    | Some (x, st) -> eval env_local env_global (VInt x :: st) log cmds
    | _ -> (env_local,env_global,log, None))
  | Trace n :: cmds -> (
    match tracen n st with
    | Some (lg, st) -> eval env_local env_global st (List.rev lg @ log) cmds
    | _ -> (env_local,env_global,log, None))
    |
    And::cmds -> (
      match st with 
      |VBool a::VBool b::rest ->eval env_local env_global (VBool (a&&b)::rest) log cmds
      |_ -> (env_local,env_global,log,None)
    )
  |
    Or::cmds -> (
      match st with 
      |VBool a::VBool b::rest ->eval env_local env_global (VBool (a||b)::rest) log cmds
      |_ -> (env_local,env_global,log,None)
    )
  |
    Not::cmds -> (
      match st with 
      |VBool a::rest -> if a == true then eval env_local env_global (VBool false::rest) log cmds
                        else eval env_local env_global (VBool true::rest) log cmds
      |_ -> (env_local,env_global,log,None)
    )
  |
    Equal::cmds -> (
      match st with 
      |VInt a::VInt b::rest -> if a == b then eval env_local env_global (VBool true::rest) log cmds
                                 else eval env_local env_global (VBool false::rest) log cmds
      |_ -> (env_local,env_global,log,None)
    )
  |
    Lte::cmds -> (
      match st with 
      |VInt a::VInt b::rest -> if a <= b then eval env_local env_global (VBool true::rest) log cmds
      else eval env_local env_global (VBool false::rest) log cmds
      |_ -> (env_local,env_global,log,None)
    )
  | Local::cmds -> (
      match localn st env_local with
      |(Some st', env_local') -> eval env_local' env_global st' log cmds
      |(None, _) -> (env_local,env_global,log,None)
  )
  | Global::cmds -> (
    match globaln st env_global with
    |(Some st', env_global') -> eval env_local env_global' st' log cmds
    |(None, _) -> (env_local,env_global,log,None)
  )
  | Lookup::cmds -> (
    match lookupn st env_global env_local with
    |Some st' -> eval env_local env_global st' log cmds
    |None -> (env_local,env_global,log, None)
  )
  | BeginEnd cmdss::cmds -> (
    match eval env_local env_global [] log cmdss with
    | (env_local',env_global',log, Some st') -> if (List.nth_opt st' 0 != None) then eval env_local env_global' (List.nth st' 0::st) log cmds
                                     else (env_local,env_global,log,None)
    | (env_local',env_global',log, None) -> (env_local,env_global,log, None)
  )
  | IfElse (cmdss1,cmdss2)::cmds -> (match st with
                                     | VBool true::rest -> (match (eval env_local env_global rest log cmdss1) with
                                                            |(env_local',env_global',log, Some st') -> eval env_local' env_global' st' log cmds
                                                            |(env_local',env_global',log, None) -> (env_local,env_global,log, None))
                                     | VBool false::rest -> (match (eval env_local env_global rest log cmdss2) with
                                                            |(env_local',env_global',log, Some st') -> eval env_local' env_global' st' log cmds
                                                            |(env_local',env_global',log, None) -> (env_local,env_global,log, None))
                                     | _ -> (env_local,env_global,log, None))

  | _ -> (env_local,env_global,log, Some st)

(* parsing util functions *)

let is_lower_case c = 'a' <= c && c <= 'z'

let is_upper_case c = 'A' <= c && c <= 'Z'

let is_alpha c = is_lower_case c || is_upper_case c

let is_digit c = '0' <= c && c <= '9'

let is_alphanum c = is_lower_case c || is_upper_case c || is_digit c

let is_blank c = String.contains " \012\n\r\t" c

let explode s = List.of_seq (String.to_seq s)

let implode ls = String.of_seq (List.to_seq ls)

let readlines (file : string) : string =
  let fp = open_in file in
  let rec loop () =
    match input_line fp with
    | s -> s ^ "\n" ^ loop ()
    | exception End_of_file -> ""
  in
  let res = loop () in
  let () = close_in fp in
  res

(* end of util functions *)

(* parser combinators *)

type 'a parser = char list -> ('a * char list) option

let parse (p : 'a parser) (s : string) : ('a * char list) option = p (explode s)

let pure (x : 'a) : 'a parser = fun ls -> Some (x, ls)

let fail : 'a parser = fun ls -> None

let bind (p : 'a parser) (q : 'a -> 'b parser) : 'b parser =
 fun ls ->
  match p ls with
  | Some (a, ls) -> q a ls
  | None -> None

let ( >>= ) = bind

let ( let* ) = bind

let read : char parser =
 fun ls ->
  match ls with
  | x :: ls -> Some (x, ls)
  | _ -> None

let satisfy (f : char -> bool) : char parser =
 fun ls ->
  match ls with
  | x :: ls ->
    if f x then
      Some (x, ls)
    else
      None
  | _ -> None

let char (c : char) : char parser = satisfy (fun x -> x = c)

let seq (p1 : 'a parser) (p2 : 'b parser) : 'b parser =
 fun ls ->
  match p1 ls with
  | Some (_, ls) -> p2 ls
  | None -> None

let ( >> ) = seq

let seq' (p1 : 'a parser) (p2 : 'b parser) : 'a parser =
 fun ls ->
  match p1 ls with
  | Some (x, ls) -> (
    match p2 ls with
    | Some (_, ls) -> Some (x, ls)
    | None -> None)
  | None -> None

let ( << ) = seq'

let alt (p1 : 'a parser) (p2 : 'a parser) : 'a parser =
 fun ls ->
  match p1 ls with
  | Some (x, ls) -> Some (x, ls)
  | None -> p2 ls

let ( <|> ) = alt

let map (p : 'a parser) (f : 'a -> 'b) : 'b parser =
 fun ls ->
  match p ls with
  | Some (a, ls) -> Some (f a, ls)
  | None -> None

let ( >|= ) = map

let ( >| ) p c = map p (fun _ -> c)

let rec many (p : 'a parser) : 'a list parser =
 fun ls ->
  match p ls with
  | Some (x, ls) -> (
    match many p ls with
    | Some (xs, ls) -> Some (x :: xs, ls)
    | None -> Some ([ x ], ls))
  | None -> Some ([], ls)

let rec many1 (p : 'a parser) : 'a list parser =
 fun ls ->
  match p ls with
  | Some (x, ls) -> (
    match many p ls with
    | Some (xs, ls) -> Some (x :: xs, ls)
    | None -> Some ([ x ], ls))
  | None -> None

let rec many' (p : unit -> 'a parser) : 'a list parser =
 fun ls ->
  match p () ls with
  | Some (x, ls) -> (
    match many' p ls with
    | Some (xs, ls) -> Some (x :: xs, ls)
    | None -> Some ([ x ], ls))
  | None -> Some ([], ls)

let rec many1' (p : unit -> 'a parser) : 'a list parser =
 fun ls ->
  match p () ls with
  | Some (x, ls) -> (
    match many' p ls with
    | Some (xs, ls) -> Some (x :: xs, ls)
    | None -> Some ([ x ], ls))
  | None -> None

let whitespace : unit parser =
 fun ls ->
  match ls with
  | c :: ls ->
    if String.contains " \012\n\r\t" c then
      Some ((), ls)
    else
      None
  | _ -> None

let ws : unit parser = many whitespace >| ()

let ws1 : unit parser = many1 whitespace >| ()

let digit : char parser = satisfy is_digit

let natural : int parser =
 fun ls ->
  match many1 digit ls with
  | Some (xs, ls) -> Some (int_of_string (implode xs), ls)
  | _ -> None

let literal (s : string) : unit parser =
 fun ls ->
  let cs = explode s in
  let rec loop cs ls =
    match (cs, ls) with
    | [], _ -> Some ((), ls)
    | c :: cs, x :: xs ->
      if x = c then
        loop cs xs
      else
        None
    | _ -> None
  in
  loop cs ls

let keyword (s : string) : unit parser = literal s >> ws >| ()

(* end of parser combinators *)

let reserved =
  [ "Push"
  ; "True"
  ; "False"
  ; "Pop"
  ; "Add"
  ; "Sub"
  ; "Mul"
  ; "Div"
  ; "Equal"
  ; "Lte"
  ; "And"
  ; "Or"
  ; "Not"
  ; "Trace"
  ; "Local"
  ; "Global"
  ; "Lookup"
  ; "Begin"
  ; "If"
  ; "Else"
  ; "Fun"
  ; "End"
  ; "Call"
  ; "Try"
  ; "Switch"
  ; "Case"
  ]

let name : string parser =
  let* c = satisfy is_alpha in
  let* cs = many (satisfy (fun c -> is_alphanum c || c = '_' || c = '\'')) in
  let s = implode (c :: cs) in
  if List.exists (fun x -> x = s) reserved then
    fail
  else
    pure s << ws

let unit_parser () =
  let* _ = keyword "()" in
  pure Unit

let int_parser () =
  (let* n = natural in
   pure (Int n) << ws)
  <|> let* _ = keyword "-" in
      let* n = natural in
      pure (Int (-n)) << ws

let true_parser () =
  let* _ = keyword "True" in
  pure true

let false_parser () =
  let* _ = keyword "False" in
  pure false

let bool_parser () =
  let* b = true_parser () <|> false_parser () in
  pure (Bool b)

let name_parser () = 
  let* a = name in 
  pure (Name a)

let const_parser () = int_parser () <|> bool_parser () <|> unit_parser () <|> name_parser ()

let rec push_parser () =
  let* _ = keyword "Push" in
  let* cst = const_parser () in
  pure (Push cst)

let rec pop_parser () =
  let* _ = keyword "Pop" in
  let* n = natural in
  pure (Pop n) << ws

and add_parser () =
  let* _ = keyword "Add" in
  let* n = natural in
  pure (Add n) << ws

and sub_parser () =
  let* _ = keyword "Sub" in
  let* n = natural in
  pure (Sub n) << ws

and mul_parser () =
  let* _ = keyword "Mul" in
  let* n = natural in
  pure (Mul n) << ws

and div_parser () =
  let* _ = keyword "Div" in
  let* n = natural in
  pure (Div n) << ws

and trace_parser () =
  let* _ = keyword "Trace" in
  let* n = natural in
  pure (Trace n) << ws

and and_parser () = 
  let* _ = keyword "And" in
  pure (And) << ws

and or_parser () = 
  let* _ = keyword "Or" in
  pure (Or) << ws

and not_parser () =
  let* _ = keyword "Not" in
  pure (Not) << ws

and equal_parser () = 
  let* _ = keyword "Equal" in
  pure (Equal) << ws

and lte_parser () = 
  let* _ = keyword "Lte" in
  pure (Lte) << ws

and local_parser () = 
  let* _ = keyword "Local" in
  pure (Local) << ws

and global_parser () = 
  let* _ = keyword "Global" in
  pure (Global) << ws

and lookup_parser () = 
  let* _ = keyword "Lookup" in 
  pure (Lookup) << ws

and begin_end_parser () = 
  let* _ = keyword "Begin" in
  let* cmds = cmds_parser () in
  let* _ = keyword "End" in
  pure (BeginEnd cmds) << ws

and if_else_parser () = 
  let* _ = keyword "If" in 
  let* cmds1 = cmds_parser () in
  let* _ = keyword "Else" in
  let* cmds2 = cmds_parser () in 
  let* _ = keyword "End" in
  pure (IfElse (cmds1, cmds2)) << ws


and cmd_parser () =
  push_parser () <|> pop_parser () <|> trace_parser () <|> add_parser ()
  <|> sub_parser () <|> mul_parser () <|> div_parser () <|> and_parser ()
  <|> or_parser () <|> not_parser () <|> equal_parser () <|> lte_parser ()
  <|> local_parser () <|> global_parser () <|> lookup_parser () <|> begin_end_parser ()
  <|> if_else_parser ()

and cmds_parser () = many (cmd_parser ())

let parse_cmds s = parse (ws >> cmds_parser ()) s

let interp (src : string) : string list =
  match parse_cmds src with
  | Some (cmds, []) -> (
    match eval [] [] [] [] cmds with
    | _,_,log, Some _ -> log
    | _,_,_, None -> [ "Error" ])
  | _ -> [ "Error" ]

let main fname =
  let src = readlines fname in
  interp src
