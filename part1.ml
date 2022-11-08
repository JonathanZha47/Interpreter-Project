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

(* parser cmdbinators *)

type 'a parser = char list -> ('a * char list) option

let parse (p : 'a parser) (s : string) : ('a * char list) option = 
  p (explode s)

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

(* end of parser cmdbinators *)


type const = 
    INT of int
  |
    Bool of bool
  |
    Unit of unit

type cmd = 
    Push of const
  |
    Pop of int
  |
    Trace of int
  |
    Add of int 
  |
    Sub of int 
  |
    Mul of int 
  |
    Div of int 

and prog = cmd list

(*helper func*)
let integerParser = 
  natural <|>
  (
    satisfy (fun x -> x = '-') >>= fun _ ->
    natural >>= fun n ->
    pure (-1*n)
  )


(*helper func*)
let boolParser = 
  (
    literal "True" >>= fun _ ->
    pure (Bool true) 
  )
  <|>
  (
    literal "False" >>= fun _ ->
    pure (Bool false) 
  )

let push:cmd parser =
  many whitespace >>= fun _ ->
  literal "Push" >>= fun _ ->
  many whitespace >>= fun _ ->
  (integerParser >>= fun i ->
   many whitespace >>= fun _ -> 
   pure (Push (INT i)))
  <|>
  (
    boolParser >>= fun bl ->
    many whitespace >>= fun _ -> 
    pure (Push bl)
  )
  <|>
  (
    literal "()" >>= fun _ ->
    many whitespace >>= fun _ -> 
    pure (Push (Unit ()))
  )
    
  let pop:cmd parser =
    many whitespace >>= fun _ ->
    literal "Pop" >>= fun _ ->
    many1 whitespace >>= fun _ ->
    integerParser >>= fun i ->
    many whitespace >>= fun _ ->
    pure (Pop i)
  
  let add:cmd parser =
    many whitespace >>= fun _ ->
    literal "Add" >>= fun _ ->
    many1 whitespace >>= fun _ ->
    integerParser >>= fun i ->
    many whitespace >>= fun _ ->
    pure (Add i)
  
  let sub:cmd parser =
    many whitespace >>= fun _ ->
    literal "Sub" >>= fun _ ->
    many1 whitespace >>= fun _ ->
    integerParser >>= fun i ->
    many whitespace >>= fun _ ->
    pure (Sub i)
  
  let mul:cmd parser =
    many whitespace >>= fun _ ->
    literal "Mul" >>= fun _ ->
    many1 whitespace >>= fun _ ->
    integerParser >>= fun i ->
    many whitespace >>= fun _ ->
    pure (Mul i)
  
  let div:cmd parser =
    many whitespace >>= fun _ ->
    literal "Div" >>= fun _ ->
    many1 whitespace >>= fun _ ->
    integerParser >>= fun i ->
    many whitespace >>= fun _ ->
    pure (Div i)
  
  let trace:cmd parser =
    many whitespace >>= fun _ ->
    literal "Trace" >>= fun _ ->
    many1 whitespace >>= fun _ ->
    integerParser >>= fun i ->
    many whitespace >>= fun _ ->
    pure (Trace i)

let com_parser = push <|> pop <|> trace <|> add <|> sub <|> mul <|> div

let cmdsparser = many (com_parser)

let rec add_help (n:int) (inp: const list):(const list option) = 
  (*add 1 stack no change
    add 0 stack push 0
    add n stack no int return error
    n < 0 stack return error
    n > length stack return error**)
  if n < 0 || n > List.length(inp) then None
  else if n = 0 then Some(INT 0::inp)
  else match inp with
  h :: rest -> (match h with
                | INT x -> (
                  match add_help (n-1) rest with
                  Some(INT y::inp') -> Some(INT(x + y)::inp')
                  |
                  _ -> None
                )
                | _ -> None)
  |
  _ -> None

let rec pop_help (n:int) (inp: const list):(const list option) = 
  if n < 0 then None 
  else if n = 0 then Some inp
  else 
    (match inp with 
       stack ->
       (
         match stack with 
           h :: rest ->
           pop_help (n-1) (rest)
         |
           _ -> None
       ) )


let rec sub_help (n:int) (inp: const list):(const list option) = 
  (**
  sub 0 stack push 0
  sub n n negative or fewer than stacklength then error
  stack not integer then error*)
  if n < 0 || n > List.length(inp) then None
  else if n = 0 then Some(INT 0::inp)
  else match inp with
  h :: rest -> (match h with
                | INT x -> (
                  match add_help (n-1) rest with
                  Some(INT y::inp') -> Some(INT(x - y)::inp')
                  |
                  _ -> None
                )
                | _ -> None)
  |
  _ -> None


let rec mul_help (n:int) (inp: const list):( const list option) =
  (**
  mul 0 push 1 to the stack
  mul n n negative or fewer than stacklength then error
  stack not integer then error*) 
  if n < 0 || n > List.length(inp) then None
  else if n = 0 then Some(INT 1::inp)
  else match inp with
  h :: rest -> (match h with
                | INT x -> (
                  match mul_help (n-1) rest with
                  Some(INT y::inp') -> Some(INT(x * y)::inp')
                  |
                  _ -> None
                )
                | _ -> None)
  |
  _ -> None

let rec div_help (n:int) (inp: const list):((const list) option) = 
  (**
  div same as sub
  div n n negtive or fewer then error
  div 0 push 1 to stack
  stack not integer then error
  product of next n-1 are 0 then error*)
  if n < 0 || n > List.length(inp) then None
  else if n = 0 then Some(INT 1::inp)
  else match inp with
  h :: rest -> (match h with
                | INT x -> (
                  match mul_help (n-1) rest with
                  Some(INT y::inp') -> if y = 0 then None else Some(INT(x / y)::inp')
                  |
                  _ -> None
                )
                | _ -> None)
  |
  _ -> None


let rec trace_help (n:int) (stack:const list):((string list * const list) option) = 
      if n < 0 then None
      else if n = 0 then Some ([],stack)
      else
        match stack with 
            |h::rest ->(
                match trace_help (n-1) rest with 
                | Some(log,stack) -> (match h with
                                     | INT i -> Some((string_of_int i::log),stack)
                                     | Bool true -> Some(("True"::log),stack)
                                     | Bool false -> Some(("False"::log),stack)
                                     | Unit () -> Some(("()"::log),stack)
                )
                | None -> None)
            |_ -> None


(*
   eval [Push (INT 7);Push (INT 1)] [] [];;
   eval [Push (INT 7);Push (INT 1); Add 2] [] [];;
   eval [Push (INT 7);Push (INT 1); Push (INT 3); Add 3] [] [];;
   eval [Push (INT 5);Push (INT 7);Pop 2;Push (INT 3); Pop 2] [] [];;
   eval [Push (INT 5); Add 0] [] [];;
   eval [Push (INT 5);Push (INT 7);Push (INT 3);Pop 2] [] [];;
   *)


let rec eval cmds stack log = 
  match cmds with 
    Push v :: cmdss -> (
      (match v with
           |INT i -> eval cmdss (INT i::stack) log
           |Bool b -> eval cmdss (Bool b::stack) log
           |Unit () -> eval cmdss (Unit()::stack) log 
           ) (*miss the case when v is not a const*)
    )
  |
    Pop v ::cmdss -> (
      match pop_help v stack with 
      | Some stack1 -> eval cmdss stack1 log
      | None -> (None,log)
    )
  |
    Trace v::cmdss -> (
      match trace_help v stack with 
      |Some (log' , stack1) -> eval cmdss stack1 (List.append (List.rev log') log)
      |_ -> (None,log)
      )
  |
    Add n:: cmdss -> (
      match add_help n stack with 
      |Some stack1 -> eval cmdss stack1 log
      |None -> (None,log)
      )
  |
    Sub v::cmdss -> (
      match sub_help v stack with 
      |Some stack1 -> eval cmdss stack1 log
      |None -> (None,log)
      )
  |
    Mul v::cmdss ->(
      match mul_help v stack with 
      |Some stack1 -> eval cmdss stack1 log
      |None -> (None,log)
      )
  |
    Div v::cmdss ->(
      match div_help v stack with 
      |Some stack1 -> eval cmdss stack1 log
      |None -> (None,log)
      )
  |
    _ -> (Some stack, log)


(* TODO *)
let interp (src : string) : string list = 
  match parse (cmdsparser) src with
  | Some (cmds, []) -> (
      match eval cmds [] [] with
      | (Some stack,log) -> log
      | (None,_) -> [ "Error" ])
  | _ -> [ "Error" ]
(* Calling (main "test.txt") will read the file test.txt and run interp on it.
   This is only used for debugging and will not be used by the gradescope autograder. *)
let main fname =
  let src = readlines fname in
  interp src

