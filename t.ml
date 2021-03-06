
(* ****************** *)
(* prelude *)

type n_act = S of int | R of string * int | A | E

(* ****************** *)
(* generated by ninja.ml *)

let n_states = 27
let n_goto =
[|
  [|1;2;3;4|];
  [|1;1;1;1|];
  [|1;1;1;1|];
  [|1;1;1;1|];
  [|1;1;1;1|];
  [|1;1;1;1|];
  [|1;9;10;11|];
  [|1;1;3;20|];
  [|1;1;3;21|];
  [|1;1;1;1|];
  [|1;1;1;1|];
  [|1;1;1;1|];
  [|1;1;1;1|];
  [|1;15;10;11|];
  [|1;1;22;1|];
  [|1;1;1;1|];
  [|1;1;26;1|];
  [|1;1;10;24|];
  [|1;1;10;25|];
  [|1;1;1;1|];
  [|1;1;1;1|];
  [|1;1;1;1|];
  [|1;1;1;1|];
  [|1;1;1;1|];
  [|1;1;1;1|];
  [|1;1;1;1|];
  [|1;1;1;1|]
|]
let n_act =
[|
  [|S 5;E;E;S 6;E;E;E|];
  [|E;E;E;E;E;E;E|];
  [|E;S 7;S 8;E;E;E;A|];
  [|E;R ("M",0);R ("M",0);E;E;R ("M",0);R ("M",0)|];
  [|E;R ("A",0);R ("A",0);E;E;S 14;R ("A",0)|];
  [|E;R ("B",0);R ("B",0);E;E;R ("B",0);R ("B",0)|];
  [|S 12;E;E;S 13;E;E;E|];
  [|S 5;E;E;S 6;E;E;E|];
  [|S 5;E;E;S 6;E;E;E|];
  [|E;S 17;S 18;E;S 19;E;E|];
  [|E;R ("M",0);R ("M",0);E;R ("M",0);R ("M",0);E|];
  [|E;R ("A",0);R ("A",0);E;R ("A",0);S 16;E|];
  [|E;R ("B",0);R ("B",0);E;R ("B",0);R ("B",0);E|];
  [|S 12;E;E;S 13;E;E;E|];
  [|S 5;E;E;S 6;E;E;E|];
  [|E;S 17;S 18;E;S 23;E;E|];
  [|S 12;E;E;S 13;E;E;E|];
  [|S 12;E;E;S 13;E;E;E|];
  [|S 12;E;E;S 13;E;E;E|];
  [|E;R ("B",1);R ("B",1);E;E;R ("B",1);R ("B",1)|];
  [|E;R ("A",1);R ("A",1);E;E;S 14;R ("A",1)|];
  [|E;R ("A",2);R ("A",2);E;E;S 14;R ("A",2)|];
  [|E;R ("M",1);R ("M",1);E;E;R ("M",1);R ("M",1)|];
  [|E;R ("B",1);R ("B",1);E;R ("B",1);R ("B",1);E|];
  [|E;R ("A",1);R ("A",1);E;R ("A",1);S 16;E|];
  [|E;R ("A",2);R ("A",2);E;R ("A",2);S 16;E|];
  [|E;R ("M",1);R ("M",1);E;R ("M",1);R ("M",1);E|]
|]
let n_nmap = [("M",3);("B",2);("A",1);("#",0)]


(* ****************** *)
(* hand written, but shoud be generated *)

type n_state =
  { n_sid: int
  ; n_obj: Obj.t }

let n_nstk = 100

let n_stk =
  Array.make n_nstk
    {n_sid=0; n_obj=Obj.repr 0}
and n_stkp = ref 0

let n_push sid obj =
  n_stk.(!n_stkp) <- {n_sid=sid; n_obj=obj};
  incr n_stkp

let n_pop () =
  decr n_stkp;
  Obj.magic (n_stk.(!n_stkp).n_obj)

let n_actions =

[ ("A",
    [ (fun () ->
        print_string "A -> M\n";
        (n_pop (): int))
    ; (fun () ->
        let i2 = (n_pop (): int) in
        let _ = n_pop () in
        let i1 = (n_pop (): int) in
        print_string "A -> A + M\n";
        i1 + i2
      )
    ; (fun () ->
        let i2 = (n_pop (): int) in
        let _ = n_pop () in
        let i1 = (n_pop (): int) in
        print_string "A -> A - M\n";
        i1 - i2
      )
    ])

; ("M",
    [ (fun () ->
        print_string "M -> B\n";
        (n_pop (): int))
    ; (fun () ->
        let i2 = (n_pop (): int) in
        let _ = n_pop () in
        let i1 = (n_pop (): int) in
        print_string "M -> M * B\n";
        i1 * i2
      )
    ])

; ("B",
    [ (fun () ->
        let i = n_pop () in
        print_string "B -> Num\n";
        i
      )
    ; (fun () ->
        let _ = n_pop () in
        let i = (n_pop (): int) in
        let _ = n_pop () in
        print_string "B -> ( A )\n";
        i
      )
    ])

]

type toks =
  | TNum of int
  | TPlus
  | TMinus
  | TLParen
  | TRParen
  | TMult
  | TEof

let n_toknum = function
  | TNum _ -> 0
  | TPlus -> 1
  | TMinus -> 2
  | TLParen -> 3
  | TRParen -> 4
  | TMult -> 5
  | TEof -> 6


exception ParseError

let n_parse lex =

  let open Printf in

  (* main parsing loop *)
  let rec loop st a =
    match n_act.(st).(n_toknum a) with
    | E -> raise ParseError
    | A -> n_pop ()
    | S st' ->
      let tobj = Obj.repr a in
      if Obj.is_block tobj then
        n_push st' (Obj.field tobj 0)
      else
        n_push st' (Obj.repr 0);
      (* printf "shift in %d\n" st'; *)
      loop st' (lex ())
    | R (rule,n) ->
      let act =
        List.nth
          (List.assoc rule n_actions)
          n in
      let res = act () in
      let st' = n_stk.(!n_stkp-1).n_sid in
      (* printf "reduce from %d back to %d\n" st st'; *)
      let st'' = n_goto.(st').(List.assoc rule n_nmap) in
      (* printf "goto %d\n" st''; *)
      n_push st'' (Obj.repr res);
      loop st'' a

  in n_push 0 (Obj.repr 0); loop 0 (lex ())


(* ****************** *)
(* hand written for good, or generated using lex *)

let next, refeed =
  (* buffered input *)
  let buf = ref None in
  (fun () ->
    match !buf with
    | None -> (try input_char stdin with End_of_file -> '\x00')
    | Some c -> buf := None; c),
  (fun c -> buf := Some c)

let rec lex () =

  let digit c = Char.code c - Char.code '0' in
  let rec pnum n =
    match next () with
    | '0'..'9' as c -> pnum (digit c + 10*n)
    | c -> refeed c; n in

  match next () with
  | '0'..'9' as c -> TNum (pnum (digit c))
  | '+' -> TPlus
  | '-' -> TMinus
  | '(' -> TLParen
  | ')' -> TRParen
  | '*' -> TMult
  | '\x00' -> TEof
  | ' ' | '\t' | '\n' -> lex ()
  | _ -> failwith "lex error"


(* main program *)
let _ =
  let n = n_parse lex in
  Printf.printf "result: %d\n" n
