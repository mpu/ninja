type token = string and id = string
type sym = T of token | N of id
type rule =
  { id: id; rhs: sym list list
  ; mutable nullable: bool
  ; mutable first: id list }

let eof: token = ""


(* Tools *)

let rec union l1 l2 =
  (* union of two sorted lists *)
  match l1, l2 with
  | a1 :: l1', a2 :: l2' ->
    let c = compare a1 a2 in
    if c = 0 then a1 :: union l1' l2'
    else if c < 0 then a1 :: union l1' l2
    else a2 :: union l1 l2'
  | _, [] -> l1
  | [], _ -> l2


module Gram = struct
  (* A grammar is a set of rules *)
  include Map.Make(String)

  let add ({id;_} as rl) gr = add id rl gr

  let find id gr =
    try find id gr
    with Not_found ->
      Printf.eprintf "oops: %s\n" id;
      raise Not_found

  let rhs id gr = (find id gr).rhs
  let nullable id gr = (find id gr).nullable
  let first id gr = (find id gr).first

  let init gr =
    (* initialize nullable and first fields *)
    let m = ref true in
    while !m = true do
      m := false;
      iter
        begin fun _ r ->
          let rec f = function
            | N y :: syms ->
              let r' = find y gr in
              if r'.nullable then f syms else begin
                let o = r.first in
                r.first <- union r.first r'.first;
                m := !m || r.first <> o
              end
            | T tok :: _ ->
              let o = r.first in
              r.first <- union r.first [ tok ];
              m := !m || r.first <> o
            | [] ->
              m := !m || r.nullable <> true;
              r.nullable <- true
          in List.iter f r.rhs
        end gr
    done

end






(* LR1 terms *)

type term =
  { rule: id
  ; prod: int (* index of the production in rhs *)
  ; dot: int (* position of the dot *)
  ; look: token (* lookahead token *)
  }

let rec first stnc gr =
  match stnc with
  | N id :: stnc ->
    if Gram.nullable id gr
      then union (Gram.first id gr) (first stnc gr)
      else Gram.first id gr
  | T tok :: _ -> [ tok ]
  | [] -> []

let dot t gr =
  (* get the symbol string right after the term dot *)
  let rec drop l n = if n = 0 then l else drop (List.tl l) (n-1) in
  let prod = List.nth (Gram.rhs t.rule gr) t.prod in
  drop prod t.dot

module LRState = Set.Make(struct
  (* Module for sets of terms *)
  type t = term
  let compare = compare
end)

let rec closure s gr =
  (* compute the closure of a set [s] of LR1 terms *)
  let s' = LRState.fold
    begin fun t s ->
      match dot t gr with
      | N b :: stnc ->
        let fstl = first (stnc @ [ T t.look ]) gr in
        let rec prodloop pid s = function
          | prod :: tl ->
            let s = List.fold_left
              (fun s fst -> LRState.add
                {rule=b; prod=pid; dot=0; look=fst} s)
              s fstl in
            prodloop (pid+1) s tl
          | [] -> s in
        prodloop 0 s (Gram.rhs b gr)
      | _ -> s
    end s s in
  if LRState.equal s' s (* test for fixpoint *)
    then s
    else closure s' gr

let goto s sym gr =
  (* compute the state after seeing [sym] in state [s] *)
  let s' = LRState.fold
    begin fun t s' ->
      match dot t gr with
      | sym' :: _ when sym' = sym ->
        LRState.add {t with dot = t.dot+1} s'
      | _ -> s'
    end s LRState.empty in
  closure s' gr

module C = struct
  (* Module for set of LRStates *)
  type nstate = {num: int; state: LRState.t}
  include Set.Make(struct
    type t = nstate
    let compare a b =
      LRState.compare a.state b.state
  end)
  let singleton s = singleton {num=0; state=s}
  let add s c = add {num=cardinal c; state=s} c
  let num s c = (find {num=0; state=s} c).num
end

let items toks gr =
  (* Generate all states *)
  let gsyms = (* all possible grammar symbols *)
    (List.map (fun (id, _) -> N id) (Gram.bindings gr)) @
    (List.map (fun t -> T t) toks) in
  let rec fix c =
    let c' = C.fold
      begin fun s c ->
        List.fold_left
          (fun c sym -> C.add (goto s.C.state sym gr) c)
          c gsyms
      end c c in
    if C.equal c' c
      then c
      else fix c' in
  let start =
    LRState.singleton {rule="#"; prod=0; dot=0; look=eof} in
  fix (C.singleton (closure start gr))


(* Pretty printing *)

let pp_state oc s gr =
  let open Printf in
  LRState.iter begin fun t ->
    let rec pprhs dot = function
      | T x :: stnc | N x :: stnc ->
        if dot = 0 then fprintf oc ". ";
        fprintf oc "%s " x; pprhs (dot-1) stnc
      | [] ->
        if dot = 0 then fprintf oc ". ";
        fprintf oc "    [lookahead = %S]\n" t.look in
    fprintf oc "%s -> " t.rule;
    pprhs t.dot (List.nth (Gram.rhs t.rule gr) t.prod)
  end s


(* Tables generation *)

type action =
  | Shift of int (* shift in a new state *)
  | Reduce of (id * int) (* reduce by a rule *)
  | Accept (* parse success *)
  | Error (* parse error *)

let mktables toks gr =
  let c = items toks gr in
  let ns = C.cardinal c in
  let nt = List.length toks in
  let toknum t =
    let rec f i = function
      | t' :: _ when t' = t -> i
      | _ :: tl -> f (i+1) tl
      | [] -> failwith "toknum" in
    f 0 toks in
  let (nn, nmap) = Gram.fold
    (fun id _ (nn, nmap) -> (nn+1, (id,nn) :: nmap))
    gr (0, []) in
  let gtbl = Array.init ns (fun _ -> Array.make nn 0) in
  let atbl = Array.init ns (fun _ -> Array.make nt Error) in
  C.iter begin fun {C.num; state} ->

    (* fill the goto table *)
    List.iter
      (fun (nid, n) ->
        gtbl.(num).(n) <- C.num (goto state (N nid) gr) c)
      nmap;

    (* fill the action table *)
    let seta nt act =
      let act' = atbl.(num).(nt) in
      if act' <> act && act' <> Error && act' <> Accept then begin
        let ptyp = function
          | Shift _ -> "shift" | Reduce _ -> "reduce" | _ -> "??" in
        pp_state stderr state gr;
        failwith (ptyp atbl.(num).(nt) ^ "/" ^ ptyp act ^ " conflict")
      end else if act' <> Accept then
        atbl.(num).(nt) <- act in

    LRState.iter begin fun t ->
        if t.rule = "#" && t.dot = 1 then (* accept action *)
          seta (toknum eof) Accept;
        match dot t gr with
        | T tok :: _ -> (* shift action *)
          seta (toknum tok) (Shift (C.num (goto state (T tok) gr) c))
        | [] -> (* reduce action *)
          seta (toknum t.look) (Reduce (t.rule, t.prod))
        | _ -> ()
    end state;
  end c;
  (gtbl, atbl, nmap)

let outtables gtbl atbl nm gr =
  let open Printf in
  let ns = Array.length gtbl in
  let nn = Array.length gtbl.(0) in
  let nt = Array.length atbl.(0) in
  printf "let n_states = %d\n" ns;
  printf "let n_goto =\n[|\n";
  for i=0 to ns-1 do
    printf "  [|";
    for j=0 to nn-1 do
      printf "%d%s" gtbl.(i).(j) (if j<>nn-1 then ";" else "")
    done;
    printf "|]%s\n" (if i<>ns-1 then ";" else "")
  done;
  let pact = function
    | Shift n -> printf "S %d" n
    | Reduce (id, n) -> printf "R (%S,%d)" id n
    | Accept -> printf "A"
    | Error -> printf "E" in
  printf "|]\nlet n_act = \n[|\n";
  for i=0 to ns-1 do
    printf "  [|";
    for j=0 to nt-1 do
      pact atbl.(i).(j); if j<>nt-1 then printf ";"
    done;
    printf "|]%s\n" (if i<>ns-1 then ";" else "")
  done;
  printf "|]\nlet n_nmap = [";
  let rec p = function
    | (nid, n) :: tl ->
      printf "(%S,%d)%s" nid n
        (if tl = [] then "" else ",");
      p tl
    | [] -> () in
  p nm; printf "]\n"

let _ =
  let mk (id, rhs) = {id; rhs; nullable=false; first=[]} in
  let toks = ["Num";"+";"-";"(";")";"*";eof] in
  let gr =
    (Gram.add (mk ("A", [[N"M"]; [N"A"; T"+"; N"M"]; [N"A"; T"-"; N"M"]]))
    (Gram.add (mk ("M", [[N"B"]; [N"M"; T"*"; N"B"]]))
    (Gram.add (mk ("B", [[T"Num"]; [T"("; N"A"; T")"]]))
    (Gram.add (mk ("#", [[N"A"]]))
     Gram.empty)))) in

  Gram.init gr;
  let start =
    LRState.singleton {rule="#"; prod=0; dot=0; look=eof} in
  if true then begin
    pp_state stdout (closure start gr) gr;
    print_string "------------\n"
  end;
  let fin = (goto (closure start gr) (T"Num") gr) in
  pp_state stdout fin gr;
  print_string "------------\n";
  let c = items toks gr in
  Printf.printf "%d elements in table (final num = %d)\n" (C.cardinal c) (C.num fin c);
  print_string "------------\n\n";
  let _g, _a, _nm =  mktables toks gr in
  outtables _g _a _nm gr;
  ()
