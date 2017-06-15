(** The state of a program during execution *)

open Util

type state =
    {
      (* Actual state data *)
      st : stack;
      hp : heap;

      (* Maximum addr allocated in this heap *)
      hp_size : int64;
    }
 and stack = (string, valu) Hashtbl.t
 (** allowed heap positions are 1, 2 .. hp_size *)
 and heap = ((int64 * string), valu) Hashtbl.t
 and valu =
   | ValAddr of int64
   | ValInt of int64
(* | ValBool of bool *)
(* and address = NullAddr | Addr of int *)


(** Unwrapping valu-s *)
let get_valaddr = function
  | ValAddr a -> a
  | _ -> failwith "get_valaddr called on valu that's not a ValAddr."

let get_valint = function
  | ValInt i -> i
  | _ -> failwith "get_valint called on valu that's not a ValInt."


(** Methods to create states *)
let start_state () =
  {
    st = Hashtbl.create 0;
    hp = Hashtbl.create 0;
    hp_size = 0L;
  }

let clone_state state =
  {
    st = Hashtbl.copy state.st;
    hp = Hashtbl.copy state.hp;
    hp_size = state.hp_size
  }

(** Get/Set methods for state *)
let get_stack_value state varname =
  try Hashtbl.find state.st varname
  with
    Not_found ->
    if varname = "null" then ValAddr 0L
    else failwith (varname ^ " is not on the stack.")

let set_stack_value state varname value =
  Hashtbl.replace state.st varname value;
  state

let has_stack_value state varname =
  Hashtbl.mem state.st varname

let new_heap_value state =
  ValAddr (Int64.add state.hp_size 1L), {state with hp_size = Int64.add state.hp_size 1L}

let get_heap_value state (addr, fname) =
  let addr = get_valaddr addr in
  if (Int64.compare addr state.hp_size) > 0 || (Int64.compare addr 1L) < 0 then
    failwith ("get_heap_value: called on invalid address " ^ (Int64.to_string addr) ^  ".")
  else
    Hashtbl.find state.hp (addr, fname)

let get_addr_field_values state addr =
  Hashtbl.fold
    (fun (source_addr, field_name) field_value acc ->
      match field_value with
      | ValAddr target_addr when source_addr = addr && not(Util.str_ends_with field_name "parent") -> target_addr :: acc
      | _ -> acc)
    state.hp []
                 
let set_heap_value state (addr, fname) value =
  if (Int64.compare addr state.hp_size) > 0 || (Int64.compare addr 1L) < 0 then
    failwith ("set_heap_value: called on invalid address " ^ (Int64.to_string addr) ^  ".")
  else
    Hashtbl.replace state.hp (addr, fname) value;
  state

let get_varnames_in_stack state =
  Hashtbl.fold (fun varname _ nameset -> StringSet.add varname nameset)
	       state.st StringSet.empty


(** Pretty printers for state *)
let string_of_valu = function
  | ValAddr addr -> "ValAddr " ^ Int64.to_string addr
  | ValInt i -> "ValInt " ^ Int64.to_string i
(* | ValBool b -> "ValBool " ^ string_of_bool b *)

let string_of_stack st =
  Hashtbl.fold
    (fun varname value out_str ->
     out_str ^ "\n    " ^ varname ^ " -> " ^ (string_of_valu value))
    st "  Stack:"

let string_of_heap hp =
  (* Print heap, ordered by address (i.e. grouping fields for one address) *)
  let sortedHeapEntries =
    Hashtbl.fold (fun k v r -> (k,v)::r) hp []
    |> List.sort (fun ((a1, f1), _) ((a2, f2), _) -> let r = compare a1 a2 in if r = 0 then compare f1 f2 else r) in
  List.fold_left
    (fun out_str ((addr, fname), value) ->
     out_str ^ "\n    " ^ (Int64.to_string addr) ^ "." ^ fname ^ " -> " ^ (string_of_valu value))
    "  Heap:"
    sortedHeapEntries

let string_of_state state =
  "State:\n" ^ (string_of_stack state.st)
  ^ "\n" ^ (string_of_heap state.hp)
  ^ "\n  hp_size = " ^ (Int64.to_string state.hp_size)


(** Util functions for values *)
let int_of_bool = function
  | true -> 1L
  | false -> 0L

let bool_of_int = function
  | 0L -> false
  | _ -> true

(** Random valu used to initialize stack variables *)
let rand_val_int () = ValInt (Int64.of_int ((Random.int 1000) - 500))
let rand_val_bool () = ValInt (int_of_bool (Random.bool ()))


(** Project stack to a StringSet of variable names *)
let restrict_stack_to_names state names =
  let re = Str.regexp_string "!ret-value!" in
  Hashtbl.iter
    (fun name _ ->
     if not (StringSet.mem name names) &&
	  (try ignore (Str.search_forward re name 0); false
	   with Not_found -> true)
     then Hashtbl.remove state.st name)
    state.st;
  state


(** Project the heap to only location reachable from the stack *)
let restrict_heap_to_reachables state =
  let reachable_locs = Hashtbl.create 0 in
  let rec mark_reachable loc =
    if loc <> 0L && (not (Hashtbl.mem reachable_locs loc)) then
      begin
	Hashtbl.add reachable_locs loc true;
        List.iter mark_reachable (get_addr_field_values state loc)
      end
  in
  Hashtbl.iter
    (fun _ valu ->
     match valu with
     | ValAddr addr -> mark_reachable addr
     | _ -> ()
    )
    state.st;
  Hashtbl.iter
    (fun (addr, fname) _ ->
     if not (Hashtbl.mem reachable_locs addr) then
       Hashtbl.remove state.hp (addr, fname)
    )
    state.hp;
  state
