open Unix

module IntSet = Set.Make(struct
    type t = int
    let compare = compare
  end)

module IntMap = Map.Make(struct
    type t = int
    let compare = compare
  end)

module Int64Set = Set.Make(struct
    type t = Int64.t
    let compare = Int64.compare
end)
                        
module StringSet = Set.Make(struct
    type t = string
    let compare = compare
  end)

module StringMap = Map.Make(struct
    type t = string
    let compare = compare
  end)

(** Utility functions on option types *)

module Opt = struct
  let to_list = function
    | Some x -> [x]
    | None -> []

  let get = function
    | Some x -> x
    | None -> failwith "Util.unopt applied to None"

  let get_or_else default = function
    | Some x -> x
    | None -> default

  let fold f init = function
    | Some x -> f init x
    | None -> init

  let map f = function
    | Some x -> Some (f x)
    | None -> None

  let iter f = function
    | Some x -> f x
    | None -> ()

  let some x = function
    | None -> Some x
    | o -> o
end

(** Utility functions on lists *)

(** generate a list of length [n] using generator [f] *)
let generate_list (f : int -> 'a) (n : int) : 'a list = 
  let rec mk_tl n acc = 
    if n <= 0 then acc 
    else mk_tl (n - 1) (f (n - 1) :: acc) 
  in mk_tl n []


(** Composition of [List.map] and [List.filter] *)
let filter_map p f xs =
  List.fold_right (fun x ys -> if p x then f x :: ys else ys) xs []

(** Composition of [List.filter] and [List.rev_map] *)
let filter_rev_map p f xs =
  List.fold_left (fun ys x -> if p x then f x :: ys else ys) [] xs

    
(** Composition of [List.map] and [List.partition] *)
let partition_map p f xs =
  List.fold_right (fun x (ys1, ys2) -> if p x then (f x :: ys1, ys2) else (ys1, f x :: ys2)) xs ([], [])

(** Composition of [List.split] and [List.map] *)
let map_split f xs =
  List.fold_right (fun x (ys, zs) -> let y, z = f x in y :: ys, z :: zs) xs ([], [])

(** Composition of [List.fold_left] and [List.map] *)
let fold_left_map f acc xs =
  let rec process acc lst = match lst with
    | x :: xs ->
      let y, acc2 = f acc x in
      let ys, acc3 = process acc2 xs in
      (y::ys, acc3)
    | [] -> ([], acc)
  in
    process acc xs

(** Applies [fn] to the elements in [xs] until the result becomes Some _ *)
let rec find_map fn = function
  | [] -> None
  | x :: xs ->
      match fn x with
      | None -> find_map fn xs
      | v -> v

let flat_map f ls = List.flatten (List.map f ls)

let flat_mapi f ls = List.flatten (List.mapi f ls)

let find_index elt ls =
  let rec traverse i lst = match lst with
    | x :: xs when elt = x -> i
    | _ :: xs -> traverse (i+1) xs
    | [] -> raise Not_found
  in
  traverse 0 ls

(* find an element x s.t. p(x) and check that the other elements do not satisfy p.
 * raise Not_found / Failure "not unique"
 *)
let find_unique p xs =
  let canditates = List.filter p xs in
    match canditates with
    | [x] -> x
    | [] -> raise Not_found
    | _ -> raise (Failure "not unique")

let rec partial_map f = function
  | [] -> []
  | x :: xs -> 
      match f x with 
      |	Some y -> y :: partial_map f xs
      |	None -> partial_map f xs

(** Like List.map2 but additionally returns the remainder of the two lists *)
let map2_remainder fn xs ys =
  let rec m xs ys zs =
  match xs, ys with
  | [], _ 
  | _, [] -> List.rev zs, xs, ys
  | x :: xs1, y :: ys1 -> 
      m xs1 ys1 (fn x y :: zs)
  in
  m xs ys []

(** Like List.map2 but ignores the tail of the longer list instead of throwing an exception *)
let map2 fn xs ys =
  let zs, _, _ = map2_remainder fn xs ys in
  zs

(** Like List.fold_left2 but ignores the tail of the longer list instead of throwing an exception *)
let rec fold_left2 fn init xs ys =
  match xs, ys with
  | [], _ 
  | _, [] -> init
  | x :: xs1, y :: ys1 -> fold_left2 fn (fn init x y) xs1 ys1

(** Like List.fold_left2 but ignores the tail of the longer list instead of throwing an exception *)
let rec for_all2 fn xs ys =
  match xs, ys with
  | [], [] -> true
  | [], _ 
  | _, [] -> false
  | x :: xs1, y :: ys1 -> 
      fn x y && for_all2 fn xs1 ys1


(** Tail-recursive concatenation of lists *)
let rev_concat lists = List.fold_left (List.fold_left (fun acc f -> f :: acc)) [] lists

let iteri fct lst =
  let rec iter idx lst =
    match lst with
    | x::xs -> fct idx x; iter (idx+1) xs
    | [] -> ()
  in
  iter 0 lst

(** Print a list with a given separator *)
let output_list chan fn sep xs =
  match xs with
  | [one] -> fn one
  | first :: rest -> 
      fn first; List.iter (fun x -> output_string chan sep; fn x) rest
  | [] -> ()
        
(** Boolean operators on predicates *)

let (~~) f x = not (f x)

let (&&&) f g x = f x && g x

let (|||) f g x = f x || g x


(** Helper function for strings - returns true if the first string starts with the second string *)
let string_starts_with s t =
  let s_len = String.length s
  and t_len = String.length t
  in if (s_len>=t_len) && ((String.sub s 0 t_len)=t) then true
    else false

(* the following is stripped from module BatSubstring in OCaml Batteries included *)

type t = string * int * int (* string, offset, length *)

let empty () = "", 0, 0

let to_string (s,o,l) = String.sub s o l

let of_string s = s, 0, String.length s

let splitl p (str, off, len) = 
  let i = ref 0 in
  while !i < len && p str.[off+ !i] do incr i; done;
  (str, off+ !i, len- !i), (str, off, !i)

let split_on_char c (str, off, len) = 
  let rec loop acc last_pos pos =
    if pos = -1 then
      (str, 0, last_pos) :: acc
    else
      if str.[pos] = c then
        let pos1 = pos + 1 in
        let sub_str = str,pos1,(last_pos - pos1) in
        loop (sub_str :: acc) pos (pos - 1)
      else loop acc last_pos (pos - 1)
  in
  loop [] len (len - 1)

let split_on_comma str = split_on_char ',' str;;

let measured_time = ref 0.
let measured_calls = ref 0

(** measure accumulated execution time and number of calls to a particular function *)
let measure fn arg =
  let start_time = 
    let ptime = Unix.times () in
    ptime.tms_utime
  in
  try
    let res = fn arg in
    let end_time = 
      let ptime = Unix.times () in
      ptime.Unix.tms_utime
    in
    measured_time := !measured_time +. (end_time -. start_time);
    incr measured_calls;
    res
  with e ->
    let end_time = 
      let ptime = Unix.times () in
      ptime.Unix.tms_utime
    in
    measured_time := !measured_time +. (end_time -. start_time);
    incr measured_calls;
    raise e

let measures = Hashtbl.create 10

let measure_call (id: string) fn arg =
  let get_time () = 
    let ptime = Unix.times () in
    ptime.tms_utime
  in
  let (calls, time) =
    if Hashtbl.mem measures id
    then Hashtbl.find measures id
    else (0, 0.)
  in
  let start_time = get_time () in
  try
    let res = fn arg in
    let end_time = get_time () in
    Hashtbl.replace measures id (calls + 1, time +. end_time -. start_time);
    res
  with e ->
    let end_time = get_time () in
    Hashtbl.replace measures id (calls + 1, time +. end_time -. start_time);
    raise e

let print_measures () =
  Hashtbl.iter
    (fun id (calls, time) ->
      print_endline (id ^ ": " ^ (string_of_int calls) ^ " call(s), " ^ (string_of_float time) ^ " s")
    )
    measures

let read_file file =
  let chan = open_in file in
  let rec read acc =
    let line =
      try
        Some (input_line chan)
      with End_of_file ->
        close_in chan;
        None
    in
    match line with
    | Some l -> read (l :: acc)
    | None -> List.rev acc
  in
  String.concat "\n" (read [])

let rec remove_duplicates lst = match lst with
  | x :: xs -> x :: remove_duplicates (List.filter (fun y -> y <> x) xs)
  | [] -> []

(* Checks if s1 ends with string s2 *)
let str_ends_with s1 s2 =
  let (l1, l2) = (String.length s1, String.length s2) in
  if (l1 >= l2) then
    let s1End = String.sub s1 (l1 - l2) l2 in
    (String.compare s1End s2) = 0
  else
    false

let listTblAddFirst (t : ('a, 'b list) Hashtbl.t) (key : 'a) (value : 'b) =
  try
    let oldValues = Hashtbl.find t key in
    Hashtbl.replace t key (value :: oldValues)
  with Not_found ->
    Hashtbl.add t key [value]
		
let listTblAddLast (t : ('a, 'b list) Hashtbl.t) (key : 'a) (value : 'b) =
  try
    let oldValues = Hashtbl.find t key in
    Hashtbl.replace t key (oldValues @ [value])
  with Not_found ->
    Hashtbl.add t key [value]

(** Append two ('a, 'b list) hashtables t1, t2. 
    Note: This mutates t1.
    We define t.find k = [] for keys k that do not occur in t.
    Let t1' be the original value of t1. Then the result of listTblAppend is that
    Hashtbl.find t1 k = (Hashtbl.find t1 k) @ (Hashtbl.find t2 k)
    Note: Does not modify t2. *)
let listTblAppend (t1 : ('a, 'b list) Hashtbl.t) (t2 : ('a, 'b list) Hashtbl.t) =
  Hashtbl.iter
    (fun key values2 ->
     try
       let oldValues1 = Hashtbl.find t1 key in
       Hashtbl.replace t1 key (oldValues1 @ values2)
     with Not_found ->
       Hashtbl.add t1 key values2)
    t2

let remove_duplicates l =
  let remove_elt e l =
    let rec go l acc = match l with
      | [] -> List.rev acc
      | x::xs when e = x -> go xs acc
      | x::xs -> go xs (x::acc)
    in go l []
  in
  let rec go l acc = match l with
    | [] -> List.rev acc
    | x :: xs -> go (remove_elt x xs) (x::acc)
  in go l []

let rec expand f xs ys =
  match xs with
  | [] -> ys
  | x::xs ->
     let (xs',ys') = f x in
     expand f (List.rev_append xs' xs) (List.rev_append ys' ys)

let extract k list =
  let rec aux k acc emit = function
    | [] -> acc
    | h :: t ->
       if k = 1 then aux k (emit [h] acc) emit t else
         let new_emit x = emit (h :: x) in
         aux k (aux (k-1) acc new_emit t) emit t
  in
  let emit x acc = x :: acc in
  aux k [] emit list

let pairs list =
  let rec loop acc = function
    | []
    | _ :: [] -> acc
    | x :: xs ->
       let newAcc = List.fold_left (fun res y -> (x,y)::res) acc xs in
       loop newAcc xs in
  loop [] list

let rec map_partial f = function
  | [] -> [] | x::xs ->
		(match f x with
		 | None -> map_partial f xs
		 | Some y -> y::(map_partial f xs))

let rec sublist b e l =
  match l with
    [] -> failwith "sublist"
  | h :: t ->
     let tail = if e=0 then [] else sublist (b-1) (e-1) t in
     if b>0 then tail else h :: tail

let remove_nth l indices =
  fst (List.fold_left (fun (l',index) li ->
		       if (List.exists (fun i -> i = index) indices)
		       then (l', index+1)
		       else (l'@[li], index+1)
		      ) ([],0) l)

let rec split3 = function
  | [] -> ([], [], [])
  | (x, y, z) :: rest ->
     let (rx, ry, rz) = split3 rest in
     (x :: rx, y :: ry, z :: rz)
