open Log
open Core.Std
open Printf

type t = {n_src: int; n_xor: int; n_prf: int}

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

let str_of_level l =
  let str_all = ref "" in
  let add_str (str, idx) =
    str_all := !str_all ^ " (" ^str ^","^ (Int.to_string idx) ^") " ;
    ();
  in
  List.iter l add_str;
  !str_all

let str_of_tuple_l l =
  let str_all = ref "" in
  let add_str (src, dst) =
    str_all := !str_all ^ " (" ^(Int.to_string src) ^","^ (Int.to_string dst) ^") " ;
    ();
  in
  List.iter l add_str;
  !str_all

let str_op_of_tuple_l l v =
  let str_all = ref "" in
  let add_str (src, dst) =
    str_all := !str_all ^ " (" ^v.(src)^(Int.to_string src) ^","^ v.(dst) ^ (Int.to_string dst) ^") " ;
    ();
  in
  List.iter l add_str;
  !str_all

let str_of_list l =
  let str_all = ref "[" in
  let add_str str =
    str_all := !str_all ^ " " ^ str;
    ();
  in
  List.iter l add_str;
  str_all := !str_all ^ " ]";
  !str_all

let str_of_list_list l =
  let str_all = ref "" in
  let add_str lst =
    str_all := !str_all ^ " " ^ (str_of_list lst);
    ();
  in
  List.iter l add_str;
  !str_all

let rec gen_list elem len =
  if len = 0 then
    []
  else
    elem :: (gen_list elem (len - 1))
                   
let permutations lst =
    let lstar = Array.of_list lst in
    let len = Array.length lstar in
    let ks = List.range 1 (len + 1) in
    let indices = Int.Set.of_list (List.range 0 len) in
    let choose k (v, indices, res) =
        let ix = Option.value_exn (Int.Set.find_index indices (v mod k)) in
        (v / k, Int.Set.remove indices ix, lstar.(ix) :: res)
    in
    let perm i =
        let (v, _, res) =
            List.fold_right ks ~f: choose ~init: (i, indices, [])
        in
        if v > 0 then None else Some res
    in
    Stream.from perm

(* place PRF on the edges *)
let add_PRF edge_l t =
    let rec add_PRF_inner acc idx l =
    match l with
    | [] -> acc
    | (src, dst) :: xs ->
       let acc_n = List.filter acc (fun x -> x <> (src, dst)) in
       add_PRF_inner ((src, idx) :: (idx, dst) :: acc_n) (idx + 1) xs;
  in
  List.map (extract t.n_prf edge_l) (fun e -> add_PRF_inner edge_l (2 * (t.n_src) + 2 * (t.n_xor)) e) 
  (* List.iter new_l (fun e -> Log.debug "%s" (str_of_tuple_l e)); *)
  (* Log.debug "%s" (str_of_tuple_l !edges_PRF); *)


(* difference beween two lists *)
let diff l1 l2 = List.filter l1 (fun x -> not (List.mem l2 x))

(* level_l, permutations ledges is for *)
(* TODO: extract 2, or permute hashtable to look up *)
let edge_all_list = ref[] 
(* aim to consume the ops at bottom level *)
(* out to the next level *)
let gen_edge_list level_l =

  let rec connect acc_e out top bot level_rest =
    let new_edge dst (_, src) =
      (src, dst);
    in

    let connect_XOR up_level dst left_l =
      let lst = extract 2 up_level in
      let connect_XOR_inner lst_e =
        let diff_l = diff up_level lst_e in
        let e_1 = new_edge dst (List.hd_exn lst_e) in
        let e_2 = new_edge dst (List.hd_exn(List.tl_exn lst_e)) in
        connect (e_1 :: e_2 :: acc_e) (("XOR", dst) :: out) diff_l left_l level_rest;
      in
      List.iter lst connect_XOR_inner;
    in

    let connect_DUP up_level dst left_l =
      let connect_DUP_inner lst_e =
        let diff_l = diff up_level [lst_e] in
        let e = new_edge dst lst_e in
        connect (e :: acc_e) (("DUP1", dst)::("DUP2", dst) :: out)
                diff_l left_l level_rest;
      in
      List.iter up_level connect_DUP_inner
    in

    let connect_OUT up_level dst left_l =
      let connect_OUT_inner lst_e =
        let diff_l = diff up_level [lst_e] in
        let e = new_edge dst lst_e in
        connect (e :: acc_e) out diff_l left_l level_rest;
      in
      List.iter up_level connect_OUT_inner;
    in

    let feed_new_level () =
      match level_rest with
      | [] -> (* Log.debug "acc_e %s" (str_of_tuple_l acc_e); *)
              (* TODO: hashtable for duplicates or not *)
              (* TODO: first use dedup *)
              edge_all_list := acc_e :: !edge_all_list;
      | y :: ys ->
         connect acc_e [] (List.append top out) y ys;
      | _ -> ()
    in
    
    (* TODO: change pattern matching for DUPs *)
    match bot with
    | [] -> feed_new_level ();
    | ("XOR", i) :: xs -> connect_XOR top i xs;
    | ("DUP1", i) :: xs -> connect_DUP top i xs;
    | ("DUP2", i) :: xs -> connect_DUP top i xs;
    | ("DUP", i) :: xs -> connect_DUP top i xs;
    | ("OUT", i) :: xs -> connect_OUT top i xs;
    | _ -> ();
  in

  (* start with the first two levels *)
  match level_l with
  | x :: y :: ys -> connect [] [] x y ys;
  | _ -> ()

(* in_deg: available srcs from the upper level *)
(* op_l: operation list *)
(* return: a list of list, represents the layout *)
(* each element is a tuple, a list of levels *)
(* tuple ('OP', idx),  first is string of operation, second is the index of v_a *)
let gen_base_graph seq t =
  let level_l = ref [] in

  let gen_l str low_i high_i =
    let in_l = ref [] in
    for i = low_i to high_i do
      in_l := (str, i) :: !in_l;
    done;
    List.rev !in_l;
  in
  level_l := (gen_l "IN" 0 (t.n_src - 1)) :: !level_l;

  let idx_XOR = ref (2 * t.n_src) in
  let idx_DUP = ref (!idx_XOR + t.n_xor) in

  (* create tuples for the level, seq is a list of list *)
  let create_level seq_l =
    let rec create_tuple acc l =
      match l with
      | [] -> acc
      | "X" :: xs -> let idx = !idx_XOR in
                     idx_XOR := !idx_XOR + 1;
                     create_tuple (("XOR", idx) :: acc) xs;
      | "D" :: xs -> let idx = !idx_DUP in
                     idx_DUP := !idx_DUP + 1;
                     create_tuple (("DUP", idx) :: acc) xs;
      | _ -> []
    in

    let add_to_level_l seq_level =
      let str_level = create_tuple [] seq_level in
      level_l := (List.rev str_level) :: !level_l;
      ()
    in
    List.iter seq_l add_to_level_l;
  in
  create_level seq;
  (* Log.debug "%s" (str_of_level (create_level seq)); *)
  (* List.iter seq create_level; *)
  level_l := (gen_l "OUT" ) t.n_src (2 * t.n_src - 1) :: !level_l;
  List.rev !level_l

let gen_level l t =
  let acc_list = ref[] in
  let rec level acc in_deg l =
    let rec same_level one_level src lst =
      if src > 0 then
        match lst with
        | [] -> ();
        | "X" :: rest ->
           if src >= 2 then
             let new_l = "X" :: one_level in
             level (new_l :: acc) (src - 1) rest;
             same_level new_l (src - 2) rest
           else
             ();
        | "D" :: rest ->
           let new_l = "D" :: one_level in
           level (new_l :: acc) (src + 1) rest;
           same_level new_l (src - 1) rest
        | _ -> ();
      else
        ();
    in

    if in_deg > 0 then
      match l with
      | [] -> let acc_rev = List.rev acc in
         acc_list := acc_rev :: !acc_list;
      | _ -> same_level [] in_deg l;
    else
      ();
  in
  level [] t.n_src l;
  !acc_list


let str_of_array a =
  let str_all = ref "" in
  let add_str str =
    str_all := !str_all ^ " " ^str;
    ();
  in
  Array.iter a add_str;
  !str_all


(* generate vertices based on #src and #XOR *)
(* string list *)
let gen_vertices v_a t =
  let str_a = [|"START"; "NEXTIV"; "XOR"; "DUP"; "PRP"|] in
  let n_a = [|t.n_src; t.n_src; t.n_xor; t.n_xor; t.n_prf|] in

  let add_to_v_a str start_i end_i  =
    for i = start_i to end_i do
      v_a.(i) <- str;
    done
  in

  let idx = ref 0 in
  for i = 0 to Array.length str_a - 1 do
    add_to_v_a str_a.(i) !idx (!idx + n_a.(i) - 1);
    idx := !idx + n_a.(i);
  done;
  v_a.(t.n_src - 1) <- "M";
  v_a.(t.n_src) <- "OUT"

let gen_candidate t = 
  let dup_list = gen_list "D" t.n_xor in
  let xor_list = gen_list "X" t.n_xor in
  let xor_dup_list = List.append dup_list xor_list in
  let perm_stream = permutations xor_dup_list in
  let perm_l = ref [] in
  let add_to_list l =
    perm_l := l :: !perm_l;
    ()
  in
  Stream.iter add_to_list perm_stream;
  let seq = List.dedup !perm_l in
  
  let rec gen_seq acc = function
    |[] -> acc
    |l :: ls ->
      let level_list = gen_level l t in
      let new_acc = ref[] in
      let add_to_acc l =
        new_acc := l :: !new_acc;
        ()
      in
      List.iter level_list add_to_acc;
      let result_l = List.append acc !new_acc in
      gen_seq result_l ls
    |_ -> acc
  in
  let seq_list = gen_seq [] seq in
  (* let log_list_list l = *)
  (*     Log.debug "%s" (str_of_list_list l) in *)
  (* List.iter seq_list log_list_list; *)

  let graph_l_l = ref[] in
  List.iter seq_list (fun e -> graph_l_l := (gen_base_graph e t) :: !graph_l_l);
  List.iter !graph_l_l (fun e -> gen_edge_list e);
  (* eliminate the duplicates *)
  let edge_list = List.dedup !edge_all_list in
  let filtered_list = List.filter edge_list (fun x -> not (List.contains_dup x)) in
  (* List.iter filtered_list (fun e -> Log.debug "base: %s" (str_of_tuple_l e)); *)
  printf "base graph=%d " (List.length filtered_list);
  let all_candidate = List.map filtered_list (fun e -> add_PRF e t) in
  List.dedup (List.join all_candidate)

(* Pass the INIT block from mosynth.ml, and instructions *)
let gen n_src n_xor n_prf init insts =
  (* save the secure blocks *)
  printf "n_src=%d, n_xor=%d, n_prf=%d\n" n_src n_xor n_prf;
  let t = {n_src=n_src; n_xor=n_xor; n_prf=n_prf} in
  let v_a = Array.create (2 * n_src + 2 * n_xor + n_prf) ""  in
  let candidate = gen_candidate t in
  printf "candidate=%d " (List.length candidate);
  gen_vertices v_a t;

  let secure_blocks = ref [] in
  let dec_blocks = ref [] in

  let secure_check l =
    Log.debug "%s" (str_of_tuple_l l);
    let g = MoGraph.create n_src v_a l in
    let is_decryptable = MoGraph.is_decryptable g in
    match is_decryptable with
    | true -> dec_blocks := l :: !dec_blocks;
              if MoGraph.validate g then
                secure_blocks := l :: !secure_blocks
              else
                ()
    | false -> ()
  in
  
  let rec secure_check_limit ctr l =
    match ctr < 74 with
    | true -> begin
        match l with
        | [] -> ()
        | x :: xs -> begin
            let g = MoGraph.create n_src v_a x in
            let is_decryptable = MoGraph.is_decryptable g in
            match is_decryptable with
            | true -> dec_blocks := x :: !dec_blocks;
                      if MoGraph.validate g then 
                        begin
                          secure_blocks := x :: !secure_blocks;
                          secure_check_limit (ctr + 1) xs
                        end
                      else begin
                          secure_check_limit ctr xs
                        end
            | false ->  begin 
                secure_check_limit ctr xs; 
              end

          end
      end
    | false -> ()         
  in

  (* secure_check_limit 0 candidate; *)
  (* List.nth_exn candidate 0 |> secure_check; *)
  List.iter candidate secure_check;
  (* printf "decrytable=%d " (List.length !dec_blocks); *)
  (* printf "secure=%d\n" (List.length !secure_blocks); *)

  (* let iobc = [(1,6); (2, 6); (6, 8); (8, 10); (10, 9); (0, 7); (9, 7); (7, 3); (8, 11); (11, 4); (9, 5)] in *)
  
  (* let iobc2 = [(1,6); (2, 6); (6, 8); (8, 11); (11, 9); (0, 7); (9, 7); (7, 3); (8, 10); (10, 4); (9, 5)] in *)

  (* let ioc = [(1,6); (2, 6); (6, 8); (8, 10); (10, 9); (0, 7); (9, 7); (7, 3); (8, 4); (9, 5)] in *)
  
  (* let rec is_sublist sub l = *)
  (*   match sub with *)
  (*   | [] -> true *)
  (*   | x :: xs -> if List.mem l x then *)
  (*                  is_sublist xs l *)
  (*                else *)
  (*                  false *)
  (* in *)

  (* let rec find_mode mode l = *)
  (*   match l with *)
  (*   | [] -> printf "Not found." *)
  (*   | x :: xs -> if is_sublist mode x then *)
  (*                  begin *)
  (*                    printf "%s\n" (str_op_of_tuple_l x v_a); *)
  (*                    let g = MoGraph.create n_src v_a x in *)
  (*                    MoGraph.display_with_feh g *)
  (*                  end *)
  (*                else *)
  (*                  find_mode mode xs *)
  (* in *)
  (* find_mode iobc !secure_blocks *)

  printf "%s\n" (str_op_of_tuple_l (List.nth_exn !secure_blocks 2) v_a);
  let g = MoGraph.create n_src v_a (List.nth_exn !secure_blocks 2) in
  MoGraph.display_with_feh g;
    
 
  (* printf "%s\n" (str_op_of_tuple_l (List.nth_exn !secure_blocks 2) v_a); *)
  (* printf "%s\n" (str_op_of_tuple_l (List.nth_exn !secure_blocks 11) v_a); *)
  (* printf "%s\n" (str_op_of_tuple_l (List.nth_exn !secure_blocks 73) v_a); *)
