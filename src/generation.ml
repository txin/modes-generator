open Log
open Core.Std;;

(* number of sources = number of sinks*)
(* TODO: 4, 3 stuck *)
let n_src = 3 
let n_xor = 2 
let n_prf = 2 

let v_a = Array.create (2 * n_src + 2 * n_xor + n_prf) "" 
(* TODO: not used for now *)
let e_a = Array.create (n_src + 3 * n_xor + n_prf) "" 

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
;;

let str_of_level l =
  (* List.fold_left (fun acc x ->) *)
  let str_all = ref "" in
  let add_str (str, idx) =
    str_all := !str_all ^ " (" ^str ^","^ (Int.to_string idx) ^") " ;
    ();
  in
  List.iter l add_str;
  !str_all
;;

let str_of_tuple_l l =
  let str_all = ref "" in
  let add_str (src, dst) =
    str_all := !str_all ^ " (" ^(Int.to_string src) ^","^ (Int.to_string dst) ^") " ;
    ();
  in
  List.iter l add_str;
  !str_all
;;

let str_of_list l =
  let str_all = ref "[" in
  let add_str str =
    str_all := !str_all ^ " " ^ str;
    ();
  in
  List.iter l add_str;
  str_all := !str_all ^ " ]";
  !str_all
;;


let str_of_list_list l =
  let str_all = ref "" in
  let add_str lst =
    str_all := !str_all ^ " " ^ (str_of_list lst);
    ();
  in
  List.iter l add_str;
  !str_all
;;

let rec gen_list elem len =
  if len = 0 then
    []
  else
    elem :: (gen_list elem (len - 1))
;;
                   
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
;;

(* (\* candidate modes *\) *)
(* (\* place PRF on the edges *\) *)
let add_PRF edge_l =
  (* let idx = ref (2 * n_src + 2 * n_xor) in *)
    let rec add_PRF_inner acc idx l =
    match l with
    | [] -> acc
    | (src, dst) :: xs ->
       add_PRF_inner ((src, idx) :: (idx, dst) :: acc) (idx + 1) xs;
  in
  let new_l = List.map (extract n_prf edge_l) (fun e -> add_PRF_inner edge_l (2*n_src + 2*n_xor) e) in
  List.iter new_l (fun e -> Log.debug "%s" (str_of_tuple_l e));
  (* Log.debug "%s" (str_of_tuple_l !edges_PRF); *)
    (* TODO: check the security/decryptability *)
  ()
;;

(* difference beween two lists *)
let diff l1 l2 = List.filter l1 (fun x -> not (List.mem l2 x))
;;
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

;;


(* in_deg: available srcs from the upper level *)
(* op_l: operation list *)
(* return: a list of list, represents the layout *)
(* each element is a tuple, a list of levels *)
(* tuple ('OP', idx),  first is string of operation, second is the index of v_a *)
let gen_base_graph seq =
  let level_l = ref [] in

  let gen_l str low_i high_i =
    let in_l = ref [] in
    for i = low_i to high_i do
      in_l := (str, i) :: !in_l;
    done;
    List.rev !in_l;
  in
  level_l := (gen_l "IN" 0 (n_src - 1)) :: !level_l;

  let idx_XOR = ref (2 * n_src) in
  let idx_DUP = ref (!idx_XOR + n_xor) in

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
  level_l := (gen_l "OUT" ) n_src (2 * n_src - 1) :: !level_l;
  List.rev !level_l
;;

let gen_level l =
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
  level [] n_src l;
  !acc_list
;;

let str_of_array a =
  let str_all = ref "" in
  let add_str str =
    str_all := !str_all ^ " " ^str;
    ();
  in
  Array.iter a add_str;
  !str_all
;;

(* generate vertices based on #src and #XOR *)
(* string list *)
let gen_vertices () =
  let str_a = [|"IN"; "OUT"; "XOR"; "DUP"; "PRF"|] in
  let n_a = [|n_src; n_src; n_xor; n_xor; n_prf|] in

  let add_to_v_a str start_i end_i  =
    for i = start_i to end_i do
      v_a.(i) <- str;
    done
  in

  let idx = ref 0 in
  for i = 0 to Array.length str_a - 1 do
    add_to_v_a str_a.(i) !idx (!idx + n_a.(i) - 1);
    idx := !idx + n_a.(i);
  done
;;


let gen () =
  (* Log.set_log_level Log.DEBUG; *)
  (* Log.set_output stdout; *)
  (* Log.color_on(); *)
  let dup_list = gen_list "D" n_xor in
  let xor_list = gen_list "X" n_xor in
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
      let level_list = gen_level l in
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

  (* let seq_list = gen_seq [] seq in *)
  (* let log_list_list l =  *)
  (*     Log.debug "%s" (str_of_list_list l) in *)
  (* List.iter seq_list log_list_list; *)
  gen_vertices ();
  (* 15: [XOR]; [DUP]; [XOR]; [DUP] *)
  (*  0: [DUP]; [DUP]; [XOR]; [XOR] *)
  (*  3: [DUP; DUP]; [XOR]; [XOR] *)
  (* 17: [DUP; XOR]; [XOR]; [DUP] *)
  let graph_l_l = ref[] in
  List.iter seq_list (fun e -> graph_l_l := (gen_base_graph e) :: !graph_l_l);
  (* let log_level l =  *)
  (*   Log.debug "%s" (str_of_level l) in *)
  (* List.iter graph_l log_level; *)
  List.iter !graph_l_l (fun e -> gen_edge_list e);
  (* eliminate the duplicates *)
  let edge_list = List.dedup !edge_all_list in
  let filtered_list = List.filter edge_list (fun x -> not (List.contains_dup x)) in
  add_PRF (List.hd_exn filtered_list)
  (* List.iter filtered_list (fun e -> Log.debug "%s" (str_of_tuple_l e)) *)
;;
