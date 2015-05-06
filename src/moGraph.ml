open Graph
open Core.Std
open MoOps
module MoInst = MoInstructions

module E = struct
    type t = Int.Set.t
    let compare = Int.Set.compare
    let default = Int.Set.empty
  end

module V = struct type t = MoOps.instruction end
module G = Graph.Imperative.Digraph.AbstractLabeled(V)(E) 
module Topo = Topological.Make_stable(G)

type t = {g : G.t; v : G.V.t array; v_sorted : G.V.t array; n_src: int} 

let string_of_v v =
  MoInst.string_of_t (Instruction(G.V.label v))

let string_of_e e =
  let l = G.E.label e |> Int.Set.to_list in
  List.to_string Int.to_string l

(* n chooses k combination *)
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

(* Set edge 'e' in 't' to have label 'label' *)
let replace_edge g e label =
  G.remove_edge_e g e;
  let e = G.E.create (G.E.src e) label (G.E.dst e) in
  G.add_edge_e g e

(* first set up the edge be the first element of the list *)
(* global variable to save family counter *)
let fam_cnt = ref 1

(* initialize Start and M with families*)
let match_label g v =
  Log.info "%s %d" (string_of_v v) !fam_cnt;
  let label = G.V.label v in
  let pre_elist = G.pred_e g v in
  let succ_elist = G.succ_e g v in
  if List.length succ_elist >= 1 then
    let e = List.hd_exn succ_elist in
    let parent v = List.hd_exn pre_elist in 

    match label with
    | Dup ->                
       let e' = parent v in
       let e_2 = List.last_exn succ_elist in
       replace_edge g e (G.E.label e');
       replace_edge g e_2 (G.E.label e');

    | Inc | Nextiv_init ->
                   let e' = parent v in
                   replace_edge g e (G.E.label e')

    | Genrand | M | Prf | Prp | Start ->
                                 let set = Int.Set.singleton !fam_cnt in
                                 fam_cnt := !fam_cnt + 1;
                                 replace_edge g e set
    | Xor ->
       let l = List.hd_exn pre_elist in
       let r = List.last_exn pre_elist in
       let inter = Int.Set.inter (G.E.label l) (G.E.label r) in
       if Int.Set.length inter <> 0 then
         ()
       else
         let fam = Int.Set.union (G.E.label l) (G.E.label r) in
         replace_edge g e fam;
    | Nextiv_block | Out -> ()
  else
    ()

(* Clear labels on all edges in 't' *)
let clear t =
  G.iter_edges_e (fun e -> replace_edge t.g e Int.Set.empty) t.g;
  fam_cnt := 1

(* assign_families using toplogical sort *)
let assign_families t = 
  Log.info("assign_families");
  clear t;
  Array.iter t.v_sorted (fun e -> match_label t.g e)

(* validate with SMT solver *)
let validate t =
  Log.info "Validating graph...";
  let smt = MoSmt.create () in
  let f v =
    Log.debug "  Hit %s" ((MoOps.Instruction(G.V.label v)) |> MoInst.string_of_t);
    MoSmt.op smt (G.V.label v) in

  Array.iter t.v_sorted f;
  MoSmt.finalize smt;
  let fname = Filename.temp_file "z3" ".smt2" in
  MoSmt.write_to_file smt fname;
  let result = MoSmt.run fname in
  Sys.remove fname;
  Log.info " %b" result;
  result

(* pass the vertex array from generation.ml *)
let create n_src block_v block_e =
  let g = G.create() in
  let v = G.V.create Start in
  let block_len = Array.length block_v in
  (* calculate from the block length and number of INIT for the START vertices *)
  let v_a = Array.create (block_len + 4 * (n_src - 1)) v in

  let v_ctr = ref 0 in
  let addV inst_str phase =
    let inst = MoInst.from_string inst_str phase in
    match inst with
    | Instruction i ->
       let v = G.V.create i in
       G.add_vertex g v;
       v_a.(!v_ctr) <-  v;
       v_ctr := !v_ctr + 1;
    | _ -> failwith "Error: instruction is not valid"
  in
  Array.iter block_v (fun e -> addV e Block);  
  let init = ["GENRAND"; "DUP"; "OUT"; "NEXTIV"] in

  (* a list of tuples to represent the edges*)
  (* last tuple connects Init and Block *)
  let init_e = [(0, 1); (1, 2); (1, 3)] in
  let add_edge_tuple (src, dst) =
    G.add_edge g v_a.(src) v_a.(dst);
  in
  (* add n_src - 2 initialised vectors *)
  for i = 0 to n_src - 2 do
    List.iter init (fun e -> addV e Init);
    let tmp_len = 4 * i + block_len in
    let init_connection = List.map init_e
                                   (fun (x, y) -> (x + tmp_len, y + tmp_len)) in
    List.iter init_connection add_edge_tuple;
    (* connect to the block *)
    add_edge_tuple (tmp_len + 3, i);
  done;
  List.iter block_e add_edge_tuple;
  
  let ctr = ref 0 in
  (* sort the vertex array into a vertex array *)
  let v_a_sorted = Array.create (Array.length v_a) (v_a.(0)) in
  let add_to_v_a_sorted v =
    v_a_sorted.(!ctr) <- v;
    ctr := !ctr + 1
  in
  Topo.iter (fun e -> add_to_v_a_sorted e) g;
  let t = {g = g; v = v_a; v_sorted = v_a_sorted; n_src = n_src} in
  assign_families t;
  t

(* display with dot file*)
let display_with_feh t =
  let module Display = struct
      include G
      let ctr = ref 1
      let vertex_name v =
        let c =
          if Mark.get v = 0
          then begin
              Mark.set v !ctr;
              ctr := !ctr + 1;
              Mark.get v
            end
          else Mark.get v in
        Printf.sprintf "%s_%d" (MoInst.string_of_t (Instruction (V.label v))) c
      let graph_attributes _ = []
      let default_vertex_attributes _ = []
      let vertex_attributes _ = []
      let default_edge_attributes _ = []
      let edge_attributes e = [`Label (string_of_e e)]
      let get_subgraph _ = None
    end in
  let module Dot = Graph.Graphviz.Dot(Display) in
  let tmp = Filename.temp_file "mode" ".dot" in
  G.Mark.clear t.g;
  let oc = Out_channel.create tmp in
  Dot.output_graph oc t.g;
  Out_channel.close oc;
  ignore (Sys.command ("dot -Tpng " ^ tmp ^ " | feh -"));
  Sys.remove tmp

type dir = Forward | Backward
let string_of_dir = function
  | Forward -> "Forward"
  | Backward -> "Backward"

(* Checks whether a graph is decryptable *)
let is_decryptable t =
  Log.debug "Checking decryptability...";
  let m_idx = t.n_src - 1 in
  let m_v = t.v.(m_idx) in
  let out_idx = 2 * t.n_src - 2 in
  let out_v = t.v.(out_idx) in
  let module P_check = Path.Check(G) in
  let path_checker = P_check.create t.g in
  let result = P_check.check_path path_checker m_v out_v in
  Log.debug "path:%B" result;
  result

