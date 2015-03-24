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
module Dfs = Traverse.Dfs(G)
module Bfs = Traverse.Bfs(G)

let string_of_v v =
  MoInst.string_of_t (Instruction (G.V.label v))

let string_of_e e =
  let l = G.E.label e |> Int.Set.to_list in
  List.to_string Int.to_string l

(* iterate the edges of the graph *)
(* add PRFs in between the edges of the base graphs *)
let add_PRF g = 
  (* G.iter_edges g; *)
  Log.info "add_PRF"


(* Set edge 'e' in 't' to have label 'label' *)
let replace_edge g e label =
  G.remove_edge_e g e;
  let e = G.E.create (G.E.src e) label (G.E.dst e) in
  G.add_edge_e g e

(* first set up the edge be the first element of the list *)
let match_label g v fam_cnt =
  Log.info "%d" !fam_cnt;
  let parents v = G.pred_e g v in
  let parent v = parents v |> List.hd_exn in 
  let label = G.V.label v in
  let e = G.pred_e g v |> List.hd_exn in
  match label with
  | Dup | Inc | Nextiv_init ->
                 let e' = parent v in
                 replace_edge g e (G.E.label e');
                 true
  | Genrand | M | Prf | Prp | Start ->
                               let set = Int.Set.singleton !fam_cnt in
                               fam_cnt := !fam_cnt + 1;
                               replace_edge g e set;
                               true
  | Xor ->
     let elist = parents v in
     let l = List.hd_exn elist in
     let r = List.last_exn elist in
     let inter = Int.Set.inter (G.E.label l) (G.E.label r) in
     if Int.Set.length inter <> 0 then
       false
     else
       let fam = Int.Set.union (G.E.label l) (G.E.label r) in
       replace_edge g e fam;
       true
  | Nextiv_block | Out ->
                    (* failwith "should not reach here!" *)
                    true

let bfs_assign_families g =
  let fam_cnt = ref 0 in
  let rec loop i =
    let v = Bfs.get i in
    let el = G.pred_e g v in
    if List.length el >= 1 then
      begin
        match_label g v fam_cnt;
        loop (Bfs.step i)
      end
    else
      loop (Bfs.step i)
  in
  try loop (Bfs.start g) with Exit -> ()


(* Clear labels on all edges in 't' *)
let clear g =
  G.iter_edges_e (fun e -> replace_edge g e Int.Set.empty) g

(* assign families BFS *)
let assign_families g = 
  Log.info("assign_families");
  clear g;
  bfs_assign_families g
                      

(* keep a separate edge list and vertex list *)
let create init block =
  (* keep a ctr for the vertex *)
  (* old API create, newer: make*)
  (* use 7 ops first *)
  let e_ctr = ref 0 in
  let v = G.V.create Start in
  let va = Array.create 7 v in

  let base_vl = ref[Instruction Xor; Instruction Dup] in
  (* concatenate doesn't work so far *)
  (* base_vl := block :: !base_vl; *)
  let g = G.create() in  
  let addV inst =
    match inst with
    |Instruction i ->
      let v = G.V.create i in
      G.add_vertex g v;
      Array.set va !e_ctr v;
      e_ctr := !e_ctr + 1;
    |_ -> 
      Log.info("Error: invalid instructions.");
  in
  
  (* add vertices from block*)
  List.iter block addV;
  List.iter !base_vl addV;

  (* a list of tuples to represent the edges*)
  let base_graph_1 = [(0,4); (1,4); (4,5); (5,2); (5,3)] in

  let add_edge_tuple tup =
    let (src, dst) = tup in
    G.add_edge g va.(src) va.(dst)
  in
  List.iter base_graph_1 add_edge_tuple;
  add_PRF g;
  (* test iter_edges *)
  (* G.iter_edges va.(0) va.(1);p *)
  let f src dst =
    Log.info ("iter_edges f") in
  G.iter_edges f g;
  assign_families g;
  g

(* display with dot file*)
let display_with_feh g =
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
  G.Mark.clear g;
  let oc = Out_channel.create tmp in
  Dot.output_graph oc g;
  Out_channel.close oc;
  ignore (Sys.command ("dot -Tpng " ^ tmp ^ " | feh -"));
  Sys.remove tmp

(*Set edge 'e' in 't' to have label 'label'*)
let replace_edge g e label = 
  G.remove_edge_e g e;
  let e = G.E.create(G.E.src e) label (G.E.dst e) in
  G.add_edge_e g e

(*Clear labels on all edges in 't'*)
let clear g =
  G.iter_edges_e(fun e -> replace_edge g e Int.Set.empty) g
