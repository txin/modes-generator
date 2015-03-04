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

let string_of_v v =
  MoInst.string_of_t (Instruction (G.V.label v))

let string_of_e e =
  let l = G.E.label e |> Int.Set.to_list in
  List.to_string Int.to_string l

(* keep a separate edge list and vertex list *)
let create init block =
  let vl = ref[] in
  let el = ref[] in
  
  let v = G.V.create Start in
  (* old API create, newer: make*)
  let va = Array.create 3 v in
  Array.set va 1 (G.V.create Xor);
  
  
  let base_vl = ref[Instruction Xor; Instruction Dup] in
  (* base_vl := block :: !base_vl; *)
  let g = G.create() in  
  let addVE inst =
    match inst with
    |Instruction i ->
      let v = G.V.create i in
      G.add_vertex g v;
      vl := List.append !vl [v];
    |_ -> 
      Log.info("Error: invalid instructions.");
  in
 
  G.add_edge g va.(0) va.(1);
  (* List.iter init f; *)
  (* add vertices from block*)
  (* List.iter block f;  *)
  List.iter block addVE;
  List.iter !base_vl addVE;
  
  (* create one edge *)

  (* let src = List.nth !vl 0  in  *)
  (* List location doesn't work, use hash instead?*)
  let src = List.find_exn !vl ~f:(fun v-> G.V.label v = Start) in
  let dst = List.find_exn !vl ~f:(fun v-> G.V.label v = Xor)in
  let e = G.E.create src Int.Set.empty dst in
  G.add_edge_e g e;
  el := List.append !el [e];
  g


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
