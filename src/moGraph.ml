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

(* type t = { g : G.t; v : G.V.t list; e : G.E.t list; out_init : G.V.t; *)
(*            out_block : G.V.t } *)

let create init block =
  let g = G.create() in
  g
