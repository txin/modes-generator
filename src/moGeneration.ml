open Core.Std
open MoOps
module MoInst = MoInstructions

let gen init depth insts =
  let blocks = ref [] in
  let process init block =
    Log.info "Trying [%s] [%s]"
      (MoInst.string_of_t_list init) (MoInst.string_of_t_list block);
    let g = MoGraph.create init block in (*tested without graph g*)
    MoGraph.display_with_feh g;
    blocks := block :: !blocks
  in
  process init [Instruction Start];
  !blocks
