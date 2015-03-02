open Core.Std
open MoOps
module MoInst = MoInstructions

let gen init depth insts =
  let blocks = ref [] in
  let process init block =
    Log.info "Trying [%s] [%s]"
      (MoInst.string_of_t_list init) (MoInst.string_of_t_list block);
    let g = MoGraph.create init block in
    blocks := block :: !blocks
  in
  !blocks
