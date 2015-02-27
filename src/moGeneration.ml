open Core.Std
open MoOps
module MoInst = MoInstructions

let gen f ?(pruning=true) init depth insts =
  let blocks = ref [] in
  let process init block =
    Log.info "Trying [%s] [%s]"
      (MoInst.string_of_t_list init) (MoInst.string_of_t_list block);
    let g = MoGraph.createNew init block in
    if f g then
      begin
        Log.info "It works!";
        blocks := block :: !blocks
      end
  in
  !blocks
