let is_pruneable i block =
  let cmp_prev i prev =
  let cmpi i = prev = Instruction i in 
  match i with
  | Instruction i ->
