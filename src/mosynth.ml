open Core.Std
open MoOps
module MoInst = MoInstructions

let instructions l all =
  let parse_ops all s =
    let loop lst s =
      let s = String.uppercase s in
      let rest s = String.slice s 1 0 in
      match String.prefix s 1 with
      | "+" ->
        let s = rest s in
        if List.exists lst (fun x -> x = s) then
          lst
        else
          s :: lst
      | "-" ->
        let s = rest s in
        List.filter lst (fun x -> x <> s)
      | _ -> failwith "Error: invalid format for -ops string"
    in
    let l = String.split s ~on:',' in
    List.fold l ~init:all ~f:loop
  in
  let all = match l with
    | "" -> all
    | s -> parse_ops all l in
  Log.info "Supported instructions: %s" (List.to_string ident all);
  let f s = MoInst.from_string s Block in
  List.map all ~f:f


let _ =

  let usage_msg () = "Usage: " ^ Sys.argv.(0) ^ " [<args>]\n" in

  let arg_all = ref false in
  let arg_n_src = ref 2 in
  let arg_n_xor = ref 1 in
  let arg_n_prf = ref 1 in
  let arg_decryptable_count = ref false in
  let arg_debug = ref 0 in
  let arg_init = ref "GENRAND DUP OUT NEXTIV" in
  let arg_ops = ref "" in
  let arg_print_modes = ref false in
  let arg_valid_count = ref false in

  let arg_specs = [
    ("-all", Arg.Set arg_all,
     "Run for all block sizes less than or equal to the size given by -block-size");
    ("-src", Arg.Set_int arg_n_src,
     "N  Number of sources in the block to generate (default = "
     ^ (Int.to_string !arg_n_src) ^ ")");
    ("-xor", Arg.Set_int arg_n_xor,
     "N  Number of XOR in the block to generate (default = "
     ^ (Int.to_string !arg_n_xor) ^ ")");
    ("-prf", Arg.Set_int arg_n_prf,
     "N  Number of sources in the block to generate (default = "
     ^ (Int.to_string !arg_n_prf) ^ ")");
    ("-valid-count", Arg.Set arg_valid_count,
     "Count schemes which are valid modes");
    ("-decryptable-count", Arg.Set arg_decryptable_count,
     "Count scheme which are decryptable");
    ("-print-modes", Arg.Set arg_print_modes,
     "Print found modes to stdout");
    ("-init", Arg.Set_string arg_init,
     "INIT  Sets INIT to be the init block (default = " ^ !arg_init ^ ")");
    ("-ops", Arg.Set_string arg_ops,
     "LIST  Sets ops in list to on (+) or off (-); e.g., \"-PRF,-INC\"");
    ("-debug", Arg.Set_int arg_debug,
     "N  Set debug level to N (0 ≤ N ≤ 4)");
  ] in
  Arg.parse arg_specs (fun _ -> ()) (usage_msg ());
  MoUtils.debug_config !arg_debug;

  (* 'all' is a list of the instruction we are using *)
  let all = [
    "DUP"; "INC"; "M"; "NEXTIV"; "OUT"; "PRF"; "PRP"; "XOR";
  ] in

  let all = instructions !arg_ops all in
  let init = MoInst.from_string_block (!arg_init) Init in
  Generation.gen !arg_n_src !arg_n_xor !arg_n_prf init all;
