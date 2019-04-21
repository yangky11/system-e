
let msg_in_tactic str : unit Proofview.tactic =
  Proofview.tclLIFT (Proofview.NonLogical.make (fun () ->
      Feedback.msg_warning (Pp.str str)))

let printHello : unit Proofview.tactic =
  let open Proofview.Notations in
  let inp = Unix.open_process_in "z3 -h" in
  let open Core in
  let _ = In_channel.input_lines inp in
  msg_in_tactic "hello" >>= fun () ->
  Tacticals.New.tclIDTAC
