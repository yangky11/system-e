DECLARE PLUGIN "euclid_plugin"

(* This should not be needed, fix in Coq! *)
open Ltac_plugin

TACTIC EXTEND Hello
| [ "hello" ] -> [ Euclid_tactics.printHello ]
END
