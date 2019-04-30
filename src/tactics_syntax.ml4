DECLARE PLUGIN "euclid_plugin"

(* This should not be needed, fix in Coq! *)
open Ltac_plugin

TACTIC EXTEND Hello
| [ "hello" ] -> [ Euclid_tactics.printHello ]
END

TACTIC EXTEND Smt
| [ "smt" ] -> [ Euclid_tactics.smt ]
END

TACTIC EXTEND Euclid_smt
| [ "euclid_smt" ] -> [ Euclid_tactics.euclid_smt ]
END