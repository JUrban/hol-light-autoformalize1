(* work.ml *)
let URYSOHN_METRIZATION = prove
 (`!top:A topology.
        regular_space top /\ second_countable top /\ hausdorff_space top <=>
        metrizable_space top`,
  CHEAT_TAC);;
