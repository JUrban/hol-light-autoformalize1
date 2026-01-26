(* work.ml - Using declarative mizar/miz3 proof style *)

(* ========================================================================= *)
(* THEOREM 41.4: Every metrizable space is paracompact                       *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Definition: paracompact_space                                             *)
(* A space is paracompact if every open covering has a locally finite        *)
(* open refinement that covers the space.                                    *)
(* ------------------------------------------------------------------------- *)

let paracompact_space = new_definition
 `paracompact_space (top:A topology) <=>
  !U. (!u. u IN U ==> open_in top u) /\ topspace top SUBSET UNIONS U
      ==> ?V. (!v. v IN V ==> open_in top v) /\
              topspace top SUBSET UNIONS V /\
              (!v. v IN V ==> ?u. u IN U /\ v SUBSET u) /\
              locally_finite_in top V`;;

(* ------------------------------------------------------------------------- *)
(* Definition: countably_locally_finite_in                                   *)
(* A collection is countably locally finite if it's a countable union        *)
(* of locally finite collections.                                            *)
(* ------------------------------------------------------------------------- *)

let countably_locally_finite_in = new_definition
 `countably_locally_finite_in (top:A topology) U <=>
  ?f. U = UNIONS {f n | n IN (:num)} /\
      !n. locally_finite_in top (f n)`;;

(* ------------------------------------------------------------------------- *)
(* Every locally finite collection is countably locally finite               *)
(* ------------------------------------------------------------------------- *)

let LOCALLY_FINITE_IN_EMPTY = thm `;
  !top:A topology. locally_finite_in top {}
  by FINITE_EMPTY, UNIONS_0, EMPTY_SUBSET, FINITE_IMP_LOCALLY_FINITE_IN, CHEAT_TAC`;;

let LOCALLY_FINITE_IMP_COUNTABLY_LOCALLY_FINITE = thm `;
  !top:A topology U. locally_finite_in top U
    ==> countably_locally_finite_in top U
  proof
    let top be A topology;
    let U be (A->bool)->bool;
    assume locally_finite_in top U [1];
    set f = \n:num. if n = 0 then U else {}:(A->bool)->bool;
    f 0 = U [f0];
    !n. ~(n = 0) ==> f n = {} [fn] by CHEAT_TAC;
    U = UNIONS {f n | n IN (:num)} [2] by f0, fn, CHEAT_TAC;
    !n. locally_finite_in top (f n) [3]
    proof
      let n be num;
      n = 0 \/ ~(n = 0);
      cases by -;
      suppose n = 0;
      qed by 1, f0;
      suppose ~(n = 0);
        f n = {} by fn;
      qed by -, LOCALLY_FINITE_IN_EMPTY;
    end;
  qed by 2, 3, countably_locally_finite_in`;;

(* ------------------------------------------------------------------------- *)
(* Compact implies paracompact                                               *)
(* ------------------------------------------------------------------------- *)

let COMPACT_IMP_PARACOMPACT = thm `;
  !top:A topology. compact_space top ==> paracompact_space top
  by CHEAT_TAC`;;

(* ------------------------------------------------------------------------- *)
(* Lemma 39.2: Every open covering of a metrizable space has a countably     *)
(* locally finite open refinement that covers the space.                     *)
(* ------------------------------------------------------------------------- *)

let METRIZABLE_COUNTABLY_LOCALLY_FINITE_REFINEMENT = thm `;
  !top:A topology U.
    metrizable_space top /\
    (!u. u IN U ==> open_in top u) /\
    topspace top SUBSET UNIONS U
    ==> ?V. (!v. v IN V ==> open_in top v) /\
            topspace top SUBSET UNIONS V /\
            (!v. v IN V ==> ?u. u IN U /\ v SUBSET u) /\
            countably_locally_finite_in top V
  proof
    let top be A topology;
    let U be (A->bool)->bool;
    assume metrizable_space top [1];
    assume (!u. u IN U ==> open_in top u) [2];
    assume topspace top SUBSET UNIONS U [3];
    consider m such that top = mtopology m [4] by 1, metrizable_space;
  qed by 1, 2, 3, 4, CHEAT_TAC`;;

(* ------------------------------------------------------------------------- *)
(* Lemma 41.3 (Michael's Lemma): For a regular space, countably locally      *)
(* finite covering refinement implies locally finite covering refinement.    *)
(* This is the key step (1) => (4) from Michael's lemma.                     *)
(* ------------------------------------------------------------------------- *)

let MICHAEL_LEMMA = thm `;
  !top:A topology U.
    regular_space top /\
    (!u. u IN U ==> open_in top u) /\
    topspace top SUBSET UNIONS U /\
    countably_locally_finite_in top U
    ==> ?V. (!v. v IN V ==> open_in top v) /\
            topspace top SUBSET UNIONS V /\
            (!v. v IN V ==> ?u. u IN U /\ v SUBSET u) /\
            locally_finite_in top V
  by CHEAT_TAC`;;

(* ------------------------------------------------------------------------- *)
(* THEOREM 41.4: Every metrizable space is paracompact                       *)
(* ------------------------------------------------------------------------- *)

let METRIZABLE_IMP_PARACOMPACT = thm `;
  !top:A topology. metrizable_space top ==> paracompact_space top
  proof
    let top be A topology;
    assume metrizable_space top [1];
    regular_space top [2] by 1, METRIZABLE_IMP_REGULAR_SPACE;
    now
      let U be (A->bool)->bool;
      assume (!u. u IN U ==> open_in top u) /\ topspace top SUBSET UNIONS U [3];
      consider W such that
        (!w. w IN W ==> open_in top w) /\
        topspace top SUBSET UNIONS W /\
        (!w. w IN W ==> ?u. u IN U /\ w SUBSET u) /\
        countably_locally_finite_in top W [4]
        by 1, 3, METRIZABLE_COUNTABLY_LOCALLY_FINITE_REFINEMENT;
      consider V such that
        (!v. v IN V ==> open_in top v) /\
        topspace top SUBSET UNIONS V /\
        (!v. v IN V ==> ?w. w IN W /\ v SUBSET w) /\
        locally_finite_in top V [5]
        by 2, 4, MICHAEL_LEMMA;
      thus ?V. (!v. v IN V ==> open_in top v) /\
               topspace top SUBSET UNIONS V /\
               (!v. v IN V ==> ?u. u IN U /\ v SUBSET u) /\
               locally_finite_in top V
        by 4, 5, CHEAT_TAC;
    end;
  qed by -, paracompact_space`;;
