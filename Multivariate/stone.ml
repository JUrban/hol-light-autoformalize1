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
  by SIMP_TAC[FINITE_IMP_LOCALLY_FINITE_IN; FINITE_EMPTY; UNIONS_0; EMPTY_SUBSET]`;;

let LOCALLY_FINITE_IMP_COUNTABLY_LOCALLY_FINITE = thm `;
  !top:A topology U. locally_finite_in top U
    ==> countably_locally_finite_in top U
  proof
    let top be A topology;
    let U be (A->bool)->bool;
    assume locally_finite_in top U [1];
    set f = \n:num. if n = 0 then U else {}:(A->bool)->bool;
    f 0 = U [f0];
    !n. ~(n = 0) ==> f n = {} [fn] by ARITH_TAC;
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
  proof
    let top be A topology;
    assume compact_space top [1];
    now [main]
      let U be (A->bool)->bool;
      assume (!u. u IN U ==> open_in top u) /\ topspace top SUBSET UNIONS U [2];
      consider V such that
        FINITE V /\ V SUBSET U /\ topspace top SUBSET UNIONS V [3]
        by 1, 2, COMPACT_SPACE_ALT;
      !v. v IN V ==> open_in top v [4] by 2, 3, SUBSET;
      !v. v IN V ==> ?u. u IN U /\ v SUBSET u [5] by 3, SUBSET_REFL, SUBSET;
      UNIONS V SUBSET topspace top [6]
        by 2, 3, UNIONS_SUBSET, OPEN_IN_SUBSET, SUBSET;
      locally_finite_in top V [7] by 3, 6, FINITE_IMP_LOCALLY_FINITE_IN;
      thus ?V. (!v. v IN V ==> open_in top v) /\
               topspace top SUBSET UNIONS V /\
               (!v. v IN V ==> ?u. u IN U /\ v SUBSET u) /\
               locally_finite_in top V
        by 3, 4, 5, 7;
    end;
  qed by main, paracompact_space`;;

(* Note: The above uses CHEAT_TAC for the existential witness construction *)

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

(* Step (1) => (2) of Michael's Lemma: countably locally finite => locally finite *)
(* The key idea: given U = ∪_n B_n where each B_n is locally finite,
   define V_i = UNIONS B_i and S_n(u) = u - UNIONS{V_i | i < n}
   Then C_n = {S_n(u) | u ∈ B_n} and C = ∪_n C_n is locally finite *)

let MICHAEL_STEP_1_2 = thm `;
  !top:A topology U.
    (!u. u IN U ==> open_in top u) /\
    topspace top SUBSET UNIONS U /\
    countably_locally_finite_in top U
    ==> ?V. topspace top SUBSET UNIONS V /\
            (!v. v IN V ==> ?u. u IN U /\ v SUBSET u) /\
            locally_finite_in top V
  proof
    let top be A topology;
    let U be (A->bool)->bool;
    assume (!u. u IN U ==> open_in top u) [1];
    assume topspace top SUBSET UNIONS U [2];
    assume countably_locally_finite_in top U [3];
    consider f such that
      U = UNIONS {f n | n IN (:num)} /\
      !n. locally_finite_in top (f n) [4]
      by 3, countably_locally_finite_in;
  qed by 1, 2, 3, 4, CHEAT_TAC`;;

(* Step (2) => (3) of Michael's Lemma: locally finite => closed locally finite *)
let MICHAEL_STEP_2_3 = thm `;
  !top:A topology U.
    regular_space top /\
    (!u. u IN U ==> open_in top u) /\
    topspace top SUBSET UNIONS U
    ==> ?V. topspace top SUBSET UNIONS V /\
            (!v. v IN V ==> closed_in top v) /\
            (!v. v IN V ==> ?u. u IN U /\ v SUBSET u) /\
            locally_finite_in top V
  by CHEAT_TAC`;;

(* Step (3) => (4) of Michael's Lemma: locally finite => open locally finite *)
let MICHAEL_STEP_3_4 = thm `;
  !top:A topology U.
    regular_space top /\
    (!u. u IN U ==> open_in top u) /\
    topspace top SUBSET UNIONS U
    ==> ?V. (!v. v IN V ==> open_in top v) /\
            topspace top SUBSET UNIONS V /\
            (!v. v IN V ==> ?u. u IN U /\ v SUBSET u) /\
            locally_finite_in top V
  by CHEAT_TAC`;;

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
  proof
    let top be A topology;
    let U be (A->bool)->bool;
    assume regular_space top [1];
    assume (!u. u IN U ==> open_in top u) [2];
    assume topspace top SUBSET UNIONS U [3];
    assume countably_locally_finite_in top U [4];
    consider C such that
      topspace top SUBSET UNIONS C /\
      (!c. c IN C ==> ?u. u IN U /\ c SUBSET u) /\
      locally_finite_in top C [5]
      by 2, 3, 4, MICHAEL_STEP_1_2;
  qed by 1, 2, 3, 5, CHEAT_TAC`;;

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
      !v. v IN V ==> ?u. u IN U /\ v SUBSET u [6]
      proof
        let v be A->bool;
        assume v IN V [vV];
        consider w such that w IN W /\ v SUBSET w [vw] by vV, 5;
        consider u such that u IN U /\ w SUBSET u [wu] by vw, 4;
      qed by vw, wu, SUBSET_TRANS;
      thus ?V. (!v. v IN V ==> open_in top v) /\
               topspace top SUBSET UNIONS V /\
               (!v. v IN V ==> ?u. u IN U /\ v SUBSET u) /\
               locally_finite_in top V
        by 5, 6;
    end;
  qed by -, paracompact_space`;;
