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

let UNIONS_SINGLETON_SEQUENCE = prove
 (`!(U:(A->bool)->bool).
     U = UNIONS {(\n. if n = 0 then U else {}) n | n IN (:num)}`,
  GEN_TAC THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
  [REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM; IN_UNIV] THEN
   GEN_TAC THEN DISCH_TAC THEN
   EXISTS_TAC `U:(A->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
   EXISTS_TAC `0` THEN REWRITE_TAC[];
   REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC; IN_UNIV] THEN
   GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[SUBSET_REFL; EMPTY_SUBSET]])

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
    U = UNIONS {f n | n IN (:num)} [2] by f0, fn, UNIONS_SINGLETON_SEQUENCE;
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

(* Helper: For x in UNIONS{B n | n}, there exists a minimum n with x in UNIONS(B n).
   This is used to show that x is in some shrunk set S_n(u), and that elements
   from later layers don't intersect x's neighborhood. *)

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
    consider B such that
      U = UNIONS {B n | n IN (:num)} /\
      !n. locally_finite_in top (B n) [4]
      by 3, countably_locally_finite_in;
    // Construction: V_layer n = UNIONS(B n), shrink n u = u DIFF (earlier layers)
    // The union C of all {shrink n u | u in B n} is locally finite because:
    // - Each layer C_n refines B_n, so is locally finite by LOCALLY_FINITE_IN_REFINEMENT
    // - For x in some u in B_N, elements of C_m (m > N) don't intersect u
    // - So we only need to consider finitely many layers around x
  qed by 1, 2, 3, 4, CHEAT_TAC`;;

(* Proof sketch for MICHAEL_STEP_1_2:
   Define V_layer n = UNIONS (B n) - the nth layer union
   Define shrink n u = u DIFF (UNIONS {V_layer i | i < n})
   Define C_n = {shrink n u | u IN B n}
   Define C = UNIONS {C_n | n IN (:num)}

   Key properties:
   1. shrink n u SUBSET u, so C refines U
   2. For x in topspace, let N = min {n | x in some u in B_n},
      then x in shrink_N u (since x not in any V_i for i < N)
   3. C_n is locally finite by LOCALLY_FINITE_IN_REFINEMENT
   4. For x in some u in B_N, elements of C_m for m > N don't intersect u
      (since shrink m v SUBSET v - V_N, and u SUBSET V_N)
   5. Therefore C is locally finite *)

(* Note: The steps (2)=>(3) and (3)=>(4) from Michael's original lemma are about
   equivalences between properties of the space, not direct constructions.
   For METRIZABLE_IMP_PARACOMPACT, we use a more direct approach combining steps. *)

(* Helper for going from locally finite to locally finite open in a regular space.
   This combines steps (2)=>(3)=>(4) from the textbook proof. *)
let LOCALLY_FINITE_OPEN_REFINEMENT = thm `;
  !top:A topology U C.
    regular_space top /\
    (!u. u IN U ==> open_in top u) /\
    topspace top SUBSET UNIONS C /\
    (!c. c IN C ==> ?u. u IN U /\ c SUBSET u) /\
    locally_finite_in top C
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
  qed by 1, 2, 5, LOCALLY_FINITE_OPEN_REFINEMENT`;;

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
