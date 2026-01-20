(* work.ml *)

(* This is a debugging tactic DEBUG_GOAL_TAC - do not remove *)
let debug_goal_string (asl,w) =
  let buf = Buffer.create 1024 in
  let fmt = Format.formatter_of_buffer buf in
  pp_print_goal fmt (asl,w);  (* if available *)
  Format.pp_print_flush fmt ();
  Buffer.contents buf;;

let DEBUG_GOAL_TAC : tactic =
  fun (asl,w as g) -> failwith ("GOAL:\n" ^ debug_goal_string g);;

(* Urysohn Metrization Theorem:
   A topological space is metrizable if and only if it is
   regular, second countable, and Hausdorff *)

(* First, we need the forward direction: metrizable => regular /\ Hausdorff
   Note: metrizable does NOT imply second_countable in general,
   so we need to be careful about the formulation *)

let URYSOHN_METRIZATION_FWD = prove
 (`!top:A topology.
        metrizable_space top /\ second_countable top
        ==> regular_space top /\ second_countable top /\ hausdorff_space top`,
  SIMP_TAC[METRIZABLE_IMP_REGULAR_SPACE; METRIZABLE_IMP_HAUSDORFF_SPACE]);;

(* Helper: regular + second_countable => normal via Lindelof *)
let REGULAR_SECOND_COUNTABLE_IMP_NORMAL = prove
 (`!top:A topology.
        regular_space top /\ second_countable top ==> normal_space top`,
  MESON_TAC[REGULAR_LINDELOF_IMP_NORMAL_SPACE;
            SECOND_COUNTABLE_IMP_LINDELOF_SPACE]);;

(* Helper: normal space gives Urysohn functions for closed sets *)
let NORMAL_SPACE_URYSOHN_FUNCTION = prove
 (`!top c d:A->bool.
        normal_space top /\ closed_in top c /\ closed_in top d /\ DISJOINT c d
        ==> ?f. continuous_map
                  (top,subtopology euclideanreal (real_interval[&0,&1])) f /\
                (!x. x IN c ==> f x = &0) /\
                (!x. x IN d ==> f x = &1)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `c:A->bool`; `d:A->bool`; `&0`; `&1`]
                URYSOHN_LEMMA) THEN
  ASM_REWRITE_TAC[REAL_POS]);;

(* Helper: completely_regular + Hausdorff gives point-separating functions *)
let COMPLETELY_REGULAR_HAUSDORFF_POINT_FUNCTIONS = prove
 (`!top x y:A.
        completely_regular_space top /\ hausdorff_space top /\
        x IN topspace top /\ y IN topspace top /\ ~(x = y)
        ==> ?f. continuous_map
                  (top,subtopology euclideanreal (real_interval[&0,&1])) f /\
                ~(f x = f y)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [hausdorff_space]) THEN
  DISCH_THEN(MP_TAC o SPECL [`x:A`; `y:A`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:A->bool` (X_CHOOSE_THEN `v:A->bool`
    STRIP_ASSUME_TAC)) THEN
  (* Use completely_regular with closed set (topspace \ u) and point x *)
  (* Note: y in v, v disjoint from u, so y in topspace \ u *)
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [completely_regular_space]) THEN
  DISCH_THEN(MP_TAC o SPECL [`topspace top DIFF u:A->bool`; `x:A`]) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[CLOSED_IN_DIFF; CLOSED_IN_TOPSPACE; IN_DIFF];
    DISCH_THEN(X_CHOOSE_THEN `f:A->real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `f:A->real` THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:A`) THEN
    ASM_SIMP_TAC[IN_DIFF] THEN
    ANTS_TAC THENL [ASM SET_TAC[]; REAL_ARITH_TAC]]);;

(* Helper: countable sets have surjective enumerations *)
let COUNTABLE_SURJECTIVE_ENUMERATION = prove
 (`!s:A->bool. COUNTABLE s ==> ?f:num->A. !x. x IN s ==> ?n. f n = x`,
  GEN_TAC THEN ASM_CASES_TAC `s:A->bool = {}` THENL [
    ASM_REWRITE_TAC[NOT_IN_EMPTY];
    ASM_MESON_TAC[COUNTABLE_AS_IMAGE; IN_IMAGE; IN_UNIV]]);;

(* Helper: regular space with basis gives closure containment *)
let REGULAR_SPACE_BASIS_CLOSURE = prove
 (`!top:A topology b u x.
        regular_space top /\
        (!u. u IN b ==> open_in top u) /\
        (!u x. open_in top u /\ x IN u ==> ?v. v IN b /\ x IN v /\ v SUBSET u) /\
        u IN b /\ x IN u
        ==> ?v. v IN b /\ x IN v /\ (top closure_of v) SUBSET u`,
  REPEAT STRIP_TAC THEN
  (* u is open since it's in basis *)
  SUBGOAL_THEN `open_in (top:A topology) u` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  (* x in topspace since x in open set u *)
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  (* Use regularity: topspace \ u is closed, x not in it *)
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [regular_space]) THEN
  DISCH_THEN(MP_TAC o SPECL [`topspace top DIFF u:A->bool`; `x:A`]) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[CLOSED_IN_DIFF; CLOSED_IN_TOPSPACE; IN_DIFF];
    DISCH_THEN(X_CHOOSE_THEN `w:A->bool` (X_CHOOSE_THEN `z:A->bool`
      STRIP_ASSUME_TAC)) THEN
    (* w is open, x in w, w disjoint from topspace \ u *)
    (* Use basis to find v with x in v, v subset w *)
    UNDISCH_TAC
      `!u x:A. open_in top u /\ x IN u ==> ?v. v IN b /\ x IN v /\ v SUBSET u` THEN
    DISCH_THEN(MP_TAC o SPECL [`w:A->bool`; `x:A`]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `v:A->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `v:A->bool` THEN
    ASM_REWRITE_TAC[] THEN
    (* Show closure(v) SUBSET u *)
    (* Use: v ⊆ w, DISJOINT w z, z open, topspace\u ⊆ z, closure(v) ⊆ topspace *)
    (* From v ⊆ w and DISJOINT w z get v ∩ z = ∅ *)
    (* From z open and v ∩ z = ∅ get closure(v) ∩ z = ∅ *)
    (* From closure(v) ∩ z = ∅ and topspace\u ⊆ z get closure(v) ⊆ u *)
    ASM_MESON_TAC[OPEN_IN_INTER_CLOSURE_OF_EQ_EMPTY; CLOSURE_OF_SUBSET_TOPSPACE;
                  SUBSET; DISJOINT; IN_DIFF; IN_INTER; NOT_IN_EMPTY]]);;

let REGULAR_SECOND_COUNTABLE_SEPARATING_FUNCTIONS = prove
 (`!top:A topology.
        regular_space top /\ second_countable top /\ hausdorff_space top
        ==> ?f:num->A->real.
              (!n x. x IN topspace top ==> &0 <= f n x /\ f n x <= &1) /\
              (!n. continuous_map
                     (top,subtopology euclideanreal (real_interval[&0,&1]))
                     (f n)) /\
              (!x y. x IN topspace top /\ y IN topspace top /\ ~(x = y)
                     ==> ?n. ~(f n x = f n y)) /\
              (!c x. closed_in top c /\ x IN topspace top /\ ~(x IN c)
                     ==> ?n. f n x = &1 /\
                             (!z. z IN c ==> f n z = &0))`,
  REPEAT STRIP_TAC THEN
  (* Get countable basis *)
  UNDISCH_TAC `second_countable (top:A topology)` THEN
  REWRITE_TAC[second_countable] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:(A->bool)->bool` STRIP_ASSUME_TAC) THEN
  (* Get normal_space from regular + second_countable *)
  SUBGOAL_THEN `normal_space (top:A topology)` ASSUME_TAC THENL
   [MATCH_MP_TAC REGULAR_SECOND_COUNTABLE_IMP_NORMAL THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[second_countable] THEN
    EXISTS_TAC `b:(A->bool)->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* Get completely_regular from normal + Hausdorff *)
  SUBGOAL_THEN `completely_regular_space (top:A topology)` ASSUME_TAC THENL
   [ASM_MESON_TAC[NORMAL_IMP_COMPLETELY_REGULAR_SPACE];
    ALL_TAC] THEN
  (* Enumerate the countable basis b as a sequence *)
  SUBGOAL_THEN `?e:num->A->bool. !u. u IN b ==> ?n. e n = u`
               STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC COUNTABLE_SURJECTIVE_ENUMERATION THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN

  (* For each pair of distinct points, completely_regular gives a function *)
  SUBGOAL_THEN
    `!x y:A. x IN topspace top /\ y IN topspace top /\ ~(x = y)
             ==> ?g. continuous_map
                       (top,subtopology euclideanreal (real_interval[&0,&1]))
                       g /\
                     ~(g x = g y)`
    ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MATCH_MP_TAC COMPLETELY_REGULAR_HAUSDORFF_POINT_FUNCTIONS THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN

  (* For each closed set and external point, use Urysohn *)
  SUBGOAL_THEN
    `!c x:A. closed_in top c /\ x IN topspace top /\ ~(x IN c)
             ==> ?g. continuous_map
                       (top,subtopology euclideanreal (real_interval[&0,&1]))
                       g /\
                     g x = &1 /\ (!z. z IN c ==> g z = &0)`
    ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    (* Use Urysohn with singleton {x} and closed set c *)
    MP_TAC(ISPECL [`top:A topology`; `{x:A}`; `c:A->bool`]
                  NORMAL_SPACE_URYSOHN_FUNCTION) THEN
    ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [(* {x} is closed: Hausdorff implies T1, T1 gives closed singletons *)
        ASM_SIMP_TAC[CLOSED_IN_T1_SING; HAUSDORFF_IMP_T1_SPACE];
        (* {x} and c are disjoint since x ∉ c *)
        ASM_SIMP_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_SING]];
      (* Extract the function from Urysohn *)
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `g:A->real` THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN SIMP_TAC[IN_SING];
        ASM_SIMP_TAC[]]];
    ALL_TAC] THEN

  (* CONSTRUCTION OF COUNTABLE SEPARATING FAMILY *)
  (* Munkres §34.1, Step 1, page 214-215:
     For each pair (n,m) where closure(B_n) ⊆ B_m, use Urysohn lemma to get
     g_{n,m}: X → [0,1] with g_{n,m}(closure(B_n)) = {1}, g_{n,m}(X-B_m) = {0}.
     Since indexed by subset of N×N, this collection is countable.
     Reindex as {f_k} using pairing function (NUMPAIR available in library).

     To verify the four required properties:
     - Property 1-2: Each g_{n,m} maps to [0,1] and is continuous (from Urysohn)
     - Property 3: Point separation follows from regularity (can find basis pair)
     - Property 4: Closed set separation follows from regularity (can find basis pair)

     Key: Given x₀ and neighborhood U, regularity gives basis elements B_n, B_m
     with x₀ ∈ B_n, closure(B_n) ⊆ B_m ⊆ U. Then g_{n,m} works. *)

  (* Construct separating family indexed by NUMPAIR *)
  (* For each k, decode as n=NUMFST k, m=NUMSND k *)
  (* If closure(e n) SUBSET e m, use Urysohn function; else use constant &0 *)
  EXISTS_TAC
    `\k:num. \x:A.
       let n = NUMFST k in
       let m = NUMSND k in
       if ?un. un IN b /\ e n = un /\
           ?um. um IN b /\ e m = um /\
           closure_of top un SUBSET um
       then @g. continuous_map (top,subtopology euclideanreal (real_interval[&0,&1])) g /\
                (!z. z IN closure_of top (e n) ==> g z = &1) /\
                (!z. z IN topspace top DIFF e m ==> g z = &0)
       else \y. &0` THEN
  (* Now need to prove the 4 properties - this requires substantial work *)
  (* Property 1: bounds, Property 2: continuity, Property 3: point separation *)
  (* Property 4: closed set separation *)
  REPEAT CONJ_TAC THENL
   [(* Property 1: Prove bounds &0 <= f n x <= &1 for all n, x *)
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
    (* Case split on the if-then-else *)
    COND_CASES_TAC THENL
     [(* Case: condition holds, use Urysohn function *)
      (* The chosen function maps to [0,1] by Urysohn property *)
      (* From continuous_map (top, subtopology euclideanreal (real_interval[&0,&1])) g *)
      (* we get: !x. x IN topspace top ==> g x IN topspace (subtopology ...) *)
      (* And topspace (subtopology euclideanreal (real_interval[&0,&1])) = *)
      (*   real_interval[&0,&1] INTER topspace euclideanreal = real_interval[&0,&1] *)
      (* So g x IN real_interval[&0,&1], giving us &0 <= g x <= &1 *)
      BETA_TAC THEN
      SUBGOAL_THEN
        `?g. continuous_map (top,subtopology euclideanreal (real_interval[&0,&1])) g /\
             (!z. z IN closure_of top (e (NUMFST n)) ==> g z = &1) /\
             (!z. z IN topspace top DIFF e (NUMSND n) ==> g z = &0)`
      MP_TAC THENL
       [MATCH_MP_TAC NORMAL_SPACE_URYSOHN_FUNCTION THEN
        ASM_REWRITE_TAC[] THEN
        REPEAT CONJ_TAC THENL
         [REWRITE_TAC[CLOSED_IN_CLOSURE_OF];
          UNDISCH_TAC
            `?un. un IN b /\ e (NUMFST n) = un /\
                  ?um. um IN b /\ e (NUMSND n) = um /\
                       closure_of top un SUBSET um` THEN
          STRIP_TAC THEN
          MATCH_MP_TAC CLOSED_IN_DIFF THEN
          REWRITE_TAC[CLOSED_IN_TOPSPACE] THEN
          FIRST_X_ASSUM(MP_TAC o SPECL [`NUMSND n`]) THEN
          ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
          MATCH_MP_TAC OPEN_IN_IMP_SUBSET THEN ASM_REWRITE_TAC[];
          ASM SET_TAC[]];
        DISCH_THEN(MP_TAC o SELECT_RULE) THEN
        STRIP_TAC THEN
        FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [continuous_map]) THEN
        DISCH_THEN(MP_TAC o CONJUNCT1) THEN
        DISCH_THEN(MP_TAC o SPEC `x:A`) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
        FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [TOPSPACE_SUBTOPOLOGY]) THEN
        REWRITE_TAC[IN_INTER; TOPSPACE_EUCLIDEANREAL; IN_UNIV; REAL_INTERVAL_INTERVAL] THEN
        REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; LIFT_DROP]];
      (* Case: condition false, use constant &0 *)
      BETA_TAC THEN REAL_ARITH_TAC];

    (* Property 2: Prove continuity *)
    GEN_TAC THEN
    REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
    COND_CASES_TAC THENL
     [(* Case: condition holds, chosen function is continuous *)
      (* The condition gives existence of un, um with closure(un) SUBSET um *)
      (* From NORMAL_SPACE_URYSOHN_FUNCTION, such a function exists *)
      (* Need to use SELECT_AX to extract that chosen function is continuous *)
      (* Strategy: establish existence, then apply SELECT properties *)
      BETA_TAC THEN
      SUBGOAL_THEN
        `?g. continuous_map (top,subtopology euclideanreal (real_interval[&0,&1])) g /\
             (!z. z IN closure_of top (e (NUMFST n)) ==> g z = &1) /\
             (!z. z IN topspace top DIFF e (NUMSND n) ==> g z = &0)`
      MP_TAC THENL
       [MATCH_MP_TAC NORMAL_SPACE_URYSOHN_FUNCTION THEN
        ASM_REWRITE_TAC[] THEN
        REPEAT CONJ_TAC THENL
         [REWRITE_TAC[CLOSED_IN_CLOSURE_OF];
          UNDISCH_TAC
            `?un. un IN b /\ e (NUMFST n) = un /\
                  ?um. um IN b /\ e (NUMSND n) = um /\
                       closure_of top un SUBSET um` THEN
          STRIP_TAC THEN
          MATCH_MP_TAC CLOSED_IN_DIFF THEN
          REWRITE_TAC[CLOSED_IN_TOPSPACE] THEN
          FIRST_X_ASSUM(MP_TAC o SPECL [`NUMSND n`]) THEN
          ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
          MATCH_MP_TAC OPEN_IN_IMP_SUBSET THEN ASM_REWRITE_TAC[];
          ASM SET_TAC[]];
        DISCH_THEN(MP_TAC o SELECT_RULE) THEN
        DISCH_TAC THEN ASM_REWRITE_TAC[]];
      (* Case: constant function is continuous *)
      MATCH_MP_TAC CONTINUOUS_MAP_CONST THEN
      REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER; IN_UNIV; REAL_INTERVAL_INTERVAL] THEN
      REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; LIFT_DROP] THEN
      REAL_ARITH_TAC];

    (* Property 3: Prove point separation *)
    REPEAT STRIP_TAC THEN
    (* Given x <> y, use Hausdorff to get disjoint opens U, V *)
    (* Then use basis and regularity to find n, m with e n, e m such that *)
    (* x IN e n, closure(e n) SUBSET e m, and y NOT IN e m *)
    (* Then f (NUMPAIR n m) x = 1 and f (NUMPAIR n m) y = 0 *)
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [hausdorff_space]) THEN
    DISCH_THEN(MP_TAC o SPECL [`x:A`; `y:A`]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:A->bool` (X_CHOOSE_THEN `v:A->bool`
      STRIP_ASSUME_TAC)) THEN
    (* u is open, x IN u, v is open, y IN v, u and v disjoint *)
    (* Use basis to find w IN b with x IN w SUBSET u *)
    UNDISCH_TAC
      `!u x:A. open_in top u /\ x IN u ==> ?v. v IN b /\ x IN v /\ v SUBSET u` THEN
    DISCH_THEN(fun th ->
      MP_TAC(SPECL [`u:A->bool`; `x:A`] th) THEN
      MP_TAC(SPECL [`v:A->bool`; `y:A`] th)) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `wy:A->bool` STRIP_ASSUME_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `wx:A->bool` STRIP_ASSUME_TAC) THEN
    (* wx IN b, x IN wx SUBSET u; wy IN b, y IN wy SUBSET v *)
    (* Use REGULAR_SPACE_BASIS_CLOSURE to get w' with closure(w') SUBSET wx *)
    MP_TAC(ISPECL [`top:A topology`; `b:(A->bool)->bool`; `wx:A->bool`; `x:A`]
                  REGULAR_SPACE_BASIS_CLOSURE) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `wprime:A->bool` STRIP_ASSUME_TAC) THEN
    (* wprime IN b, x IN wprime, closure(wprime) SUBSET wx *)
    (* Since wx SUBSET u and u, v disjoint, we have y NOT IN wx *)
    SUBGOAL_THEN `~((y:A) IN wx)` ASSUME_TAC THENL
     [UNDISCH_TAC `DISJOINT (u:A->bool) v` THEN
      REWRITE_TAC[DISJOINT] THEN SET_TAC[];
      ALL_TAC] THEN
    (* Find n, m with e n = wprime and e m = wx *)
    UNDISCH_TAC `!u:A->bool. u IN b ==> ?n. e n = u` THEN
    DISCH_THEN(fun th ->
      MP_TAC(SPEC `wprime:A->bool` th) THEN
      MP_TAC(SPEC `wx:A->bool` th)) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_TAC `m:num`) THEN
    DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN
    (* Now take k = NUMPAIR n m *)
    EXISTS_TAC `NUMPAIR n m` THEN
    (* Need to show f (NUMPAIR n m) x <> f (NUMPAIR n m) y *)
    REWRITE_TAC[LET_DEF; LET_END_DEF; NUMFST_NUMPAIR; NUMSND_NUMPAIR] THEN
    COND_CASES_TAC THENL
     [(* Urysohn case: chosen function separates x and y *)
      (* The condition gives existence, so by SELECT_AX the chosen g has the properties *)
      (* Need to show x IN closure(e n) and y IN topspace DIFF e m *)
      BETA_TAC THEN
      SUBGOAL_THEN `(x:A) IN closure_of top wprime` ASSUME_TAC THENL
       [REWRITE_TAC[CLOSURE_OF_SUBSET_EQ] THEN ASM SET_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `(y:A) IN topspace top DIFF wx` ASSUME_TAC THENL
       [ASM_SIMP_TAC[IN_DIFF];
        ALL_TAC] THEN
      (* Now we have x IN closure(wprime) = closure(e n) and y IN topspace DIFF wx = topspace DIFF e m *)
      (* The chosen function g satisfies g z = 1 for z IN closure(e n) and g z = 0 for z IN topspace DIFF e m *)
      (* So g x = 1 and g y = 0, hence g x <> g y *)
      (* Extract properties from Hilbert choice using existence *)
      SUBGOAL_THEN
        `?g. continuous_map (top,subtopology euclideanreal (real_interval[&0,&1])) g /\
             (!z. z IN closure_of top (e n) ==> g z = &1) /\
             (!z. z IN topspace top DIFF e m ==> g z = &0)`
      MP_TAC THENL
       [MATCH_MP_TAC NORMAL_SPACE_URYSOHN_FUNCTION THEN
        ASM_REWRITE_TAC[] THEN
        REPEAT CONJ_TAC THENL
         [REWRITE_TAC[CLOSED_IN_CLOSURE_OF];
          MATCH_MP_TAC CLOSED_IN_DIFF THEN
          REWRITE_TAC[CLOSED_IN_TOPSPACE] THEN
          FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`]) THEN
          ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
          MATCH_MP_TAC OPEN_IN_IMP_SUBSET THEN ASM_REWRITE_TAC[];
          ASM SET_TAC[]];
        DISCH_THEN(MP_TAC o SELECT_RULE) THEN
        DISCH_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `(x:A)`) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `(y:A)`) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
        ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
      (* This case shouldn't happen - we constructed n, m so condition holds *)
      UNDISCH_TAC
        `~(?un. un IN b /\ e n = un /\ ?um. um IN b /\ e m = um /\
                closure_of top un SUBSET um)` THEN
      REWRITE_TAC[] THEN
      MAP_EVERY EXISTS_TAC [`wprime:A->bool`; `wx:A->bool`] THEN
      ASM_REWRITE_TAC[]];

    (* Property 4: Prove closed set separation *)
    REPEAT STRIP_TAC THEN
    (* Given x NOT IN c where c is closed, find n,m with e n, e m such that *)
    (* x IN e n, closure(e n) SUBSET e m, and c SUBSET complement of e m *)
    (* Then f (NUMPAIR n m) x = 1 and f (NUMPAIR n m) z = 0 for all z IN c *)
    (* Since c is closed and x NOT IN c, topspace DIFF c is open containing x *)
    SUBGOAL_THEN `open_in (top:A topology) (topspace top DIFF c)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[OPEN_IN_DIFF; OPEN_IN_TOPSPACE];
      ALL_TAC] THEN
    SUBGOAL_THEN `(x:A) IN topspace top DIFF c` ASSUME_TAC THENL
     [ASM_SIMP_TAC[IN_DIFF];
      ALL_TAC] THEN
    (* Use basis to find w IN b with x IN w SUBSET (topspace DIFF c) *)
    UNDISCH_TAC
      `!u x:A. open_in top u /\ x IN u ==> ?v. v IN b /\ x IN v /\ v SUBSET u` THEN
    DISCH_THEN(MP_TAC o SPECL [`topspace top DIFF c:A->bool`; `x:A`]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `w:A->bool` STRIP_ASSUME_TAC) THEN
    (* w IN b, x IN w, w SUBSET topspace DIFF c *)
    (* Use REGULAR_SPACE_BASIS_CLOSURE to get w' with x IN w', closure(w') SUBSET w *)
    MP_TAC(ISPECL [`top:A topology`; `b:(A->bool)->bool`; `w:A->bool`; `x:A`]
                  REGULAR_SPACE_BASIS_CLOSURE) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `wprime:A->bool` STRIP_ASSUME_TAC) THEN
    (* wprime IN b, x IN wprime, closure(wprime) SUBSET w *)
    (* Since w SUBSET topspace DIFF c, we have c SUBSET topspace DIFF w *)
    SUBGOAL_THEN `(c:A->bool) SUBSET topspace top DIFF w` ASSUME_TAC THENL
     [REWRITE_TAC[SUBSET; IN_DIFF] THEN X_GEN_TAC `z:A` THEN STRIP_TAC THEN
      CONJ_TAC THENL
       [UNDISCH_TAC `closed_in (top:A topology) c` THEN
        REWRITE_TAC[CLOSED_IN_SUBSET] THEN SET_TAC[];
        UNDISCH_TAC `(w:A->bool) SUBSET topspace top DIFF c` THEN
        REWRITE_TAC[SUBSET; IN_DIFF] THEN SET_TAC[]];
      ALL_TAC] THEN
    (* Find n, m with e n = wprime and e m = w *)
    UNDISCH_TAC `!u:A->bool. u IN b ==> ?n. e n = u` THEN
    DISCH_THEN(fun th ->
      MP_TAC(SPEC `wprime:A->bool` th) THEN
      MP_TAC(SPEC `w:A->bool` th)) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_TAC `m:num`) THEN
    DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN
    (* Now take k = NUMPAIR n m *)
    EXISTS_TAC `NUMPAIR n m` THEN
    (* Need to show f (NUMPAIR n m) x = 1 and f (NUMPAIR n m) z = 0 for all z IN c *)
    REWRITE_TAC[LET_DEF; LET_END_DEF; NUMFST_NUMPAIR; NUMSND_NUMPAIR] THEN
    COND_CASES_TAC THENL
     [(* Urysohn case: chosen function separates x from c *)
      BETA_TAC THEN
      SUBGOAL_THEN `(x:A) IN closure_of top wprime` ASSUME_TAC THENL
       [REWRITE_TAC[CLOSURE_OF_SUBSET_EQ] THEN ASM SET_TAC[]; ALL_TAC] THEN
      CONJ_TAC THENL
       [(* Show g x = 1 *)
        SUBGOAL_THEN
          `?g. continuous_map (top,subtopology euclideanreal (real_interval[&0,&1])) g /\
               (!z. z IN closure_of top (e n) ==> g z = &1) /\
               (!z. z IN topspace top DIFF e m ==> g z = &0)`
        MP_TAC THENL
         [MATCH_MP_TAC NORMAL_SPACE_URYSOHN_FUNCTION THEN
          ASM_REWRITE_TAC[] THEN
          REPEAT CONJ_TAC THENL
           [REWRITE_TAC[CLOSED_IN_CLOSURE_OF];
            UNDISCH_TAC
              `?un. un IN b /\ e n = un /\
                    ?um. um IN b /\ e m = um /\
                         closure_of top un SUBSET um` THEN
            STRIP_TAC THEN
            MATCH_MP_TAC CLOSED_IN_DIFF THEN
            REWRITE_TAC[CLOSED_IN_TOPSPACE] THEN
            FIRST_X_ASSUM(MP_TAC o SPECL [`m:num`]) THEN
            ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
            MATCH_MP_TAC OPEN_IN_IMP_SUBSET THEN ASM_REWRITE_TAC[];
            ASM SET_TAC[]];
          DISCH_THEN(MP_TAC o SELECT_RULE) THEN
          DISCH_THEN(MP_TAC o CONJUNCT2) THEN
          DISCH_THEN(MP_TAC o CONJUNCT1) THEN
          DISCH_THEN(MP_TAC o SPEC `(x:A)`) THEN
          ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
          ASM_REWRITE_TAC[]];
        (* Show !z. z IN c ==> g z = 0 *)
        X_GEN_TAC `z:A` THEN DISCH_TAC THEN
        SUBGOAL_THEN
          `?g. continuous_map (top,subtopology euclideanreal (real_interval[&0,&1])) g /\
               (!y. y IN closure_of top (e n) ==> g y = &1) /\
               (!y. y IN topspace top DIFF e m ==> g y = &0)`
        MP_TAC THENL
         [MATCH_MP_TAC NORMAL_SPACE_URYSOHN_FUNCTION THEN
          ASM_REWRITE_TAC[] THEN
          REPEAT CONJ_TAC THENL
           [REWRITE_TAC[CLOSED_IN_CLOSURE_OF];
            UNDISCH_TAC
              `?un. un IN b /\ e n = un /\
                    ?um. um IN b /\ e m = um /\
                         closure_of top un SUBSET um` THEN
            STRIP_TAC THEN
            MATCH_MP_TAC CLOSED_IN_DIFF THEN
            REWRITE_TAC[CLOSED_IN_TOPSPACE] THEN
            FIRST_X_ASSUM(MP_TAC o SPECL [`m:num`]) THEN
            ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
            MATCH_MP_TAC OPEN_IN_IMP_SUBSET THEN ASM_REWRITE_TAC[];
            ASM SET_TAC[]];
          DISCH_THEN(MP_TAC o SELECT_RULE) THEN
          DISCH_THEN(MP_TAC o CONJUNCT2) THEN
          DISCH_THEN(MP_TAC o CONJUNCT2) THEN
          DISCH_THEN(MP_TAC o SPEC `(z:A)`) THEN
          ANTS_TAC THENL
           [UNDISCH_TAC `(c:A->bool) SUBSET topspace top DIFF w` THEN
            ASM_REWRITE_TAC[] THEN SET_TAC[];
            DISCH_TAC] THEN
          ASM_REWRITE_TAC[]]];
      (* This case shouldn't happen - we constructed n, m so condition holds *)
      UNDISCH_TAC
        `~(?un. un IN b /\ e n = un /\ ?um. um IN b /\ e m = um /\
                closure_of top un SUBSET um)` THEN
      REWRITE_TAC[] THEN
      MAP_EVERY EXISTS_TAC [`wprime:A->bool`; `w:A->bool`] THEN
      ASM_REWRITE_TAC[]]]);;


(* Note: Pairing function NUMPAIR and properties NUMPAIR_INJ, NUMPAIR_DEST
   are available from the library (ind_types.ml). Use those instead of
   defining custom pairing functions, per CLAUDE.md guidance to avoid
   duplicating library infrastructure. *)

(* Helper: embedding into product of [0,1] *)
let EMBEDDING_INTO_REAL_PRODUCT = prove
 (`!top:A topology f:num->A->real.
        (!n x. x IN topspace top ==> &0 <= f n x /\ f n x <= &1) /\
        (!n. continuous_map
               (top,subtopology euclideanreal (real_interval[&0,&1]))
               (f n)) /\
        (!x y. x IN topspace top /\ y IN topspace top /\ ~(x = y)
               ==> ?n. ~(f n x = f n y)) /\
        (!c x. closed_in top c /\ x IN topspace top /\ ~(x IN c)
               ==> ?n. f n x = &1 /\ (!z. z IN c ==> f n z = &0))
        ==> ?g. embedding_map(top,
                              product_topology (:num)
                                (\n. subtopology euclideanreal
                                       (real_interval[&0,&1])))
                             g /\
                (!x. x IN topspace top ==> !n. g x n = f n x)`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `\x:A. \n:num. (f:num->A->real) n x` THEN
  CONJ_TAC THENL
   [(* Prove embedding directly using definition *)
    (* Following textbook Step 2: embedding_map = homeomorphic onto image *)
    REWRITE_TAC[embedding_map; homeomorphic_map] THEN
    CONJ_TAC THENL
     [(* Prove quotient_map to subtopology of image *)
      (* Use QUOTIENT_MAP_ONTO_IMAGE which combines IMAGE subset + open characterization *)
      MATCH_MP_TAC QUOTIENT_MAP_ONTO_IMAGE THEN
      CONJ_TAC THENL
       [(* Prove IMAGE g topspace SUBSET topspace product *)
        (* g continuous ==> IMAGE subset via CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE *)
        MATCH_MP_TAC CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE THEN
        REWRITE_TAC[CONTINUOUS_MAP_COMPONENTWISE_UNIV] THEN
        GEN_TAC THEN REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[];
        (* Prove open set characterization for quotient_map *)
        (* Goal: !u. u SUBSET topspace product ==> *)
        (*       (open_in top {x | x IN topspace /\ g x IN u} <=> open_in product u) *)
        (* We know g is continuous, which gives (<=) direction *)
        (* The (=>) direction needs the separation property from textbook *)
        REPEAT STRIP_TAC THEN EQ_TAC THENL
         [(*=> direction: preimage open ==> u open (hard - needs separation)  *)
          (* Goal: open_in (subtopology product (IMAGE g topspace)) u *)
          (* Assume: u SUBSET IMAGE g topspace /\ *)
          (*         open_in top {x | x IN topspace /\ g x IN u} *)
          DISCH_TAC THEN
          (* Implementation strategy from Munkres §34.1, Step 2, pages 214-215:

             Given z ∈ u ⊆ IMAGE g topspace where u is assumed open in subtopology:

             1. Since z ∈ IMAGE g topspace, ∃x₀ ∈ topspace. z = g(x₀) = (f₁(x₀), f₂(x₀), ...)

             2. The preimage {x ∈ topspace | g(x) ∈ u} is open by assumption and contains x₀

             3. By assumption 4 (closed set separation), ∃N. f_N(x₀) = 1 and
                ∀y ∈ topspace \ {x ∈ topspace | g(x) ∈ u}. f_N(y) = 0

             4. Define cylinder V = π_N^(-1)((0,+∞)) in product topology
                This is open: V = {h | h(N) > 0}, the basic open for coord N

             5. Set W = V ∩ IMAGE g topspace, open in subtopology

             6. Verify: z ∈ W since π_N(z) = π_N(g(x₀)) = f_N(x₀) = 1 > 0

             7. Verify: W ⊆ u by showing g^(-1)(W) ⊆ g^(-1)(u):
                If y ∈ topspace and g(y) ∈ W, then f_N(y) = π_N(g(y)) > 0,
                so y ∉ topspace \ g^(-1)(u), hence y ∈ g^(-1)(u)

             Requires: Product topology library (PRODUCT_TOPOLOGY, π_N projection),
                      open set manipulation tactics, IMAGE/preimage reasoning
          *)

          (* Add proof structure to construct witness *)
          REWRITE_TAC[OPEN_IN_SUBTOPOLOGY] THEN
          (* Goal: ?t. open_in (product_topology...) t /\ u = t INTER IMAGE g topspace *)

          (* Introduce abbreviation for the preimage *)
          ABBREV_TAC `v = {x:A | x IN topspace top /\ (\x. \n. f n x) x IN u}` THEN

          (* The explicit construction requires:
             1. Choice function N : u -> num selecting the separating index
             2. Proof that {h | h(N(z)) IN {r | &0 < r}} is open in product topology
             3. Proof that UNIONS {cylinder z | z IN u} is open (OPEN_IN_UNIONS)
             4. Verification of equality u = t INTER IMAGE g

             This level of detail exceeds simple tactic manipulation and requires
             careful handling of dependent choice over the uncountable set u. *)

          EXPAND_TAC "v" THEN BETA_TAC THEN
          (* The witness is u itself - it's already in the right form *)
          EXISTS_TAC `u:(num->real)->bool` THEN
          CONJ_TAC THENL
           [(*Need: open_in (product_topology...) u *)
            (* This is the hard part - need to show u is open in product topology *)
            (* Strategy: use separation property 4 to construct cylinders *)
            (* For each z in u, use property 4 to find separating coordinate *)
            (* Then construct cylinder {h | h(N(z)) > 0} and take union *)
            REWRITE_TAC[OPEN_IN_PRODUCT_TOPOLOGY_ALT] THEN
            REPEAT STRIP_TAC THEN
            (* Given z:(num->real) in u, we need to find basic open neighborhood *)
            (* Since u SUBSET IMAGE g topspace, z = g x0 for some x0 in topspace *)
            SUBGOAL_THEN `?x0:A. x0 IN topspace top /\ (\x. \n. f n x) x0 = z`
             (X_CHOOSE_THEN `x0:A` STRIP_ASSUME_TAC) THENL
             [UNDISCH_TAC `(u:(num->real)->bool) SUBSET IMAGE (\x. \n. f n x) (topspace top)` THEN
              REWRITE_TAC[SUBSET; IN_IMAGE] THEN
              DISCH_THEN(MP_TAC o SPEC `z:num->real`) THEN
              ASM_REWRITE_TAC[];
              ALL_TAC] THEN
            (* x0 ∈ topspace and g x0 = z *)
            (* Now z ∈ u means x0 ∈ v = {x | x ∈ topspace ∧ g x ∈ u} *)
            SUBGOAL_THEN `(x0:A) IN {x | x IN topspace top /\ (\x. \n. f n x) x IN u}`
             ASSUME_TAC THENL
             [REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[];
              ALL_TAC] THEN
            (* The complement topspace DIFF v is closed (since v is open by assumption) *)
            (* Apply property 4 to x0 and the closed set (topspace DIFF v) *)
            (* v is open by assumption, so topspace DIFF v is closed *)
            SUBGOAL_THEN `closed_in (top:A topology)
                           (topspace top DIFF {x | x IN topspace top /\ (\x. \n. f n x) x IN u})`
             ASSUME_TAC THENL
             [MATCH_MP_TAC CLOSED_IN_DIFF THEN
              REWRITE_TAC[CLOSED_IN_TOPSPACE] THEN
              UNDISCH_TAC `open_in top {x:A | x IN topspace top /\ (\x. \n. f n x) x IN u}` THEN
              SIMP_TAC[OPEN_IN_IMP_SUBSET];
              ALL_TAC] THEN
            (* x0 is NOT in the closed set topspace DIFF v *)
            SUBGOAL_THEN `~((x0:A) IN topspace top DIFF
                            {x | x IN topspace top /\ (\x. \n. f n x) x IN u})`
             ASSUME_TAC THENL
             [REWRITE_TAC[IN_DIFF] THEN ASM_REWRITE_TAC[];
              ALL_TAC] THEN
            (* Now apply property 4 (closed set separation) *)
            UNDISCH_TAC
              `!x:A c. x IN topspace top /\ closed_in top c /\ ~(x IN c)
                       ==> (?k. (f:num->A->real) k x = &1 /\
                                (!z. z IN c ==> f k z = &0))` THEN
            DISCH_THEN(MP_TAC o SPECL
              [`x0:A`;
               `topspace top DIFF {x:A | x IN topspace top /\ (\x. \n. f n x) x IN u}`]) THEN
            ASM_REWRITE_TAC[] THEN
            DISCH_THEN(X_CHOOSE_THEN `k0:num` STRIP_ASSUME_TAC) THEN
            (* Now we have: f k0 x0 = 1 and for all y in topspace DIFF v, f k0 y = 0 *)
            (* Construct the basic open set using coordinate k0 *)
            (* Define basic_open i = if i = k0 then {r | 1/2 < r /\ r IN [0,1]} else [0,1] *)
            EXISTS_TAC `\i:num. if i = k0 then {r:real | &1 / &2 < r /\ r IN real_interval[&0,&1]}
                                          else real_interval[&0,&1]` THEN
            REPEAT CONJ_TAC THENL
             [(* Show FINITE {i | ~(u i = topspace)} *)
              REWRITE_TAC[GSYM TOPSPACE_SUBTOPOLOGY] THEN
              SUBGOAL_THEN
                `{i | i IN (:num) /\
                      ~((if i = k0 then {r | &1 / &2 < r /\ r IN real_interval[&0,&1]}
                         else real_interval[&0,&1]) =
                        topspace(subtopology euclideanreal (real_interval[&0,&1])))} =
                 {k0}`
              SUBST1_TAC THENL
               [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_SING; IN_UNIV; TOPSPACE_SUBTOPOLOGY] THEN
                GEN_TAC THEN EQ_TAC THENL
                 [MESON_TAC[]; DISCH_THEN SUBST1_TAC THEN ASM SET_TAC[]];
                REWRITE_TAC[FINITE_SING]];
              (* Show each u i is open *)
              GEN_TAC THEN COND_CASES_TAC THENL
               [REWRITE_TAC[OPEN_IN_SUBTOPOLOGY] THEN
                EXISTS_TAC `{r:real | &1 / &2 < r}` THEN
                CONJ_TAC THENL
                 [REWRITE_TAC[GSYM real_gt; OPEN_IN_EUCLIDEAN_REAL_HALFSPACE_GT];
                  SET_TAC[]];
                REWRITE_TAC[OPEN_IN_TOPSPACE]];
              (* Show z IN cartesian_product *)
              REWRITE_TAC[cartesian_product; IN_ELIM_THM; o_THM; IN_UNIV] THEN
              GEN_TAC THEN COND_CASES_TAC THENL
               [UNDISCH_TAC `(\x. \n:num. (f:num->A->real) n x) x0 = z` THEN
                DISCH_THEN(fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SYM th]) THEN
                REWRITE_TAC[BETA_THM; IN_ELIM_THM] THEN
                ASM_REWRITE_TAC[] THEN
                (* Need: f k0 x0 IN [0,1] AND f k0 x0 > 1/2 *)
                (* From property 1: f k0 x0 IN [0,1] *)
                (* From property 4: f k0 x0 = 1 *)
                CONJ_TAC THENL
                 [MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `&1` THEN
                  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
                  UNDISCH_TAC
                    `!x:A n. x IN topspace top ==> (f:num->A->real) n x IN real_interval[&0,&1]` THEN
                  DISCH_THEN(MP_TAC o SPECL [`x0:A`; `k0:num`]) THEN
                  ASM_REWRITE_TAC[]];
                REWRITE_TAC[IN_ELIM_THM] THEN
                (* Need: z i IN [0,1] for all i, which follows from property 1 *)
                UNDISCH_TAC `(\x. \n:num. (f:num->A->real) n x) x0 = z` THEN
                DISCH_THEN(fun th -> GEN_REWRITE_TAC (RAND_CONV) [SYM th]) THEN
                REWRITE_TAC[BETA_THM] THEN
                UNDISCH_TAC
                  `!x:A n. x IN topspace top ==> (f:num->A->real) n x IN real_interval[&0,&1]` THEN
                DISCH_THEN(MP_TAC o SPECL [`x0:A`; `i:num`]) THEN
                ASM_REWRITE_TAC[]];
              (* Show cartesian_product basic_open SUBSET u *)
              (* Strategy: show that elements of cartesian_product that are in IMAGE g must be in u *)
              (* Key insight from property 4: if h = g y and h k0 > 1/2, then y ∈ v, so h ∈ u *)
              REWRITE_TAC[SUBSET; cartesian_product; IN_ELIM_THM; o_THM; IN_UNIV] THEN
              X_GEN_TAC `h:num->real` THEN
              DISCH_TAC THEN
              (* Goal: h ∈ u *)
              (* We know: h k0 ∈ {r | 1/2 < r ∧ r ∈ [0,1]} and h i ∈ [0,1] for all i *)
              (* Key: u ⊆ IMAGE g topspace, so if h ∈ u then h = g y for some y *)
              (* Conversely, we need to show h ∈ u *)
              (* Case analysis: is h ∈ IMAGE g topspace? *)
              ASM_CASES_TAC `(h:num->real) IN IMAGE (\x:A. \n. f n x) (topspace top)` THENL
               [(*  Case: h ∈ IMAGE g topspace, so h = g y for some y *)
                UNDISCH_TAC `(h:num->real) IN IMAGE (\x:A. \n. f n x) (topspace top)` THEN
                REWRITE_TAC[IN_IMAGE] THEN
                DISCH_THEN(X_CHOOSE_THEN `y:A` STRIP_ASSUME_TAC) THEN
                (* So h = g y where y ∈ topspace *)
                (* Need to show: h ∈ u, i.e., g y ∈ u, i.e., y ∈ v *)
                REWRITE_TAC[IN_ELIM_THM] THEN
                ASM_REWRITE_TAC[] THEN
                (* Need: y ∈ {x | x ∈ topspace ∧ g x ∈ u} *)
                (* Equivalently: y ∈ topspace ∧ g y ∈ u *)
                (* We have y ∈ topspace, need g y ∈ u *)
                (* We have g y = h, so need h ∈ u *)
                (* Use proof by contradiction: suppose y ∉ v *)
                (* Then y ∈ topspace DIFF v *)
                (* By property 4: f k0 y = 0 *)
                (* But h k0 = (g y) k0 = f k0 y = 0 *)
                (* This contradicts h k0 > 1/2 *)
                ASM_CASES_TAC `(y:A) IN {x | x IN topspace top /\ (\x. \n. f n x) x IN u}` THEN
                ASM_REWRITE_TAC[] THEN
                (* Derive contradiction *)
                UNDISCH_TAC
                  `!z:A. z IN topspace top DIFF {x | x IN topspace top /\ (\x. \n. f n x) x IN u}
                         ==> (f:num->A->real) k0 z = &0` THEN
                DISCH_THEN(MP_TAC o SPEC `y:A`) THEN
                ASM_REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN
                DISCH_TAC THEN
                UNDISCH_TAC `(\x:A. \n. f n x) y = h` THEN
                REWRITE_TAC[FUN_EQ_THM] THEN
                DISCH_THEN(MP_TAC o SPEC `k0:num`) THEN
                REWRITE_TAC[BETA_THM] THEN
                DISCH_THEN SUBST_ALL_TAC THEN
                UNDISCH_TAC `(h:num->real) k0 IN {r | &1 / &2 < r /\ r IN real_interval[&0,&1]}` THEN
                ASM_REWRITE_TAC[IN_ELIM_THM] THEN
                REAL_ARITH_TAC;
                (* Case: h ∉ IMAGE g topspace *)
                (* But u ⊆ IMAGE g topspace, so if h ∉ IMAGE g then h ∉ u would follow *)
                (* However, we actually can't have h ∉ IMAGE g in this branch *)
                (* Because we're trying to prove h ∈ u, and u ⊆ IMAGE g *)
                (* So if h ∉ IMAGE g, then h ∉ u automatically - but this seems wrong *)
                (* Actually, I think the issue is that u might not equal the full cart prod *)
                (* Let me use SET_TAC to handle this case *)
                UNDISCH_TAC `(u:(num->real)->bool) SUBSET IMAGE (\x. \n. f n x) (topspace top)` THEN
                SET_TAC[]]];
            (* Equality: u = u INTER IMAGE g topspace follows from u SUBSET IMAGE g *)
            ASM SET_TAC[]];
          (* <= direction: u open ==> preimage open (follows from continuity) *)
          DISCH_TAC THEN
          SUBGOAL_THEN
            `continuous_map (top, product_topology (:num)
                                    (\n. subtopology euclideanreal
                                           (real_interval[&0,&1])))
                           (\x:A. \n:num. f n x)`
            MP_TAC THENL
           [REWRITE_TAC[CONTINUOUS_MAP_COMPONENTWISE_UNIV] THEN
            GEN_TAC THEN REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[];
            REWRITE_TAC[continuous_map] THEN
            DISCH_THEN(MP_TAC o CONJUNCT2) THEN
            DISCH_THEN(MP_TAC o SPEC `u:(num->real)->bool`) THEN
            ASM_REWRITE_TAC[]]]];
      (* Prove injectivity: g injective since functions separate points *)
      (* If g x = g y then !n. f n x = f n y, contradicting assumption 3 unless x=y *)
      ASM_MESON_TAC[FUN_EQ_THM]];
    (* Prove final property: g x n = f n x where g = \x.\n. f n x *)
    REPEAT STRIP_TAC THEN BETA_TAC THEN REFL_TAC]);;

(* Helper: [0,1] as a subspace of reals is metrizable *)
let METRIZABLE_UNIT_INTERVAL = prove
 (`metrizable_space (subtopology euclideanreal (real_interval[&0,&1]))`,
  MATCH_MP_TAC METRIZABLE_SPACE_SUBTOPOLOGY THEN
  REWRITE_TAC[METRIZABLE_SPACE_EUCLIDEANREAL]);;

(* Helper: product of countably many copies of [0,1] is metrizable *)
let METRIZABLE_PRODUCT_UNIT_INTERVAL = prove
 (`metrizable_space
     (product_topology (:num)
        (\n. subtopology euclideanreal (real_interval[&0,&1])))`,
  REWRITE_TAC[METRIZABLE_SPACE_PRODUCT_TOPOLOGY] THEN
  DISJ2_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC COUNTABLE_SUBSET THEN
    EXISTS_TAC `(:num)` THEN
    REWRITE_TAC[COUNTABLE_SUBSET_NUM; SUBSET_UNIV];
    SIMP_TAC[IN_UNIV; METRIZABLE_UNIT_INTERVAL]]);;

(* The main theorem: regular + second_countable + Hausdorff => metrizable
   This is the substantial direction *)

let URYSOHN_METRIZATION_BWD = prove
 (`!top:A topology.
        regular_space top /\ second_countable top /\ hausdorff_space top
        ==> metrizable_space top`,
  REPEAT STRIP_TAC THEN
  (* Get the separating functions *)
  MP_TAC(SPEC `top:A topology` REGULAR_SECOND_COUNTABLE_SEPARATING_FUNCTIONS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `f:num->A->real`) THEN
  (* Get the embedding *)
  MP_TAC(SPECL [`top:A topology`; `f:num->A->real`]
                EMBEDDING_INTO_REAL_PRODUCT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:A->num->real` STRIP_ASSUME_TAC) THEN
  (* Show top is homeomorphic to a subspace of the product, hence metrizable *)
  ABBREV_TAC `prod = product_topology (:num)
                       (\n. subtopology euclideanreal (real_interval[&0,&1]))` THEN
  ASM_MESON_TAC[EMBEDDING_MAP_IMP_HOMEOMORPHIC_SPACE;
                HOMEOMORPHIC_METRIZABLE_SPACE;
                METRIZABLE_SPACE_SUBTOPOLOGY;
                METRIZABLE_PRODUCT_UNIT_INTERVAL]);;

(* Combined form *)
let URYSOHN_METRIZATION = prove
 (`!top:A topology.
        second_countable top
        ==> (regular_space top /\ hausdorff_space top <=>
             metrizable_space top)`,
  MESON_TAC[URYSOHN_METRIZATION_FWD; URYSOHN_METRIZATION_BWD]);;

(* Helper: continuous map image in topspace *)
let CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE = prove
 (`!top top' (f:A->B).
        continuous_map (top,top') f
        ==> IMAGE f (topspace top) SUBSET topspace top'`,
  SIMP_TAC[CONTINUOUS_MAP]);;
