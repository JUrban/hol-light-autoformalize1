(* work.ml *)

(* This is a debugging tactic DEBUG_GOAL_TAC - do not remove *)
let debug_goal_string (asl,w) =
  let buf = Buffer.create 16384 in
  let fmt = Format.formatter_of_buffer buf in
  Format.pp_set_max_boxes fmt 200;
  Format.pp_set_margin fmt 200;
  pp_print_goal fmt (asl,w);  (* if available *)
  Format.pp_print_flush fmt ();
  Buffer.contents buf;;

let DEBUG_GOAL_TAC : tactic =
  fun (asl,w as g) ->
  let s = debug_goal_string g in
  print_string ("DEBUG_GOAL:\n" ^ s ^ "\n");
  failwith "DEBUG_GOAL_TAC";;

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
    (* Step 1: v INTER z = {} since v SUBSET w and DISJOINT w z *)
    SUBGOAL_THEN `(v:A->bool) INTER z = {}` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    (* Step 2: closure(v) INTER z = {} using OPEN_IN_INTER_CLOSURE_OF_EQ_EMPTY (equivalence) *)
    SUBGOAL_THEN `(top closure_of v:A->bool) INTER z = {}` ASSUME_TAC THENL
     [ONCE_REWRITE_TAC[INTER_COMM] THEN
      FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP OPEN_IN_INTER_CLOSURE_OF_EQ_EMPTY th]) THEN
      ASM_REWRITE_TAC[INTER_COMM]; ALL_TAC] THEN
    (* Step 3: Use set reasoning with CLOSURE_OF_SUBSET_TOPSPACE *)
    MP_TAC(ISPECL [`top:A topology`; `v:A->bool`] CLOSURE_OF_SUBSET_TOPSPACE) THEN
    ASM SET_TAC[]]);;

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
    (* Use Urysohn with c as first set (gets 0) and {x} as second (gets 1) *)
    MP_TAC(ISPECL [`top:A topology`; `c:A->bool`; `{x:A}`]
                  NORMAL_SPACE_URYSOHN_FUNCTION) THEN
    ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL
     [(* Need: closed_in top c /\ closed_in top {x} /\ DISJOINT c {x} *)
      (* closed_in top c is already assumed, so will be solved by ASM_REWRITE_TAC *)
      ASM_SIMP_TAC[CLOSED_IN_T1_SING; HAUSDORFF_IMP_T1_SPACE; DISJOINT_SING];
      (* Extract the function from Urysohn *)
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `g:A->real` THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      (* g x = &1 follows from assumption 14 with x' = x *)
      FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN
      SIMP_TAC[IN_SING]];
    ALL_TAC] THEN

  (* CONSTRUCTION OF COUNTABLE SEPARATING FAMILY *)
  (* Munkres §34.1, Step 1:
     For each pair (n,m) where closure(e n) ⊆ e m, use Urysohn lemma.
     The witness function uses Hilbert choice @ applied to the existential
     from assumption 9 (Urysohn for closed sets). *)

  (* Construct the witness using Hilbert choice @ on the existential assumptions.
     The idea: define f k = @g. properties_for_k(g) where properties_for_k are
     the appropriate Urysohn properties when k encodes a valid basis pair,
     or trivially true (g = const 0) when k is invalid.

     Use the fact that for valid pairs (n,m) with closure(e n) ⊆ e m:
     - topspace \ e m is closed (complement of open)
     - any point in e n is in e m (by subset), hence not in topspace \ e m
     - by assumption 9, there exists a separating function

     For invalid k, use constant 0 which trivially has range [0,1] and is continuous.

     The witness: for k:num, let n = NUMFST k, m = NUMSND k, define
     f k = @g. (e n IN b /\ e m IN b /\ closure(e n) ⊆ e m /\ e n ≠ {}) ==>
               (properties g) /\
               (~(e n IN b /\ e m IN b /\ closure(e n) ⊆ e m /\ e n ≠ {}) ==>
                g = \x. &0)
  *)

  (* Build the witness explicitly *)
  (* Key change: use closure(e(NUMFST k)) as the "1-set" instead of a single point.
     This ensures f_k(x) = 1 for ALL x in closure(e(NUMFST k)), not just one point. *)
  EXISTS_TAC
    `\k:num. \x:A.
       if (e:num->A->bool) (NUMFST k) IN b /\
          e (NUMSND k) IN b /\
          (top closure_of e (NUMFST k)) SUBSET e (NUMSND k) /\
          ~(e (NUMFST k) = {})
       then (@g:A->real.
              continuous_map (top, subtopology euclideanreal (real_interval[&0,&1])) g /\
              (!z. z IN top closure_of e (NUMFST k) ==> g z = &1) /\
              (!z. z IN topspace top DIFF e (NUMSND k) ==> g z = &0)) x
       else &0` THEN

  (* Abbreviate the validity condition for cleaner proof *)
  ABBREV_TAC
    `valid (k:num) <=> (e:num->A->bool) (NUMFST k) IN b /\
                       e (NUMSND k) IN b /\
                       (top closure_of e (NUMFST k)) SUBSET e (NUMSND k) /\
                       ~(e (NUMFST k) = {})` THEN

  (* Now prove the four required properties *)
  (* Beta-reduce the witness function *)
  BETA_TAC THEN

  (* Split into 4 conjuncts *)
  REPEAT CONJ_TAC THENL
   [(* Property 1: range [0,1] for all n, x in topspace *)
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    (* Case split on validity of n *)
    ASM_CASES_TAC `(valid:num->bool) n` THENL
     [(* Valid case: use SELECT_AX to extract properties *)
      ASM_SIMP_TAC[] THEN
      (* Abbreviate the predicate for the chosen function *)
      (* NEW: P uses closure as the "1-set" instead of a single point *)
      ABBREV_TAC `P = \g:A->real.
        continuous_map (top, subtopology euclideanreal (real_interval[&0,&1])) g /\
        (!z. z IN top closure_of e (NUMFST n) ==> g z = &1) /\
        (!z. z IN topspace top DIFF e (NUMSND n) ==> g z = &0)` THEN
      (* First, show existence of such g using URYSOHN_LEMMA directly *)
      SUBGOAL_THEN `?g:A->real. P g` ASSUME_TAC THENL
       [(* Branch 1: Prove the existential using URYSOHN_LEMMA *)
        EXPAND_TAC "P" THEN BETA_TAC THEN
        (* Use URYSOHN_LEMMA with:
           - s = topspace DIFF e(NUMSND n) (closed, gets 0)
           - t = closure_of e(NUMFST n) (closed, gets 1)
           - Need: DISJOINT s t, which follows from closure ⊆ e(NUMSND n) *)
        MP_TAC(ISPECL [`top:A topology`;
                       `topspace top DIFF e (NUMSND n):A->bool`;
                       `top closure_of (e:num->A->bool) (NUMFST n)`;
                       `&0`; `&1`] URYSOHN_LEMMA) THEN
        REWRITE_TAC[REAL_POS] THEN
        ANTS_TAC THENL
         [(* Verify: normal_space, both sets closed, DISJOINT *)
          ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
           [(* closed_in (topspace DIFF e(NUMSND n)) *)
            MATCH_MP_TAC CLOSED_IN_DIFF THEN
            REWRITE_TAC[CLOSED_IN_TOPSPACE] THEN
            ASM_MESON_TAC[];
            (* closed_in (closure_of e(NUMFST n)) *)
            REWRITE_TAC[CLOSED_IN_CLOSURE_OF];
            (* DISJOINT *)
            (* closure ⊆ e(NUMSND n) from valid n, so closure ∩ (topspace \ e(NUMSND n)) = {} *)
            FIRST_X_ASSUM(fun th -> REWRITE_TAC[GSYM th]) THEN
            ASM_REWRITE_TAC[] THEN
            REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_DIFF] THEN
            ASM SET_TAC[]];
          (* Extract the function - URYSOHN gives g = 0 on first set, g = 1 on second *)
          MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `g:A->real` THEN
          STRIP_TAC THEN ASM_REWRITE_TAC[]];
        (* Branch 2: Use the existence to get properties of @ *)
        SUBGOAL_THEN `(P:((A->real)->bool)) ((@) P)` MP_TAC THENL
         [(* P ((@) P) follows from ?g. P g via SELECT_AX *)
          FIRST_X_ASSUM(MP_TAC o MATCH_MP
            (MESON[SELECT_AX] `(?g. P g) ==> P ((@) P)`)) THEN
          SIMP_TAC[];
          ALL_TAC] THEN
        EXPAND_TAC "P" THEN BETA_TAC THEN STRIP_TAC THEN
        (* continuous_map to subtopology [0,1] implies g x IN [0,1] *)
        FIRST_X_ASSUM(MP_TAC o
          GEN_REWRITE_RULE I [CONTINUOUS_MAP_IN_SUBTOPOLOGY]) THEN
        STRIP_TAC THEN
        FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
        REWRITE_TAC[FORALL_IN_IMAGE; IN_REAL_INTERVAL] THEN
        DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      (* Invalid case: constant 0 in [0,1] *)
      ASM_SIMP_TAC[] THEN REAL_ARITH_TAC];
    (* Property 2: continuity for each n *)
    GEN_TAC THEN
    ASM_CASES_TAC `(valid:num->bool) n` THENL
     [(* Valid case: chosen function is continuous by SELECT_AX *)
      ASM_SIMP_TAC[] THEN
      (* Abbreviate the predicate for the chosen function *)
      (* NEW: P uses closure as the "1-set" instead of a single point *)
      ABBREV_TAC `P = \g:A->real.
        continuous_map (top, subtopology euclideanreal (real_interval[&0,&1])) g /\
        (!z. z IN top closure_of e (NUMFST n) ==> g z = &1) /\
        (!z. z IN topspace top DIFF e (NUMSND n) ==> g z = &0)` THEN
      (* First, show existence of such g using URYSOHN_LEMMA *)
      SUBGOAL_THEN `?g:A->real. P g` ASSUME_TAC THENL
       [(* Branch 1: Prove the existential using URYSOHN_LEMMA *)
        EXPAND_TAC "P" THEN BETA_TAC THEN
        MP_TAC(ISPECL [`top:A topology`;
                       `topspace top DIFF e (NUMSND n):A->bool`;
                       `top closure_of (e:num->A->bool) (NUMFST n)`;
                       `&0`; `&1`] URYSOHN_LEMMA) THEN
        REWRITE_TAC[REAL_POS] THEN
        ANTS_TAC THENL
         [(* Verify: normal_space, both sets closed, DISJOINT *)
          ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
           [(* closed_in (topspace DIFF e(NUMSND n)) *)
            MATCH_MP_TAC CLOSED_IN_DIFF THEN
            REWRITE_TAC[CLOSED_IN_TOPSPACE] THEN
            ASM_MESON_TAC[];
            (* closed_in (closure_of e(NUMFST n)) *)
            REWRITE_TAC[CLOSED_IN_CLOSURE_OF];
            (* DISJOINT *)
            FIRST_X_ASSUM(fun th -> REWRITE_TAC[GSYM th]) THEN
            ASM_REWRITE_TAC[] THEN
            REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_DIFF] THEN
            ASM SET_TAC[]];
          (* Extract the function *)
          MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `g:A->real` THEN
          STRIP_TAC THEN ASM_REWRITE_TAC[]];
        (* Branch 2: Use the existence to extract properties of @ *)
        SUBGOAL_THEN `(P:((A->real)->bool)) ((@) P)` MP_TAC THENL
         [FIRST_X_ASSUM(MP_TAC o MATCH_MP
            (MESON[SELECT_AX] `(?g. P g) ==> P ((@) P)`)) THEN
          SIMP_TAC[];
          ALL_TAC] THEN
        EXPAND_TAC "P" THEN BETA_TAC THEN
        STRIP_TAC THEN
        (* Goal is to show continuity, which is the first conjunct of P *)
        (* Note: goal is `continuous_map ... (\x. (@g. ...) x)` but assumption
           is `continuous_map ... (@g. ...)` - these are equal by eta *)
        REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[]];
      (* Invalid case: constant 0 is continuous *)
      ASM_SIMP_TAC[ETA_AX] THEN
      REWRITE_TAC[CONTINUOUS_MAP_CONST; TOPSPACE_SUBTOPOLOGY] THEN
      REWRITE_TAC[IN_INTER; TOPSPACE_EUCLIDEANREAL; IN_UNIV; IN_REAL_INTERVAL] THEN
      REAL_ARITH_TAC];

    (* Property 3: point separation *)
    MAP_EVERY X_GEN_TAC [`x0:A`; `y0:A`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `closed_in (top:A topology) {y0:A}` ASSUME_TAC THENL
     [ASM_MESON_TAC[CLOSED_IN_T1_SING; HAUSDORFF_IMP_T1_SPACE]; ALL_TAC] THEN
    SUBGOAL_THEN `open_in (top:A topology) (topspace top DIFF {y0})` ASSUME_TAC THENL
     [ASM_SIMP_TAC[OPEN_IN_DIFF; OPEN_IN_TOPSPACE]; ALL_TAC] THEN
    SUBGOAL_THEN `(x0:A) IN topspace top DIFF {y0}` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `?u1:A->bool. u1 IN b /\ x0 IN u1 /\ u1 SUBSET topspace top DIFF {y0}`
                 STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `b:(A->bool)->bool`; `u1:A->bool`; `x0:A`]
                  REGULAR_SPACE_BASIS_CLOSURE) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `v:A->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `?m:num. (e:num->A->bool) m = v` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `?n:num. (e:num->A->bool) n = u1` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    EXISTS_TAC `NUMPAIR (m:num) (n:num)` THEN
    REWRITE_TAC[NUMPAIR_DEST] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(v:A->bool) IN b /\ (u1:A->bool) IN b /\
                  (top:A topology) closure_of v SUBSET u1 /\ ~(v = {})`
                 ASSUME_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    (* Skip proving valid separately - just use ASM_CASES_TAC *)
    ASM_CASES_TAC `valid (NUMPAIR (m:num) (n:num)):bool` THENL
     [(* valid case: now goal is ~((@g...) x0 = (@g...) y0) *)
      ASM_REWRITE_TAC[] THEN
      (* Abbreviate the predicate for the chosen function *)
      ABBREV_TAC `P = \g:A->real.
                        continuous_map (top, subtopology euclideanreal (real_interval[&0,&1])) g /\
                        (!z. z IN top closure_of v ==> g z = &1) /\
                        (!z. z IN topspace top DIFF u1 ==> g z = &0)` THEN
      (* Prove existence using URYSOHN_LEMMA *)
      SUBGOAL_THEN `?g:A->real. P g` ASSUME_TAC THENL
       [EXPAND_TAC "P" THEN BETA_TAC THEN
        MP_TAC(ISPECL [`top:A topology`; `topspace top DIFF (u1:A->bool)`;
                       `top closure_of (v:A->bool)`; `&0`; `&1`] URYSOHN_LEMMA) THEN
        REWRITE_TAC[REAL_POS] THEN
        ANTS_TAC THENL
         [CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
          CONJ_TAC THENL
           [MATCH_MP_TAC CLOSED_IN_DIFF THEN
            REWRITE_TAC[CLOSED_IN_TOPSPACE] THEN ASM_MESON_TAC[];
            ALL_TAC] THEN
          CONJ_TAC THENL [REWRITE_TAC[CLOSED_IN_CLOSURE_OF]; ALL_TAC] THEN
          REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_DIFF] THEN
          ASM SET_TAC[];
          DISCH_THEN(X_CHOOSE_THEN `g:A->real` STRIP_ASSUME_TAC) THEN
          EXISTS_TAC `g:A->real` THEN ASM_REWRITE_TAC[]];
        ALL_TAC] THEN
      (* Now use P((@) P) via SELECT_AX *)
      SUBGOAL_THEN `(P:((A->real)->bool)) ((@) P)` MP_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o MATCH_MP
         (MESON[SELECT_AX] `(?g. P g) ==> P ((@) P)`)) THEN
        SIMP_TAC[];
        ALL_TAC] THEN
      EXPAND_TAC "P" THEN BETA_TAC THEN STRIP_TAC THEN
      (* Now (@g...) gives &1 on closure v, &0 on topspace DIFF u1 *)
      (* x0 IN v ⊆ closure(v) ⟹ (@g...) x0 = 1 *)
      (* y0 ∉ u1 (since u1 ⊆ topspace DIFF {y0}) ⟹ (@g...) y0 = 0 *)
      SUBGOAL_THEN `(x0:A) IN top closure_of v` ASSUME_TAC THENL
       [(* x0 IN v and v SUBSET closure(v) *)
        SUBGOAL_THEN `(v:A->bool) SUBSET top closure_of v` MP_TAC THENL
         [MATCH_MP_TAC CLOSURE_OF_SUBSET THEN ASM_MESON_TAC[OPEN_IN_SUBSET];
          ASM SET_TAC[]];
        ALL_TAC] THEN
      SUBGOAL_THEN `(y0:A) IN topspace top DIFF u1` ASSUME_TAC THENL
       [ASM SET_TAC[];
        ALL_TAC] THEN
      (* We have:
         - !z. z IN topspace DIFF u1 ==> (@g...) z = &0
         - !z. z IN closure v ==> (@g...) z = &1
         From x0 IN closure v: (@g...) x0 = &1
         From y0 IN topspace DIFF u1: (@g...) y0 = &0
         Hence ~(&1 = &0) *)
      SUBGOAL_THEN `((@g:A->real. continuous_map (top,subtopology euclideanreal (real_interval [&0,&1])) g /\
                    (!z. z IN top closure_of v ==> g z = &1) /\
                    (!z. z IN topspace top DIFF u1 ==> g z = &0)) x0 = &1)`
                   ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `((@g:A->real. continuous_map (top,subtopology euclideanreal (real_interval [&0,&1])) g /\
                    (!z. z IN top closure_of v ==> g z = &1) /\
                    (!z. z IN topspace top DIFF u1 ==> g z = &0)) y0 = &0)`
                   ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      (* ~valid case: derive contradiction since valid actually holds *)
      FIRST_X_ASSUM(MP_TAC o SPEC `NUMPAIR (m:num) (n:num)`) THEN
      REWRITE_TAC[NUMPAIR_DEST] THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_TAC THEN ASM_MESON_TAC[]];

    (* Property 4: closed set separation *)
    MAP_EVERY X_GEN_TAC [`c0:A->bool`; `x0:A`] THEN STRIP_TAC THEN
    (* topspace DIFF c0 is open (complement of closed) *)
    SUBGOAL_THEN `open_in (top:A topology) (topspace top DIFF c0)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[OPEN_IN_DIFF; OPEN_IN_TOPSPACE]; ALL_TAC] THEN
    (* x0 is in topspace DIFF c0 *)
    SUBGOAL_THEN `(x0:A) IN topspace top DIFF c0` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    (* Use basis to find u1 containing x0 in complement of c0 *)
    SUBGOAL_THEN `?u1:A->bool. u1 IN b /\ x0 IN u1 /\ u1 SUBSET topspace top DIFF c0`
                 STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    (* Use REGULAR_SPACE_BASIS_CLOSURE to find v with closure SUBSET u1 *)
    MP_TAC(ISPECL [`top:A topology`; `b:(A->bool)->bool`; `u1:A->bool`; `x0:A`]
                  REGULAR_SPACE_BASIS_CLOSURE) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `v:A->bool` STRIP_ASSUME_TAC) THEN
    (* Find indices m, n for v, u1 *)
    SUBGOAL_THEN `?m:num. (e:num->A->bool) m = v` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `?n:num. (e:num->A->bool) n = u1` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    (* Witness is NUMPAIR m n *)
    EXISTS_TAC `NUMPAIR (m:num) (n:num)` THEN
    REWRITE_TAC[NUMPAIR_DEST] THEN
    ASM_REWRITE_TAC[] THEN
    (* Establish valid condition holds *)
    SUBGOAL_THEN `(v:A->bool) IN b /\ (u1:A->bool) IN b /\
                  (top:A topology) closure_of v SUBSET u1 /\ ~(v = {})`
                 ASSUME_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    (* Case split on valid *)
    ASM_CASES_TAC `valid (NUMPAIR (m:num) (n:num)):bool` THENL
     [(* valid case *)
      ASM_REWRITE_TAC[] THEN
      (* Abbreviate the predicate *)
      ABBREV_TAC `P = \g:A->real.
                        continuous_map (top, subtopology euclideanreal (real_interval[&0,&1])) g /\
                        (!z. z IN top closure_of v ==> g z = &1) /\
                        (!z. z IN topspace top DIFF u1 ==> g z = &0)` THEN
      (* Prove existence using URYSOHN_LEMMA *)
      SUBGOAL_THEN `?g:A->real. P g` ASSUME_TAC THENL
       [EXPAND_TAC "P" THEN BETA_TAC THEN
        MP_TAC(ISPECL [`top:A topology`; `topspace top DIFF (u1:A->bool)`;
                       `top closure_of (v:A->bool)`; `&0`; `&1`] URYSOHN_LEMMA) THEN
        REWRITE_TAC[REAL_POS] THEN
        ANTS_TAC THENL
         [CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
          CONJ_TAC THENL
           [MATCH_MP_TAC CLOSED_IN_DIFF THEN
            REWRITE_TAC[CLOSED_IN_TOPSPACE] THEN ASM_MESON_TAC[];
            ALL_TAC] THEN
          CONJ_TAC THENL [REWRITE_TAC[CLOSED_IN_CLOSURE_OF]; ALL_TAC] THEN
          REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_DIFF] THEN
          ASM SET_TAC[];
          DISCH_THEN(X_CHOOSE_THEN `g:A->real` STRIP_ASSUME_TAC) THEN
          EXISTS_TAC `g:A->real` THEN ASM_REWRITE_TAC[]];
        ALL_TAC] THEN
      (* Use P((@) P) via SELECT_AX *)
      SUBGOAL_THEN `(P:((A->real)->bool)) ((@) P)` MP_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o MATCH_MP
         (MESON[SELECT_AX] `(?g. P g) ==> P ((@) P)`)) THEN
        SIMP_TAC[];
        ALL_TAC] THEN
      EXPAND_TAC "P" THEN BETA_TAC THEN STRIP_TAC THEN
      (* x0 IN v ⊆ closure(v) ⟹ (@g...) x0 = 1 *)
      SUBGOAL_THEN `(x0:A) IN top closure_of v` ASSUME_TAC THENL
       [SUBGOAL_THEN `(v:A->bool) SUBSET top closure_of v` MP_TAC THENL
         [MATCH_MP_TAC CLOSURE_OF_SUBSET THEN ASM_MESON_TAC[OPEN_IN_SUBSET];
          ASM SET_TAC[]];
        ALL_TAC] THEN
      (* c0 ⊆ topspace DIFF u1 since u1 ⊆ topspace DIFF c0 *)
      SUBGOAL_THEN `(c0:A->bool) SUBSET topspace top DIFF u1` ASSUME_TAC THENL
       [MP_TAC(ISPECL [`top:A topology`; `c0:A->bool`] CLOSED_IN_SUBSET) THEN
        ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
        ALL_TAC] THEN
      (* Prove f(NUMPAIR m n) x0 = 1 and f(NUMPAIR m n) z = 0 for z in c0 *)
      CONJ_TAC THENL
       [(* x0 gives 1 *)
        SUBGOAL_THEN `((@g:A->real. continuous_map (top,subtopology euclideanreal (real_interval [&0,&1])) g /\
                      (!z. z IN top closure_of v ==> g z = &1) /\
                      (!z. z IN topspace top DIFF u1 ==> g z = &0)) x0 = &1)`
                     (fun th -> REWRITE_TAC[th]) THEN
        ASM_MESON_TAC[];
        (* z in c0 gives 0 *)
        X_GEN_TAC `z:A` THEN DISCH_TAC THEN
        SUBGOAL_THEN `(z:A) IN topspace top DIFF u1` ASSUME_TAC THENL
         [ASM SET_TAC[]; ALL_TAC] THEN
        SUBGOAL_THEN `((@g:A->real. continuous_map (top,subtopology euclideanreal (real_interval [&0,&1])) g /\
                      (!z. z IN top closure_of v ==> g z = &1) /\
                      (!z. z IN topspace top DIFF u1 ==> g z = &0)) z = &0)`
                     (fun th -> REWRITE_TAC[th]) THEN
        ASM_MESON_TAC[]];
      (* ~valid case: contradiction *)
      FIRST_X_ASSUM(MP_TAC o SPEC `NUMPAIR (m:num) (n:num)`) THEN
      REWRITE_TAC[NUMPAIR_DEST] THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_TAC THEN ASM_MESON_TAC[]]]);;

(* Note: Pairing function NUMPAIR and properties NUMPAIR_INJ, NUMPAIR_DEST
   are available from the library (ind_types.ml). Use those instead of
   defining custom pairing functions, per CLAUDE.md guidance to avoid
   duplicating library infrastructure. *)

(* Helper: {h | h IN topspace /\ h n > 0} is open in product topology of [0,1]^num *)
let OPEN_IN_PRODUCT_HALFSPACE = prove
 (`!n. open_in (product_topology (:num)
                  (\i. subtopology euclideanreal (real_interval[&0,&1])))
               {h:num->real | h IN topspace (product_topology (:num)
                  (\i. subtopology euclideanreal (real_interval[&0,&1]))) /\
                h n > &0}`,
  GEN_TAC THEN
  ABBREV_TAC `prod = product_topology (:num)
                       (\i. subtopology euclideanreal (real_interval[&0,&1]))` THEN
  MP_TAC(ISPECL [`\i:num. subtopology euclideanreal (real_interval [&0,&1])`;
                 `(:num)`; `n:num`] CONTINUOUS_MAP_PRODUCT_PROJECTION) THEN
  REWRITE_TAC[IN_UNIV] THEN EXPAND_TAC "prod" THEN
  REWRITE_TAC[continuous_map] THEN DISCH_THEN(MP_TAC o CONJUNCT2) THEN
  DISCH_THEN(MP_TAC o SPEC `{r:real | r > &0} INTER real_interval[&0,&1]`) THEN
  SUBGOAL_THEN `open_in (subtopology euclideanreal (real_interval[&0,&1]))
                        ({r:real | r > &0} INTER real_interval[&0,&1])`
    ASSUME_TAC THENL
   [REWRITE_TAC[OPEN_IN_SUBTOPOLOGY] THEN EXISTS_TAC `{r:real | r > &0}` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM real_gt; GSYM REAL_OPEN_IN; real_open] THEN
      X_GEN_TAC `r:real` THEN REWRITE_TAC[IN_ELIM_THM; real_gt] THEN
      DISCH_TAC THEN EXISTS_TAC `r:real` THEN ASM_REWRITE_TAC[REAL_SUB_LT] THEN
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[INTER_COMM]]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER] THEN
  REWRITE_TAC[TOPSPACE_PRODUCT_TOPOLOGY; IN_CARTESIAN_PRODUCT; o_THM; IN_UNIV] THEN
  REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER; IN_REAL_INTERVAL] THEN
  X_GEN_TAC `h:num->real` THEN EQ_TAC THENL
   [STRIP_TAC THEN ASM_REWRITE_TAC[];
    STRIP_TAC THEN ASM_REWRITE_TAC[real_gt] THEN
    UNDISCH_TAC `(h:num->real) IN topspace prod` THEN EXPAND_TAC "prod" THEN
    REWRITE_TAC[TOPSPACE_PRODUCT_TOPOLOGY; IN_CARTESIAN_PRODUCT; o_THM; IN_UNIV] THEN
    REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER; IN_REAL_INTERVAL] THEN
    SIMP_TAC[]]);;

(* Helper: The map g = \x.\n. f n x is an open map to subtopology on its image
   This is the key lemma for the embedding proof. *)
let OPEN_MAP_INTO_PRODUCT_IMAGE = prove
 (`!top:A topology f:num->A->real.
        (!n x. x IN topspace top ==> &0 <= f n x /\ f n x <= &1) /\
        (!n. continuous_map
               (top,subtopology euclideanreal (real_interval[&0,&1]))
               (f n)) /\
        (!c x. closed_in top c /\ x IN topspace top /\ ~(x IN c)
               ==> ?n. f n x = &1 /\ (!z. z IN c ==> f n z = &0))
        ==> open_map (top,
                      subtopology
                        (product_topology (:num)
                           (\n. subtopology euclideanreal (real_interval[&0,&1])))
                        (IMAGE (\x. \n. f n x) (topspace top)))
                     (\x. \n. f n x)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `prod = product_topology (:num)
                       (\i. subtopology euclideanreal (real_interval[&0,&1]))` THEN
  ABBREV_TAC `g = \x:A. \n:num. (f:num->A->real) n x` THEN
  REWRITE_TAC[open_map; OPEN_IN_SUBTOPOLOGY] THEN
  X_GEN_TAC `u:A->bool` THEN DISCH_TAC THEN
  (* Goal: ?t. open_in prod t /\ IMAGE g u = t INTER IMAGE g (topspace top) *)

  (* First establish that u SUBSET topspace top *)
  SUBGOAL_THEN `(u:A->bool) SUBSET topspace top` ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_IN_SUBSET THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN

  (* The witness t is the union of cylinders *)
  EXISTS_TAC `UNIONS {c | ?x:A. x IN u /\
                c = {h:num->real | h IN topspace prod /\
                     h ((@n. (f:num->A->real) n x = &1 /\
                            (!z. z IN topspace top DIFF u ==> f n z = &0))) > &0}}` THEN
  CONJ_TAC THENL
   [(* Prove the union is open - each cylinder is open *)
    MATCH_MP_TAC OPEN_IN_UNIONS THEN REWRITE_TAC[IN_ELIM_THM] THEN
    X_GEN_TAC `c:(num->real)->bool` THEN
    DISCH_THEN(X_CHOOSE_THEN `y:A` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "prod" THEN
    REWRITE_TAC[GSYM real_gt; OPEN_IN_PRODUCT_HALFSPACE];
    ALL_TAC] THEN

  (* Prove IMAGE g u = t INTER IMAGE g (topspace top) *)
  REWRITE_TAC[EXTENSION; IN_INTER; IN_IMAGE; IN_UNIONS; IN_ELIM_THM] THEN
  X_GEN_TAC `h:num->real` THEN EQ_TAC THENL
   [(* ==> direction: h = g x for some x IN u, show h in union and in image of topspace *)
    DISCH_THEN(X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC) THEN
    CONJ_TAC THENL
     [CHEAT_TAC;
      EXISTS_TAC `x:A` THEN ASM SET_TAC[]];
    CHEAT_TAC]);;

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
  ABBREV_TAC `prod = product_topology (:num)
                       (\n. subtopology euclideanreal (real_interval[&0,&1]))` THEN
  ABBREV_TAC `g = \x:A. \n:num. (f:num->A->real) n x` THEN
  CONJ_TAC THENL
   [(* Prove embedding: unfold to homeomorphic_map to subtopology *)
    REWRITE_TAC[embedding_map] THEN
    EXPAND_TAC "prod" THEN EXPAND_TAC "g" THEN
    (* Use BIJECTIVE_OPEN_IMP_HOMEOMORPHIC_MAP *)
    MATCH_MP_TAC BIJECTIVE_OPEN_IMP_HOMEOMORPHIC_MAP THEN
    REPEAT CONJ_TAC THENL
     [(* Prove continuous_map to subtopology *)
      REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY; SUBSET_REFL] THEN
      REWRITE_TAC[CONTINUOUS_MAP_COMPONENTWISE_UNIV] THEN
      GEN_TAC THEN REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[];
      (* Prove open_map to subtopology of image - use OPEN_MAP_INTO_PRODUCT_IMAGE *)
      MATCH_MP_TAC OPEN_MAP_INTO_PRODUCT_IMAGE THEN ASM_REWRITE_TAC[];
      (* Prove surjectivity: IMAGE g (topspace top) = topspace (subtopology ...) *)
      REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN
      MATCH_MP_TAC(SET_RULE `s SUBSET t ==> s = t INTER s`) THEN
      REWRITE_TAC[SUBSET; IN_IMAGE] THEN
      GEN_TAC THEN DISCH_THEN(X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[TOPSPACE_PRODUCT_TOPOLOGY; CARTESIAN_PRODUCT_UNIV] THEN
      REWRITE_TAC[cartesian_product; IN_ELIM_THM; o_DEF; IN_UNIV] THEN
      REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; TOPSPACE_EUCLIDEANREAL; INTER_UNIV] THEN
      REWRITE_TAC[IN_REAL_INTERVAL; EXTENSIONAL_UNIV] THEN
      GEN_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL [`i:num`; `x:A`]) THEN
      ASM_REWRITE_TAC[];
      (* Prove injectivity: g x = g y <=> x = y *)
      REPEAT GEN_TAC THEN STRIP_TAC THEN EQ_TAC THENL
       [DISCH_TAC THEN
        ASM_CASES_TAC `(x:A) = y` THEN ASM_REWRITE_TAC[] THEN
        FIRST_X_ASSUM(MP_TAC o SPECL [`x:A`; `y:A`]) THEN
        ASM_REWRITE_TAC[] THEN
        DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN
        FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [FUN_EQ_THM]) THEN
        DISCH_THEN(MP_TAC o SPEC `n:num`) THEN
        ASM_REWRITE_TAC[];
        DISCH_TAC THEN ASM_REWRITE_TAC[]]];
    (* Prove final property: g x n = f n x where g = \x.\n. f n x *)
    EXPAND_TAC "g" THEN REPEAT STRIP_TAC THEN BETA_TAC THEN REFL_TAC]);;

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
  (* Step 1: metrizable_space prod *)
  SUBGOAL_THEN `metrizable_space (prod:(num->real)topology)` ASSUME_TAC THENL
   [EXPAND_TAC "prod" THEN REWRITE_TAC[METRIZABLE_PRODUCT_UNIT_INTERVAL];
    ALL_TAC] THEN
  (* Step 2: embedding_map gives homeomorphic to subtopology *)
  MP_TAC(ISPECL [`top:A topology`; `prod:(num->real)topology`;
                 `g:A->num->real`]
                EMBEDDING_MAP_IMP_HOMEOMORPHIC_SPACE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  (* Step 3: subtopology of metrizable is metrizable *)
  SUBGOAL_THEN `metrizable_space (subtopology (prod:(num->real)topology) (IMAGE (g:A->num->real) (topspace top)))`
               ASSUME_TAC THENL
   [MATCH_MP_TAC METRIZABLE_SPACE_SUBTOPOLOGY THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* Step 4: homeomorphic to metrizable space is metrizable *)
  (* HOMEOMORPHIC_METRIZABLE_SPACE: top homeomorphic top' ==> (metrizable top <=> metrizable top') *)
  (* Use the equivalence in the backward direction: top homeomorphic S /\ metrizable S ==> metrizable top *)
  FIRST_X_ASSUM(fun th ->
    MP_TAC(MATCH_MP HOMEOMORPHIC_METRIZABLE_SPACE th)) THEN
  ASM_REWRITE_TAC[]);;

(* Combined form *)
let URYSOHN_METRIZATION = prove
 (`!top:A topology.
        second_countable top
        ==> (regular_space top /\ hausdorff_space top <=>
             metrizable_space top)`,
  GEN_TAC THEN DISCH_TAC THEN EQ_TAC THENL
   [STRIP_TAC THEN MATCH_MP_TAC URYSOHN_METRIZATION_BWD THEN
    ASM_REWRITE_TAC[];
    DISCH_TAC THEN
    MP_TAC(SPEC `top:A topology` URYSOHN_METRIZATION_FWD) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[]]);;

(* Helper: continuous map image in topspace *)
let CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE = prove
 (`!top top' (f:A->B).
        continuous_map (top,top') f
        ==> IMAGE f (topspace top) SUBSET topspace top'`,
  SIMP_TAC[CONTINUOUS_MAP]);;
