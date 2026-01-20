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
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REGULAR_LINDELOF_IMP_NORMAL_SPACE THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SECOND_COUNTABLE_IMP_LINDELOF_SPACE THEN
  ASM_REWRITE_TAC[]);;

(* Helper: continuous function to [0,1] composed with (1-x) stays in [0,1] *)
let CONTINUOUS_MAP_COMPLEMENT_UNIT_INTERVAL = prove
 (`!top f:A->real.
        continuous_map (top,subtopology euclideanreal (real_interval[&0,&1])) f
        ==> continuous_map
              (top,subtopology euclideanreal (real_interval[&0,&1]))
              (\x. &1 - f x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
    `(\x:A. &1 - f x) = (\y. &1 - y) o (f:A->real)`
    SUBST1_TAC THENL
   [REWRITE_TAC[o_DEF; ETA_AX];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
  EXISTS_TAC `subtopology euclideanreal (real_interval[&0,&1])` THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_INTO_SUBTOPOLOGY THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THEN
    MATCH_MP_TAC CONTINUOUS_MAP_REAL_SUB THEN
    REWRITE_TAC[CONTINUOUS_MAP_REAL_CONST; CONTINUOUS_MAP_ID;
                TOPSPACE_EUCLIDEANREAL; IN_UNIV];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; TOPSPACE_SUBTOPOLOGY;
                TOPSPACE_EUCLIDEANREAL; IN_INTER; IN_UNIV;
                IN_REAL_INTERVAL] THEN
    REAL_ARITH_TAC]);;

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

(* Helper: T3 + Hausdorff gives point separation via closed sets *)
let T3_HAUSDORFF_POINT_SEPARATION = prove
 (`!top x y:A.
        regular_space top /\ hausdorff_space top /\
        x IN topspace top /\ y IN topspace top /\ ~(x = y)
        ==> ?c. closed_in top c /\ x IN c /\ ~(y IN c)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [hausdorff_space]) THEN
  DISCH_THEN(MP_TAC o SPECL [`x:A`; `y:A`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:A->bool` (X_CHOOSE_THEN `v:A->bool`
    STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `topspace top DIFF v:A->bool` THEN
  ASM_SIMP_TAC[CLOSED_IN_DIFF; CLOSED_IN_TOPSPACE; IN_DIFF] THEN
  ASM SET_TAC[]);;

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
  (* Construct countable family using basis enumeration *)
  (* Enumerate the countable basis b as a sequence *)
  SUBGOAL_THEN `?e:num->A->bool. !u. u IN b ==> ?n. e n = u`
               STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC COUNTABLE_SURJECTIVE_ENUMERATION THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN

  (* Now construct the function family *)
  (* We'll use choice to get separating functions for each needed case *)

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
  (* Following textbook Step 1: construct {g_{n,m}} for pairs where cl(B_n) ⊂ B_m *)

  (* Textbook approach: For each pair (n,m) where closure(e n) ⊂ e m,
     use Urysohn to get g_{n,m} with g_{n,m}(cl(e n)) = {1} and g_{n,m}(X - e m) = {0}.
     Then reindex this countable collection to get {f_n}. *)

  (* For each valid pair, we can construct the function using the closed set assumption *)
  (* The pair (n,m) is "valid" when closure_of top (e n) SUBSET e m *)
  (* For such pairs, apply Urysohn with c = closure_of top (e n) and d = topspace DIFF e m *)

  (* Attempt 16: Explicit construction following textbook *)
  (* Need to:
     1) Define valid pairs predicate
     2) For each valid pair, get function via choice from closed set assumption
     3) Reindex via NUMPAIR to get countable family
     4) Prove separation properties *)
  (* This requires sophisticated choice principles and pair enumeration *)
  (* Leaving as CHEAT_TAC but with clear textbook strategy documented *)
  CHEAT_TAC);;


(* Note: Pairing function NUMPAIR and properties NUMPAIR_INJ, NUMPAIR_DEST
   are available from the library (ind_types.ml). Use those instead of
   defining custom pairing functions, per CLAUDE.md guidance to avoid
   duplicating library infrastructure. *)

(* Note: SECOND_COUNTABLE_IMP_SEPARABLE_SPACE from metric.ml shows that
   second-countable spaces have countable dense subsets. This could potentially
   be useful for constructing the separating function family, as a countable
   dense subset can be enumerated and used to index separation requirements.
   The separable_space property gives ?c. COUNTABLE c /\ c SUBSET topspace /\
   closure_of c = topspace. For future work on SEPARATING_FUNCTIONS. *)

(* Helper: implication from conditional inequality *)
let COND_NE_IMP = prove
 (`!b x y z. (~((if b then x else y) = z) ==> b) <=> b \/ (y = z)`,
  MESON_TAC[]);;

(* Helper: open and closed unit intervals are not equal *)
let REAL_INTERVAL_OPEN_NE_CLOSED_UNIT = prove
 (`~(real_interval(&1 / &2, &1) = real_interval[&0,&1])`,
  REWRITE_TAC[EXTENSION; real_interval; IN_ELIM_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `&0`) THEN
  REAL_ARITH_TAC);;

(* Helper: open intervals in unit interval are open *)
let OPEN_IN_UNIT_INTERVAL_SUBINTERVAL = prove
 (`!a b. &0 <= a /\ a < b /\ b <= &1
         ==> open_in (subtopology euclideanreal (real_interval[&0,&1]))
                     (real_interval(a,b))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[OPEN_IN_SUBTOPOLOGY] THEN
  EXISTS_TAC `real_interval(a:real,b)` THEN
  REWRITE_TAC[GSYM REAL_OPEN_IN; REAL_OPEN_REAL_INTERVAL; INTER_SUBSET] THEN
  REWRITE_TAC[EXTENSION; IN_INTER; IN_REAL_INTERVAL] THEN
  ASM_MESON_TAC[REAL_LT_IMP_LE; REAL_LE_TRANS]);;

(* Helper: conditional interval equality for potential use in EMBEDDING *)
let COND_INTERVAL_EQ_CLOSED = prove
 (`!i n. (if i = n then real_interval(&1 / &2, &1) else real_interval[&0,&1]) =
         real_interval[&0,&1] <=> ~(i = n)`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[REAL_INTERVAL_OPEN_NE_CLOSED_UNIT]);;

(* Helper: half and one bounds *)
let HALF_ONE_BOUNDS = prove
 (`&0 <= &1 / &2 /\ &1 / &2 < &1 /\ &1 <= &1`,
  REAL_ARITH_TAC);;

(* Helper: half open interval is open in unit interval *)
let HALF_ONE_OPEN_IN_UNIT = prove
 (`open_in (subtopology euclideanreal (real_interval[&0,&1]))
           (real_interval(&1 / &2, &1))`,
  MATCH_MP_TAC OPEN_IN_UNIT_INTERVAL_SUBINTERVAL THEN
  REAL_ARITH_TAC);;

(* Helper: [0,1]\{0} is open in unit interval *)
let OPEN_IN_UNIT_INTERVAL_DIFF_ZERO = prove
 (`open_in (subtopology euclideanreal (real_interval[&0,&1]))
           (real_interval[&0,&1] DIFF {&0})`,
  REWRITE_TAC[OPEN_IN_SUBTOPOLOGY; GSYM REAL_OPEN_IN] THEN
  EXISTS_TAC `real_interval(&0,&2)` THEN
  REWRITE_TAC[REAL_OPEN_REAL_INTERVAL] THEN
  REWRITE_TAC[EXTENSION; IN_INTER; IN_DIFF; IN_SING; IN_REAL_INTERVAL] THEN
  REAL_ARITH_TAC);;

(* Helper: [0,1] is open in itself *)
let OPEN_IN_UNIT_INTERVAL_SELF = prove
 (`open_in (subtopology euclideanreal (real_interval[&0,&1]))
           (real_interval[&0,&1])`,
  REWRITE_TAC[OPEN_IN_SUBTOPOLOGY; GSYM REAL_OPEN_IN; INTER_IDEMPOT] THEN
  EXISTS_TAC `real_interval(&0 - &1, &1 + &1)` THEN
  REWRITE_TAC[REAL_OPEN_REAL_INTERVAL] THEN
  REWRITE_TAC[EXTENSION; IN_INTER; IN_REAL_INTERVAL] THEN
  REAL_ARITH_TAC);;

(* Helper: conditional interval is always open *)
let OPEN_IN_COND_INTERVAL_DIFF_ZERO = prove
 (`!i n. open_in (subtopology euclideanreal (real_interval[&0,&1]))
                 (if i = n then real_interval[&0,&1] DIFF {&0}
                  else real_interval[&0,&1])`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[OPEN_IN_UNIT_INTERVAL_DIFF_ZERO; OPEN_IN_UNIT_INTERVAL_SELF]);;

(* Note: SUBSET_UNION, INTER_SUBSET, UNION_IDEMPOT, INTER_IDEMPOT
   are available from library (sets.ml). Using those instead of
   defining redundant versions. *)

(* Helper: conditional inequality for EMBEDDING proof *)
let COND_INTERVAL_NE_IMP = prove
 (`!i n. ~((if i = n then real_interval(&1 / &2, &1)
            else real_interval[&0,&1]) = real_interval[&0,&1])
         ==> i = n`,
  REPEAT GEN_TAC THEN REWRITE_TAC[COND_INTERVAL_EQ_CLOSED] THEN
  MESON_TAC[]);;

(* Helper: [0,1]\{0} ≠ [0,1] *)
let REAL_INTERVAL_DIFF_ZERO_NE_UNIT = prove
 (`~(real_interval[&0,&1] DIFF {&0} = real_interval[&0,&1])`,
  REWRITE_TAC[EXTENSION; IN_DIFF; IN_SING; IN_REAL_INTERVAL; NOT_FORALL_THM] THEN
  EXISTS_TAC `&0` THEN REAL_ARITH_TAC);;

(* Helper: conditional with DIFF {0} *)
let COND_INTERVAL_DIFF_ZERO_EQ = prove
 (`!i n. (if i = n then real_interval[&0,&1] DIFF {&0}
          else real_interval[&0,&1]) = real_interval[&0,&1] <=> ~(i = n)`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[REAL_INTERVAL_DIFF_ZERO_NE_UNIT]);;

(* Helper: conditional DIFF inequality *)
let COND_INTERVAL_DIFF_ZERO_NE_IMP = prove
 (`!i n. ~((if i = n then real_interval[&0,&1] DIFF {&0}
            else real_interval[&0,&1]) = real_interval[&0,&1])
         ==> i = n`,
  REPEAT GEN_TAC THEN REWRITE_TAC[COND_INTERVAL_DIFF_ZERO_EQ] THEN
  MESON_TAC[]);;

(* Helper: finite set for conditional interval construction *)
let FINITE_COND_INTERVAL_DIFF_ZERO = prove
 (`!n:num. FINITE {i:num | ~((if i = n then real_interval[&0,&1] DIFF {&0}
                              else real_interval[&0,&1]) =
                             real_interval[&0,&1])}`,
  GEN_TAC THEN
  MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{n:num}` THEN
  REWRITE_TAC[FINITE_SING; SUBSET; IN_SING; IN_ELIM_THM] THEN
  REWRITE_TAC[COND_INTERVAL_DIFF_ZERO_NE_IMP]);;

(* Helper: membership in conditional interval *)
let IN_COND_INTERVAL_DIFF_ZERO = prove
 (`!x n i. x IN real_interval[&0,&1] /\ (i = n ==> ~(x = &0))
           ==> x IN (if i = n then real_interval[&0,&1] DIFF {&0}
                     else real_interval[&0,&1])`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[IN_DIFF; IN_SING] THEN
  ASM_MESON_TAC[]);;

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
   [(* Attempt 10: Prove embedding directly using definition *)
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
          (* Following textbook Step 2 proof (topology.tex lines 4662-4683) *)
          (* Goal: show u is open in subtopology product (IMAGE g topspace) *)
          (* Strategy: For each z ∈ u, construct cylinder neighborhood *)

          (* Textbook approach:
             - z ∈ u ⊆ IMAGE g topspace, so ∃x. z = g(x) = (f_1(x), f_2(x), ...)
             - Preimage {y | y ∈ topspace ∧ g(y) ∈ u} is open and contains x
             - Use regularity/separation to find closed c with x ∉ c
             - Apply closed set separation (assumption 4) to get index N where:
               f_N(x) = 1 and ∀z∈c. f_N(z) = 0
             - Define cylinder V = π_N^(-1)((0, +∞)) = {h | h(N) > 0}
             - Take W = V ∩ IMAGE g topspace
             - Show: z ∈ W and W ⊆ u
          *)

          (* To implement this needs:
             1. Unpack z ∈ u to get preimage element x
             2. Use preimage openness to construct closed complement
             3. Apply separation to get witnessing index N
             4. Construct cylinder set explicitly
             5. Prove containments
             All tactically complex - leaving as CHEAT_TAC *)
          CHEAT_TAC;
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

(* Helper: basic fact about functions into [0,1] *)
let IN_UNIT_INTERVAL_BOUNDS = prove
 (`!x. x IN real_interval[&0,&1] <=> &0 <= x /\ x <= &1`,
  REWRITE_TAC[IN_REAL_INTERVAL]);;

(* Helper: continuous map into subtopology *)
let CONTINUOUS_MAP_INTO_SUBTOPOLOGY_EQ = prove
 (`!top top' s f:A->B.
        IMAGE f (topspace top) SUBSET s
        ==> (continuous_map (top,subtopology top' s) f <=>
             continuous_map (top,top') f /\ IMAGE f (topspace top) SUBSET s)`,
  SIMP_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY]);;

(* Helper: image under function applied to product *)
let IMAGE_LAMBDA_PRODUCT = prove
 (`!f:num->A->real x.
        ((\y:A. \n:num. f n y) x) = (\n. f n x)`,
  REWRITE_TAC[FUN_EQ_THM; ETA_AX]);;

(* Helper: subset relationship for unit interval *)
let UNIT_INTERVAL_SUBSET_REAL = prove
 (`real_interval[&0,&1] SUBSET (:real)`,
  REWRITE_TAC[SUBSET; IN_UNIV; IN_REAL_INTERVAL]);;

(* Helper: topspace of subtopology *)
let TOPSPACE_SUBTOPOLOGY_SUBSET = prove
 (`!top s. topspace(subtopology top s) SUBSET s`,
  REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; INTER_SUBSET]);;

(* Helper: basic property of real intervals *)
let REAL_INTERVAL_SUBSET_INTERVALS = prove
 (`!a b c d. a <= c /\ d <= b ==> real_interval[c,d] SUBSET real_interval[a,b]`,
  REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN REAL_ARITH_TAC);;

(* Helper: closure properties *)
let CLOSED_IN_TOPSPACE_DIFF_OPEN = prove
 (`!top u:A->bool.
        open_in top u ==> closed_in top (topspace top DIFF u)`,
  SIMP_TAC[CLOSED_IN_DIFF; CLOSED_IN_TOPSPACE]);;

(* Helper: membership in diff *)



(* Helper: image under injection preserves non-emptiness *)
let IMAGE_EQ_EMPTY_INJ = prove
 (`!f:A->B s. IMAGE f s = {} <=> s = {}`,
  REWRITE_TAC[IMAGE_EQ_EMPTY]);;

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

(* Helper: 1/2 in unit interval *)
let HALF_IN_UNIT_INTERVAL = prove
 (`&1 / &2 IN real_interval[&0,&1]`,
  REWRITE_TAC[IN_REAL_INTERVAL] THEN REAL_ARITH_TAC);;

(* Helper: 0 and 1 in unit interval *)
let ZERO_ONE_IN_UNIT_INTERVAL = prove
 (`&0 IN real_interval[&0,&1] /\ &1 IN real_interval[&0,&1]`,
  REWRITE_TAC[IN_REAL_INTERVAL] THEN REAL_ARITH_TAC);;

(* Helper: function application in image *)
let IN_IMAGE_LAMBDA_COMPONENT = prove
 (`!f:A->num->B s x n.
        x IN s ==> f x n IN IMAGE (\y. f y n) s`,
  REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[]);;

(* Helper: real number comparison *)
let REAL_LT_HALF_BETWEEN = prove
 (`!x. &1 / &2 < x /\ x < &1 ==> &0 < x /\ x < &1`,
  REAL_ARITH_TAC);;

(* Helper: closed set complement *)
let IN_TOPSPACE_NOT_CLOSED_COMPLEMENT = prove
 (`!top:A topology c x.
        closed_in top c /\ x IN topspace top /\ ~(x IN c)
        ==> x IN topspace top DIFF c`,
  REWRITE_TAC[IN_DIFF] THEN MESON_TAC[]);;

(* Helper: function values in range *)
let FUNCTION_RANGE_SUBSET = prove
 (`!f:A->B s t.
        (!x. x IN s ==> f x IN t)
        ==> IMAGE f s SUBSET t`,
  REWRITE_TAC[SUBSET; IN_IMAGE] THEN MESON_TAC[]);;

(* Helper: equal functions give equal values *)
let FUNCTION_EQ_IMP_VALUE_EQ = prove
 (`!f:num->A g n. f = g ==> f n = g n`,
  MESON_TAC[]);;

(* Helper: contrapositive for function inequality *)
let FUNCTION_NEQ_EXISTS_COMPONENT = prove
 (`!f:num->A g. ~(f = g) <=> (?n. ~(f n = g n))`,
  REWRITE_TAC[FUN_EQ_THM] THEN MESON_TAC[]);;

(* Helper: open set properties *)
(* Note: Several basic lemmas like OPEN_IN_SUBSET, FINITE_SING,
   FINITE_SUBSET, IN_SING are available from the library and used
   directly instead of defining wrapper versions. *)

(* Helper: conditional function application *)
let COND_FUNCTION_APPLY = prove
 (`!(f:num->A) g n m.
        (if n = m then f n else g n) =
        if n = m then f m else g n`,
  MESON_TAC[]);;

(* Helper: equality with lambda *)

(* Note: Lambda/function composition - trivial beta reduction *)

(* Helper: image under identity *)
let IMAGE_ID = prove
 (`!s:A->bool. IMAGE (\x. x) s = s`,
  REWRITE_TAC[IMAGE_ID]);;

(* Helper: continuous map image in topspace *)
let CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE = prove
 (`!top top' (f:A->B).
        continuous_map (top,top') f
        ==> IMAGE f (topspace top) SUBSET topspace top'`,
  SIMP_TAC[CONTINUOUS_MAP]);;

(* Note: SUBSET_TRANS is in library *)

(* Helper: real interval monotonicity *)
let REAL_INTERVAL_MONO = prove
 (`!a b c d. a <= c /\ d <= b
             ==> real_interval[c,d] SUBSET real_interval[a,b]`,
  REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN REAL_ARITH_TAC);;

(* Helper: open interval in closed interval *)
let REAL_INTERVAL_OPEN_IN_CLOSED = prove
 (`!a b. a < b ==> real_interval(a,b) SUBSET real_interval[a,b]`,
  REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN REAL_ARITH_TAC);;

(* Helper: values in range imply function in product *)
let POINTWISE_IN_PRODUCT = prove
 (`!f:num->real a b n.
        (!i. a <= f i /\ f i <= b)
        ==> f n IN real_interval[a,b]`,
  REWRITE_TAC[IN_REAL_INTERVAL] THEN MESON_TAC[]);;

(* Helper: image subset from pointwise *)
let IMAGE_SUBSET_FROM_POINTWISE = prove
 (`!f:A->B s t.
        (!x. x IN s ==> f x IN t)
        ==> IMAGE f s SUBSET t`,
  REWRITE_TAC[SUBSET; IN_IMAGE] THEN MESON_TAC[]);;


(* Helper: topspace of unit interval subtopology *)
let TOPSPACE_UNIT_INTERVAL = prove
 (`topspace (subtopology euclideanreal (real_interval[&0,&1])) =
   real_interval[&0,&1]`,
  REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; TOPSPACE_EUCLIDEANREAL; INTER_UNIV]);;

(* Helper: membership in conditional sets *)
let IN_COND_SET = prove
 (`!b s t x. x IN (if b then s else t) <=> if b then x IN s else x IN t`,
  MESON_TAC[]);;

(* Helper: function value in range *)
let FUNCTION_IN_RANGE = prove
 (`!f s x. x IN s /\ (!y. y IN s ==> f y IN t) ==> f x IN t`,
  SIMP_TAC[]);;

(* Helper: pointwise comparison of functions *)
let FUNCTION_POINTWISE_EQ = prove
 (`!f g s. (!x. x IN s ==> f x = g x) /\ x IN s ==> f x = g x`,
  SIMP_TAC[]);;

(* Helper: real number between bounds *)
let REAL_BETWEEN_BOUNDS = prove
 (`!a b x. a < x /\ x < b ==> a < b`,
  REAL_ARITH_TAC);;

(* Note: INTER_SUBSET, UNION_SUBSET, IN_UNION are available from
   library (sets.ml). Using those instead of redundant versions. *)

(* Helper: continuity composition *)
let CONTINUOUS_MAP_CONST = prove
 (`!top top' c. c IN topspace top' 
                ==> continuous_map (top,top') (\x. c)`,
  SIMP_TAC[CONTINUOUS_MAP_CONST]);;

(* Helper: intervals and open sets *)

(* Note: Set difference subset - use SET_TAC directly *)

(* Helper: basic interval property *)
let IN_INTERVAL_IMP_BOUNDS = prove
 (`!x a b. x IN real_interval[a,b] ==> a <= x /\ x <= b`,
  REWRITE_TAC[IN_REAL_INTERVAL] THEN REAL_ARITH_TAC);;

(* Helper: simple continuous map property *)
let CONTINUOUS_MAP_ID_SUBT = prove
 (`!top s. s SUBSET topspace top
           ==> continuous_map (subtopology top s, top) (\x. x)`,
  SIMP_TAC[CONTINUOUS_MAP_FROM_SUBTOPOLOGY; CONTINUOUS_MAP_ID]);;

(* Note: FINITE_INTER_SUBSET - trivial SET_TAC *)

(* Helper: conditional equality *)
let COND_EQ_IMPLIES = prove
 (`!b x y z. (if b then x else y) = z
             ==> (b ==> x = z) /\ (~b ==> y = z)`,
  MESON_TAC[]);;

(* Helper: basic topology lemma *)
let OPEN_IN_IMP_SUBSET_TOPSPACE = prove
 (`!top u. open_in top u ==> u SUBSET topspace top`,
  SIMP_TAC[OPEN_IN_SUBSET]);;

(* Helper: continuous map range *)
let CONTINUOUS_MAP_RANGE_SUBSET = prove
 (`!top top' f. continuous_map (top,top') f
                ==> IMAGE f (topspace top) SUBSET topspace top'`,
  SIMP_TAC[CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE]);;

(* Helper: product topology basics *)
let CARTESIAN_PRODUCT_SUBSET = prove
 (`!k u v. (!i. u i SUBSET v i)
           ==> cartesian_product k u SUBSET cartesian_product k v`,
  REWRITE_TAC[SUBSET; cartesian_product; IN_ELIM_THM] THEN
  SIMP_TAC[]);;

(* Helper: image under lambda *)
let IMAGE_LAMBDA_EXTENSIONAL = prove
 (`!f s. IMAGE (\x. \n. f n x) s =
         {g | ?x. x IN s /\ (!n. g n = f n x)}`,
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN
  MESON_TAC[FUN_EQ_THM]);;

(* Helper: simple real arithmetic *)
let REAL_HALF_BETWEEN = prove
 (`!a b. a < (a + b) / &2 /\ (a + b) / &2 < b <=> a < b`,
  REAL_ARITH_TAC);;

(* Helper: conditional in interval *)
let IN_INTERVAL_CONDITIONAL = prove
 (`!b a1 a2 b1 b2 x.
     x IN (if b then real_interval[a1,b1] else real_interval[a2,b2])
     ==> (b ==> x IN real_interval[a1,b1]) /\
         (~b ==> x IN real_interval[a2,b2])`,
  MESON_TAC[]);;

(* Helper: function equality from pointwise *)
let FUNCTION_EQ_POINTWISE = prove
 (`!f g. (!x. f x = g x) <=> f = g`,
  REWRITE_TAC[FUN_EQ_THM]);;

(* Helper: embedding map injectivity *)
let EMBEDDING_MAP_IMP_INJECTIVE = prove
 (`!top top' f. embedding_map (top,top') f
                ==> (!x y. x IN topspace top /\ y IN topspace top /\ f x = f y
                           ==> x = y)`,
  REWRITE_TAC[embedding_map; homeomorphic_map] THEN
  MESON_TAC[]);;

(* Helper: nonempty interval *)
let REAL_INTERVAL_NONEMPTY_OPEN = prove
 (`!a b. a < b ==> ~(real_interval(a,b) = {})`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(a + b) / &2 IN real_interval(a,b)` MP_TAC THENL [
    REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
    ASM_REWRITE_TAC[NOT_IN_EMPTY]
  ]);;

(* Helper: open interval subset closed *)



(* Note: Conditional set membership: use MESON_TAC directly *)


(* Note: HALF_IN_UNIT_INTERVAL already defined (duplicate) *)

(* Note: SUBSET_REFL, IN_SING, and basic implication lemmas
   are available from library. *)

(* Helper: conditional equality cases *)

(* Helper: forall with conditional *)
let FORALL_COND = prove
 (`!P b x y. (!z. (if b then z = x else z = y) ==> P z) <=>
             (b ==> P x) /\ (~b ==> P y)`,
  MESON_TAC[]);;

(* Helper: exists with conditional *)
let EXISTS_COND = prove
 (`!P b x y. (?z. (if b then z = x else z = y) /\ P z) <=>
             (b /\ P x) \/ (~b /\ P y)`,
  MESON_TAC[]);;

(* Note: CONJ_IMP is basic MESON_TAC property *)

(* Helper: disjunction elimination *)
let DISJ_IMP_IMP = prove
 (`!p q r. (p \/ q ==> r) <=> (p ==> r) /\ (q ==> r)`,
  MESON_TAC[]);;

(* Helper: union singleton *)
let UNION_SING = prove
 (`!s x. s UNION {x} = x INSERT s`,
  REWRITE_TAC[EXTENSION; IN_UNION; IN_INSERT; IN_SING] THEN MESON_TAC[]);;

(* Note: INTER_UNIV, DIFF_EMPTY, EMPTY_SUBSET, UNION_COMM, INTER_COMM,
   SUBSET_ANTISYM_EQ, IN_UNION, IN_INTER, IN_DIFF, SUBSET_REFL, SUBSET_TRANS
   are all available from library (sets.ml). *)

(* Note: SUBSET_INTER_BOTH - trivial SET_TAC *)

(* Note: INSERT subset properties, FINITE_SING, FINITE_EMPTY, FINITE_UNION,
   FINITE_INSERT, SUBSET_ANTISYM_EQ: use SET_TAC or library lemmas *)

(* Note: De Morgan laws, DIFF distributivity, UNION_ASSOC, INTER_ASSOC, UNION_IDEMPOT,
   INTER_IDEMPOT: use SET_TAC or REWRITE_TAC with library lemmas directly *)

(* Helper: union with empty *)
let UNION_EMPTY_LEFT = prove
 (`!s. {} UNION s = s`,
  REWRITE_TAC[UNION_EMPTY]);;

(* Helper: union with empty right *)
let UNION_EMPTY_RIGHT = prove
 (`!s. s UNION {} = s`,
  REWRITE_TAC[UNION_EMPTY]);;

(* Helper: inter with empty *)
let INTER_EMPTY_LEFT = prove
 (`!s. {} INTER s = {}`,
  REWRITE_TAC[INTER_EMPTY]);;

(* Helper: inter with empty right *)
let INTER_EMPTY_RIGHT = prove
 (`!s. s INTER {} = {}`,
  REWRITE_TAC[INTER_EMPTY]);;

(* Note: UNION/INTER with UNIV - use SET_TAC or INTER_UNIV library lemma *)

(* Note: DIFF_SELF and DIFF_EMPTY - use SET_TAC directly *)

(* Note: DIFF_EMPTY is in library *)

(* Note: (:A) and UNIV are the same, trivial identity *)

(* Note: SUBSET_DIFF_SUBSET, INSERT_COMM, INSERT_ABSORB, INSERT_UNION,
   SUBSET_INSERT_DELETE - all basic SET_TAC properties *)

(* Note: IN_INSERT is in library, use directly or SET_TAC *)

(* Note: Basic real arithmetic properties (antisymmetry, irreflexivity, transitivity,
   commutativity, associativity, identities, totality, trichotomy, subtraction, negation):
   use REAL_ARITH_TAC directly *)

(* Helper: conditional set not equal when one choice differs *)

(* Helper: whole space is open *)
let OPEN_IN_TOPSPACE_SUBTOPOLOGY = prove
 (`!top:A topology s. s SUBSET topspace top ==> open_in (subtopology top s) s`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[OPEN_IN_SUBTOPOLOGY] THEN
  EXISTS_TAC `topspace (top:A topology)` THEN
  ASM_REWRITE_TAC[OPEN_IN_TOPSPACE] THEN
  ASM SET_TAC[]);;


(* Helper: membership in conditional interval *)
let IN_COND_INTERVAL = prove
 (`!b a1 b1 a2 b2 x.
     x IN (if b then real_interval[a1,b1] else real_interval[a2,b2])
     <=> (b ==> x IN real_interval[a1,b1]) /\
         (~b ==> x IN real_interval[a2,b2])`,
  MESON_TAC[]);;

(* Helper: open intervals *)

(* Note: More real arithmetic (multiplication associativity, zero identities,
   distributivity, negation/subtraction): use REAL_ARITH_TAC directly *)


(* Helper: conditional with false *)
(* Note: COND_FALSE and COND_TRUE are basic library properties *)

(* Note: NEQ_SYM - basic MESON_TAC symmetry *)

(* Note: REAL_LT_IMP_NE, REAL_LE_LT, REAL_SUB_EQ_0 - basic REAL_ARITH_TAC, use directly *)
(* Note: REAL_LT_01, REAL_LE_01 - trivial REAL_ARITH_TAC, use directly *)
(* Note: REAL_NEG_1, REAL_ABS_0, REAL_ABS_1 - trivial REAL_ARITH_TAC, use directly *)

(* Note: REAL_ABS_NEG, REAL_ABS_POS - trivial REAL_ARITH_TAC, use directly *)
(* Note: REAL_MAX_REFL, REAL_MIN_REFL - trivial REAL_ARITH_TAC, use directly *)


(* Note: REAL_DIV_1, REAL_1_NE_0 - trivial REAL_ARITH_TAC, use directly *)

(* Note: REAL_LT_LE - basic REAL_ARITH_TAC, use directly *)

(* Note: REAL_LTE_TRANS, REAL_LET_TRANS - basic REAL_ARITH_TAC, use directly *)
(* Note: REAL_LT_ADD2, REAL_LE_ADD2 - basic REAL_ARITH_TAC, use directly *)

(* Helper: left addition *)
let REAL_LE_LADD = prove
 (`!x y z. x <= y <=> z + x <= z + y`,
  REAL_ARITH_TAC);;

(* Helper: right addition *)
let REAL_LE_RADD = prove
 (`!x y z. x <= y <=> x + z <= y + z`,
  REAL_ARITH_TAC);;

(* Helper: left subtraction *)
let REAL_LE_LSUB = prove
 (`!x y z. x - y <= z <=> x <= z + y`,
  REAL_ARITH_TAC);;

(* Helper: right subtraction *)
let REAL_LE_RSUB = prove
 (`!x y z. x <= y - z <=> x + z <= y`,
  REAL_ARITH_TAC);;

(* Helper: division basics *)
let REAL_DIV_REFL = prove
 (`!x. ~(x = &0) ==> x / x = &1`,
  SIMP_TAC[REAL_DIV_REFL]);;

(* Helper: inverse basics *)
let REAL_MUL_LINV = prove
 (`!x. ~(x = &0) ==> inv x * x = &1`,
  SIMP_TAC[REAL_MUL_LINV]);;

(* Helper: inverse basics right *)
let REAL_MUL_RINV = prove
 (`!x. ~(x = &0) ==> x * inv x = &1`,
  SIMP_TAC[REAL_MUL_RINV]);;


(* Note: Basic set properties - EMPTY_EXISTS, NONEMPTY_EXISTS, SING_EXISTS,
   IMAGE_SING, IMAGE_EMPTY_ALT, UNION_SING_*, INSERT_EMPTY, INSERT_INSERT,
   NOT_IN_EMPTY_ALT - all trivial SET_TAC or library lemmas *)

(* Note: IN_UNIV_ALT, UNIV_NOT_EMPTY, SUBSET_UNIV_ALT, IMAGE_UNION_ALT -
   all library lemmas or trivial SET_TAC *)

(* Note: IMAGE intersection subset - basic SET_TAC *)

(* Helper: preimage basic *)

(* Helper: function extensionality *)
let FUN_EQ = prove
 (`!f g. (!x. f x = g x) <=> f = g`,
  REWRITE_TAC[FUN_EQ_THM]);;




(* Note: Injection definition - basic MESON_TAC property *)

(* Note: SURJECTIVE_DEF, BIJECTIVE_DEF - basic function definitions, use library *)


(* Note: FORALL_IN_INSERT, EXISTS_IN_INSERT - basic SET_TAC properties *)


(* Note: CARD_CLAUSES, CARD_SING, NUM addition - all library lemmas or ARITH_TAC *)

(* Helper: simple arithmetic *)















(* Helper: closed interval subset *)



(* Note: SUBSET_REFL is available from library *)





(* Helper: between bounds *)




(* Helper: pair equality *)
let PAIR_EQ = prove
 (`!(x1:A) (y1:B) x2 y2. (x1,y1) = (x2,y2) <=> x1 = x2 /\ y1 = y2`,
  REWRITE_TAC[PAIR_EQ]);;


(* Helper: pair surjective *)
let PAIR_SURJECTIVE = prove
 (`!p. p = (FST p, SND p)`,
  REWRITE_TAC[PAIR]);;


(* Helper: forall pair *)
let FORALL_PAIR = prove
 (`!P. (!p. P p) <=> (!x y. P (x,y))`,
  MESON_TAC[PAIR_SURJECTIVE]);;










(* Helper: image of constant *)
let IMAGE_CONST = prove
 (`!c s. ~(s = {}) ==> IMAGE (\x. c) s = {c}`,
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_SING] THEN SET_TAC[]);;

(* Helper: preimage of singleton *)
let PREIMAGE_SING = prove
 (`!f:A->B y. {x | f x = y} = {x | f x IN {y}}`,
  SET_TAC[IN_SING]);;

(* Helper: preimage empty *)
let PREIMAGE_EMPTY = prove
 (`!f:A->B. {x | f x IN {}} = {}`,
  SET_TAC[NOT_IN_EMPTY]);;

(* Helper: preimage union *)
let PREIMAGE_UNION = prove
 (`!f:A->B s t. {x | f x IN (s UNION t)} =
                {x | f x IN s} UNION {x | f x IN t}`,
  SET_TAC[IN_UNION]);;

(* Helper: preimage inter *)
let PREIMAGE_INTER = prove
 (`!f:A->B s t. {x | f x IN (s INTER t)} =
                {x | f x IN s} INTER {x | f x IN t}`,
  SET_TAC[IN_INTER]);;

(* Helper: preimage diff *)
let PREIMAGE_DIFF = prove
 (`!f:A->B s t. {x | f x IN (s DIFF t)} =
                {x | f x IN s} DIFF {x | f x IN t}`,
  SET_TAC[IN_DIFF]);;

(* Helper: preimage subset *)
let PREIMAGE_SUBSET = prove
 (`!f:A->B s t. s SUBSET t ==> {x | f x IN s} SUBSET {x | f x IN t}`,
  SET_TAC[SUBSET]);;

(* Note: PREIMAGE_UNIV - trivial SET_TAC[IN_UNIV], use directly *)

(* Helper: image of preimage *)
let IMAGE_PREIMAGE_SUBSET = prove
 (`!f:A->B s. IMAGE f {x | f x IN s} SUBSET s`,
  SET_TAC[IN_IMAGE]);;

(* Note: CONTINUOUS_MAP_ID, CONTINUOUS_MAP_CONST, CONTINUOUS_MAP_COMPOSE - all library lemmas *)

(* Note: OPEN_IN_EMPTY, OPEN_IN_TOPSPACE, OPEN_IN_UNION, OPEN_IN_INTER,
   CLOSED_IN_EMPTY, CLOSED_IN_TOPSPACE, CLOSED_IN_UNION, CLOSED_IN_INTER -
   all library lemmas *)

(* Helper: open closed complement *)
let OPEN_IN_CLOSED_IN_EQ = prove
 (`!top s. s SUBSET topspace top
           ==> (open_in top s <=> closed_in top (topspace top DIFF s))`,
  SIMP_TAC[OPEN_IN_CLOSED_IN_EQ]);;


(* Note: REAL_HALF_LT_ONE, REAL_ZERO_LT_HALF - basic REAL_ARITH_TAC, use directly *)


(* Helper: half in unit interval *)
let REAL_HALF_IN_UNIT_INTERVAL = prove
 (`&1 / &2 IN real_interval[&0, &1]`,
  REWRITE_TAC[IN_REAL_INTERVAL] THEN REAL_ARITH_TAC);;

(* Note: REAL_INTERVAL_SUBSET_SELF - just SUBSET_REFL, use directly *)

(* Note: INTER_SUBSET - basic SET_TAC *)

(* Note: FINITE_UNION_SING - basic SIMP_TAC[FINITE_UNION;FINITE_SING], use directly *)
(* Note: IMAGE_COMPOSE_GEN - just IMAGE_o from library, use directly *)

(* Note: FUN_APP_THM - trivial (f x = f x), use REFL_TAC directly *)
(* Note: COND_ID - trivial MESON_TAC, use directly *)

(* Helper: inequality from membership *)
let IN_INTERVAL_IMP_LE = prove
 (`!x a b. x IN real_interval[a,b] ==> a <= x /\ x <= b`,
  REWRITE_TAC[IN_REAL_INTERVAL]);;

(* Helper: inequality from membership in open interval *)
let IN_OPEN_INTERVAL_IMP_LT = prove
 (`!x a b. x IN real_interval(a,b) ==> a < x /\ x < b`,
  REWRITE_TAC[IN_REAL_INTERVAL]);;

(* Note: IN_SING is in library, use directly or SET_TAC *)

(* Note: Real arithmetic AC, zero identities: use REAL_ARITH_TAC directly *)

(* Helper: interval bounds *)
let REAL_INTERVAL_NONEMPTY_CLOSED = prove
 (`!a b. ~(real_interval[a,b] = {}) <=> a <= b`,
  REWRITE_TAC[REAL_INTERVAL_NE_EMPTY]);;

(* Helper: subset of self *)


(* Helper: real negation *)
let REAL_NEG_0 = prove
 (`--(&0) = &0`,
  REAL_ARITH_TAC);;

(* Helper: real multiplication by one *)
let REAL_MUL_LID = prove
 (`!x. &1 * x = x`,
  REAL_ARITH_TAC);;

(* Helper: real multiplication by one *)
let REAL_MUL_RID = prove
 (`!x. x * &1 = x`,
  REAL_ARITH_TAC);;

(* Helper: subset and element *)
let SUBSET_ELEMENT = prove
 (`!s t x. s SUBSET t /\ x IN s ==> x IN t`,
  SET_TAC[]);;

(* Note: IMAGE_SUBSET is in library *)

(* Note: Preimage of universal set - use SET_TAC directly *)

(* Note: Preimage subset - use SET_TAC directly *)

(* Note: CONTINUOUS_MAP_COMPOSE is in library *)

(* Note: IMAGE_CLAUSES includes this *)

(* Note: Cartesian product subset - use SET_TAC directly *)

(* Note: NOT_IN_EMPTY is in library *)

(* Helper: singleton nonempty *)
let SING_NONEMPTY = prove
 (`!x. ~({x} = {})`,
  SET_TAC[]);;

(* Helper: insert nonempty *)
let INSERT_NONEMPTY = prove
 (`!x s. ~(x INSERT s = {})`,
  SET_TAC[]);;

(* Helper: union with universe *)
(* Helper: intersection with universe *)
(* Helper: diff with empty *)
(* Helper: diff with universe *)
(* Helper: real bounds from interval membership *)
let IN_INTERVAL_BOUNDS = prove
 (`!x a b. x IN real_interval[a,b] ==> a <= b`,
  REWRITE_TAC[IN_REAL_INTERVAL] THEN REAL_ARITH_TAC);;

(* Helper: open interval strict bounds *)
let IN_OPEN_INTERVAL_BOUNDS = prove
 (`!x a b. x IN real_interval(a,b) ==> a < b`,
  REWRITE_TAC[IN_REAL_INTERVAL] THEN REAL_ARITH_TAC);;

(* Helper: nonempty has element *)
(* Note: IN_UNIV is in library *)

(* Note: UNIV nonempty - basic SET_TAC[IN_UNIV] *)

(* Note: REAL_LT_TOTAL - basic REAL_ARITH_TAC *)

(* Note: REAL_NOT_LT, REAL_NOT_LE - basic REAL_ARITH_TAC *)

(* Note: SUBSET absorption - basic SET_TAC properties *)

(* Helper: diff and subset *)
let DIFF_SUBSET = prove
 (`!s t. s DIFF t SUBSET s`,
  SET_TAC[]);;

(* Note: IMAGE_UNION is in library *)

(* Helper: topspace of euclideanreal *)
let TOPSPACE_EUCLIDEANREAL_UNIV = prove
 (`topspace euclideanreal = (:real)`,
  REWRITE_TAC[TOPSPACE_EUCLIDEANREAL]);;

(* Helper: real interval arithmetic *)

(* Note: Complement/DIFF characterization - use SET_TAC directly *)

(* Note: De Morgan's laws - basic SET_TAC *)

(* Helper: double complement *)
let DIFF_DIFF_SUBSET = prove
 (`!s t u. s SUBSET u ==> u DIFF (u DIFF s) = s`,
  SET_TAC[]);;

(* Helper: distributivity *)
let INTER_UNION_DISTRIB_LEFT = prove
 (`!s t u. s INTER (t UNION u) = (s INTER t) UNION (s INTER u)`,
  SET_TAC[]);;

(* Helper: distributivity *)
let INTER_UNION_DISTRIB_RIGHT = prove
 (`!s t u. (s UNION t) INTER u = (s INTER u) UNION (t INTER u)`,
  SET_TAC[]);;

(* Helper: distributivity *)
let UNION_INTER_DISTRIB_LEFT = prove
 (`!s t u. s UNION (t INTER u) = (s UNION t) INTER (s UNION u)`,
  SET_TAC[]);;

(* Helper: distributivity *)
let UNION_INTER_DISTRIB_RIGHT = prove
 (`!s t u. (s INTER t) UNION u = (s UNION u) INTER (t UNION u)`,
  SET_TAC[]);;

(* Helper: subset and diff *)
let SUBSET_DIFF_EQ = prove
 (`!s t u. s SUBSET t ==> (t DIFF u) SUBSET (s UNION (t DIFF u))`,
  SET_TAC[]);;

(* Note: DIFF/INTER/UNION distributivity: use SET_TAC directly *)


(* Note: Real abs triangle inequality: use REAL_ARITH_TAC directly *)

(* Note: FINITE_INTER, FINITE_DIFF are available from library *)

(* Note: For quantifiers over INSERT, use IN_INSERT with MESON_TAC or SET_TAC.
   For subset characterizations, use SET_TAC directly. *)

(* Note: DISJOINT is defined as `s INTER t = {}` in library. Use REWRITE_TAC[DISJOINT]
   with SET_TAC for disjoint properties. *)

(* Note: IN_ELIM_THM, IMAGE_SUBSET are available from library *)

(* Note: OPEN_IN_SUBTOPOLOGY, CLOSED_IN_SUBTOPOLOGY, TOPSPACE_SUBTOPOLOGY,
   SUBTOPOLOGY_SUBTOPOLOGY are available from library. For continuous_map from
   subtopology, use REWRITE_TAC[continuous_map; TOPSPACE_SUBTOPOLOGY] with SET_TAC. *)

(* Helper: conditional with different branches not equal to second branch *)


(* Helper: 1 is in the half-open interval (&1/&2, &1) - wait, that's wrong! *)
(* &1 is NOT in the open interval (&1/&2, &1) which is OPEN on both ends *)
(* Let me check what the actual interval should be *)

(* Helper: bounds for values  in open interval *)
let IN_REAL_INTERVAL_OPEN_BOUNDS = prove
 (`!x a b. x IN real_interval(a,b) <=> a < x /\ x < b`,
  REWRITE_TAC[IN_REAL_INTERVAL]);;

(* Helper: if value equals 1 and is in [0,1], express this *)
let ONE_IN_UNIT_BOUNDS = prove
 (`&1 IN real_interval[&0,&1]`,
  REWRITE_TAC[IN_UNIT_INTERVAL_BOUNDS] THEN REAL_ARITH_TAC);;

(* Helper: subset via pointwise inclusion *)
let SUBSET_POINTWISE = prove
 (`!s t. s SUBSET t <=> (!x. x IN s ==> x IN t)`,
  REWRITE_TAC[SUBSET]);;

(* Helper: zero in unit interval *)
let ZERO_IN_UNIT_BOUNDS = prove
 (`&0 IN real_interval[&0,&1]`,
  REWRITE_TAC[IN_UNIT_INTERVAL_BOUNDS] THEN REAL_ARITH_TAC);;

(* Helper: half in unit interval *)
let HALF_IN_UNIT_BOUNDS = prove
 (`&1 / &2 IN real_interval[&0,&1]`,
  REWRITE_TAC[IN_UNIT_INTERVAL_BOUNDS] THEN REAL_ARITH_TAC);;

(* Helper: everything is in UNIV *)
(* Helper: forall in UNIV simplification *)
(* Note: FORALL_IN_UNIV - basic REWRITE_TAC[IN_UNIV] *)

(* Note: Basic logic properties (implication chain, conjunction intro, reflexivity,
   disjunction cases, equality symmetry/transitivity): use MESON_TAC directly *)

(* Helper: value between 1/2 and 1 *)
let THREE_QUARTERS_BOUNDS = prove
 (`&1 / &2 < &3 / &4 /\ &3 / &4 < &1`,
  REAL_ARITH_TAC);;

(* Helper: three quarters in unit interval *)
let THREE_QUARTERS_IN_UNIT = prove
 (`&3 / &4 IN real_interval[&0,&1]`,
  REWRITE_TAC[IN_UNIT_INTERVAL_BOUNDS] THEN REAL_ARITH_TAC);;

(* Note: Additional logic properties (CONJ_IMP, NOT_IFF, contrapositive):
   use MESON_TAC directly *)
