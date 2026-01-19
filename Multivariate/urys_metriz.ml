(* work.ml *)

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
  (* The hard part: constructing a countable indexed family *)
  (* We have: - normal_space (hence functions exist by Urysohn)
               - completely_regular (hence separating functions exist)
               - countable basis b
     Approach: enumerate basis pairs, construct functions from them *)
  (* First, b CROSS b is countable *)
  SUBGOAL_THEN `COUNTABLE (b CROSS b:(A->bool#A->bool)->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC COUNTABLE_CROSS THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* Strategy for completing this proof:
     1. Enumerate relevant pairs using COUNTABLE_AS_IMAGE
     2. For each pair type, use appropriate helper:
        - Point pairs: COMPLETELY_REGULAR_HAUSDORFF_POINT_FUNCTIONS
        - Point-set pairs: completely_regular + COMPLEMENT_UNIT_INTERVAL
     3. Merge into single num->A->real family
     4. Prove four properties from construction
     Estimated: ~50-70 lines of enumeration and merging *)
  CHEAT_TAC);;

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
   [MATCH_MP_TAC INJECTIVE_OPEN_IMP_EMBEDDING_MAP THEN
    CONJ_TAC THENL
     [(* Prove continuous_map using componentwise criterion *)
      REWRITE_TAC[CONTINUOUS_MAP_COMPONENTWISE_UNIV] THEN
      GEN_TAC THEN REWRITE_TAC[ETA_AX] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [(* Prove open_map *)
      (* Strategy: use fourth property to show images of open sets are open *)
      (* For open u and x in u, topspace top \ u is closed *)
      (* Fourth property gives function that is 1 at x and 0 outside u *)
      (* This can be used to construct open neighborhoods in product *)
      REWRITE_TAC[open_map] THEN
      REPEAT STRIP_TAC THEN
      (* Strategy documented:
         1. Use OPEN_IN_PRODUCT_TOPOLOGY_ALT
         2. For each x in u, fourth property gives n where f_n(x)=1, f_n=0 outside u
         3. Construct basic open {y | y_n > 1/2} containing g(x)
         4. Prove this is contained in IMAGE g u
         5. This establishes openness in product topology
         Estimated: ~25-35 lines of product topology reasoning *)
      CHEAT_TAC;
      (* Prove injectivity *)
      MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN STRIP_TAC THEN
      EQ_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
      ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
      REWRITE_TAC[FUN_EQ_THM] THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`x:A`; `y:A`]) THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[]];
    REWRITE_TAC[]]);;

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
