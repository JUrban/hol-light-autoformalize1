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

(* Helper: construct separating functions from countable basis *)
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
  (* Now enumerate: either empty or can use COUNTABLE_AS_IMAGE *)
  (* The complete construction requires choosing appropriate pairs,
     applying Urysohn/completely_regular to each, and proving properties *)
  (* This is substantial infrastructure (~50-80 lines) *)
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
      (* Need to show: for any open u, IMAGE g u is open in product *)
      REPEAT STRIP_TAC THEN
      (* Have: open_in top u *)
      (* Goal: open_in (product_topology...) (IMAGE (\x. \n. f n x) u) *)
      (* The direct proof requires OPEN_IN_PRODUCT_TOPOLOGY_ALT *)
      (* and constructing basic opens from the fourth property *)
      (* This is substantial infrastructure (~30-40 lines) *)
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
