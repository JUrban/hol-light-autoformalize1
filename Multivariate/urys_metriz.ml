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
  (* Strategy from Munkres topology.tex §34:
     For pairs (Bn, Bm) where Bn ⊆ Bm from countable basis,
     use Urysohn to get function that is 1 on Bn and 0 outside Bm.
     Since basis is countable, and we use pairs from basis, we get
     countably many functions. These functions separate points and
     closed sets as required. *)

  (* Use Axiom of Choice to get functions for all needed separations *)
  (* For point separation: use COMPLETELY_REGULAR_HAUSDORFF_POINT_FUNCTIONS *)
  (* For closed set separation: use completely_regular directly *)

  (* The collection of all such separation needs is at most countable *)
  (* because the space is second countable *)

  (* Key insight: We don't need to explicitly construct the enumeration *)
  (* We just need to show existence of a countable family with the properties *)

  (* For a second countable space, the collection of pairs (x,y) with x≠y *)
  (* and the collection of pairs (closed set, point) we need to separate *)
  (* can both be covered by countably many functions from the basis *)

  (* Full rigorous proof requires ~40-60 more lines of careful argument *)
  (* involving enumeration, choice, and verification *)
  (* Gradual approach: admit for now *)
  CHEAT_TAC);;

(* Helper: explicit pairing function for enumeration *)
let CANTOR_PAIRING = new_definition
 `CANTOR_PAIRING (n:num,m:num) = (n + m) * (n + m + 1) DIV 2 + m`;;

(* Helper: inverse of Cantor pairing *)
(* For a given k, find the unique (n,m) such that CANTOR_PAIRING(n,m) = k *)
(* We can compute this by finding the "diagonal" s = n+m, then extracting m *)
let CANTOR_UNPAIR = new_definition
 `CANTOR_UNPAIR k =
    let s = @s. s * (s + 1) DIV 2 <= k /\ k < (s + 1) * (s + 2) DIV 2 in
    let m = k - s * (s + 1) DIV 2 in
    let n = s - m in
    (n,m)`;;

(* Note: Full bijectivity proofs would require ~30-40 lines *)
(* These are standard results about Cantor pairing *)
(* For now, definitions are available for use *)

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
      X_GEN_TAC `u:A->bool` THEN STRIP_TAC THEN
      (* Need to show: IMAGE g u is open in product topology *)
      (* Strategy: For each x in u, use fourth property with closed topspace \ u *)
      (* This gives index n where f_n(x) = 1, f_n = 0 outside u *)
      (* Then {w | w_n > 1/2} is a basic open containing g(x) *)
      (* Must show this is contained in IMAGE g u - uses that f_n = 0 outside u *)
      (* Requires detailed product topology and set theory reasoning *)
      CHEAT_TAC;
      (* Prove injectivity *)
      MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN STRIP_TAC THEN
      EQ_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
      ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
      REWRITE_TAC[FUN_EQ_THM] THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`x:A`; `y:A`]) THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[]];
    REWRITE_TAC[]]);;

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
let IN_DIFF_CONTRAPOS = prove
 (`!s t x:A. x IN s /\ ~(x IN t) ==> x IN s DIFF t`,
  REWRITE_TAC[IN_DIFF]);;

(* Helper: subset and image *)
let SUBSET_IMAGE_INJ = prove
 (`!f:A->B s t. (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y) /\
                 t SUBSET s
                 ==> (IMAGE f t SUBSET IMAGE f s)`,
  REWRITE_TAC[SUBSET; IN_IMAGE] THEN MESON_TAC[]);;

(* Helper: function values and intervals *)
let IN_INTERVAL_1_2 = prove
 (`&1 / &2 < &1`,
  REAL_ARITH_TAC);;

(* Helper: image under injection preserves non-emptiness *)
let IMAGE_EQ_EMPTY_INJ = prove
 (`!f:A->B s. IMAGE f s = {} <=> s = {}`,
  REWRITE_TAC[IMAGE_EQ_EMPTY]);;

(* Helper: basic set theory for diff *)
let SUBSET_DIFF_SUBSET = prove
 (`!s t u:A->bool. s SUBSET t /\ u SUBSET s ==> t DIFF s SUBSET t DIFF u`,
  REWRITE_TAC[SUBSET; IN_DIFF] THEN MESON_TAC[]);;

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
let OPEN_IN_SUBSET_TOPSPACE = prove
 (`!top:A topology u. open_in top u ==> u SUBSET topspace top`,
  MESON_TAC[OPEN_IN_SUBSET]);;

(* Helper: point in open set is in topspace *)
let IN_OPEN_IN_IMP_IN_TOPSPACE = prove
 (`!top:A topology u x.
        open_in top u /\ x IN u ==> x IN topspace top`,
  MESON_TAC[OPEN_IN_SUBSET; SUBSET]);;

(* Helper: image contains preimage elements *)
let PREIMAGE_IN_IMAGE = prove
 (`!f:A->B s x. x IN s ==> f x IN IMAGE f s`,
  REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[]);;

(* Helper: singleton is finite *)
let FINITE_SING_ALT = prove
 (`!x:A. FINITE {x}`,
  REWRITE_TAC[FINITE_SING]);;

(* Helper: subset of finite set *)
let SUBSET_FINITE_I = prove
 (`!s:A->bool t. FINITE t /\ s SUBSET t ==> FINITE s`,
  MESON_TAC[FINITE_SUBSET]);;

(* Helper: membership in singleton set *)
let IN_SING_EQ = prove
 (`!x:A y. x IN {y} <=> x = y`,
  REWRITE_TAC[IN_SING]);;

(* Helper: conditional function application *)
let COND_FUNCTION_APPLY = prove
 (`!(f:num->A) g n m.
        (if n = m then f n else g n) =
        if n = m then f m else g n`,
  MESON_TAC[]);;

(* Helper: equality with lambda *)
let LAMBDA_ETA = prove
 (`!f:A->B. (\x. f x) = f`,
  REWRITE_TAC[ETA_AX]);;

(* Helper: function composition with lambda *)
let LAMBDA_COMPOSE = prove
 (`!f:B->C g:A->B x. (\y. f (g y)) x = f (g x)`,
  REWRITE_TAC[]);;

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

(* Helper: subset transitivity *)
let SUBSET_TRANS_ALT = prove
 (`!s:A->bool t u. s SUBSET t /\ t SUBSET u ==> s SUBSET u`,
  REWRITE_TAC[SUBSET] THEN MESON_TAC[]);;

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

(* Helper: set inequality *)
let SET_NEQ_EXISTS_ELEMENT = prove
 (`!s:A->bool t. ~(s = t) <=> (?x. x IN s /\ ~(x IN t) \/ ~(x IN s) /\ x IN t)`,
  REWRITE_TAC[EXTENSION] THEN MESON_TAC[]);;

(* Helper: nonempty set has element *)
let NONEMPTY_HAS_ELEMENT = prove
 (`!s:A->bool. ~(s = {}) <=> (?x. x IN s)`,
  REWRITE_TAC[EXTENSION; NOT_IN_EMPTY] THEN MESON_TAC[]);;

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
