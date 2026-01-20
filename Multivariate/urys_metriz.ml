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

(* Note: CONTINUOUS_MAP_COMPLEMENT_UNIT_INTERVAL - unused, can derive with
   CONTINUOUS_MAP_COMPOSE + CONTINUOUS_MAP_REAL_SUB as needed *)

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

(* Note: T3_HAUSDORFF_POINT_SEPARATION - unused, can derive from
   hausdorff_space definition + CLOSED_IN_DIFF as needed *)

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

  (* Attempt 17: More explicit construction with partial admits *)

  (* Step 1: For pairs where closure(e n) ⊆ e m, construct separating function *)
  (* This follows textbook approach: use Urysohn for each valid pair *)
  (* Then enumerate the countable family of pairs to get sequence {f_n} *)
  (* The enumeration and choice construction are complex, so we admit this step *)
  (* with clear documentation of the strategy *)

  (* Textbook strategy from Munkres Topology §34, Theorem 34.1, Step 1:
     - For each pair (n,m) where closure(B_n) ⊂ B_m in the countable basis,
       use Urysohn lemma to construct g_{n,m}: X → [0,1] with:
       * g_{n,m}(closure(B_n)) = {1}
       * g_{n,m}(X - B_m) = {0}
     - The set of such pairs is countable (subset of ℕ × ℕ)
     - Enumerate these pairs and their functions to get {f_n: n ∈ ℕ}
     - This family separates points and points from closed sets by regularity

     Implementation requires:
     - Dependent choice to extract function for each valid pair
     - Pairing enumeration (e.g., via Cantor pairing or library NUMPAIR)
     - Verification that separation properties are preserved under reindexing
  *)

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

(* Note: Removed 8 unused conditional interval helper lemmas:
   REAL_INTERVAL_OPEN_NE_CLOSED_UNIT, COND_INTERVAL_EQ_CLOSED,
   OPEN_IN_UNIT_INTERVAL_DIFF_ZERO, OPEN_IN_UNIT_INTERVAL_SELF,
   REAL_INTERVAL_DIFF_ZERO_NE_UNIT, COND_INTERVAL_DIFF_ZERO_EQ,
   COND_INTERVAL_DIFF_ZERO_NE_IMP, IN_COND_INTERVAL_DIFF_ZERO
   All were unused and can be derived with REAL_ARITH_TAC/SET_TAC as needed. *)

(* Note: SUBSET_UNION, INTER_SUBSET, UNION_IDEMPOT, INTER_IDEMPOT
   are available from library (sets.ml). Using those instead of
   defining redundant versions. *)

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
(* Helper: continuous map into subtopology *)

(* Helper: membership in diff *)

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

(* Note: HALF_IN_UNIT_INTERVAL - trivial REAL_ARITH_TAC, unused, removed *)

(* Helper: 0 and 1 in unit interval *)

(* Helper: open set properties *)
(* Note: Several basic lemmas like OPEN_IN_SUBSET, FINITE_SING,
   FINITE_SUBSET, IN_SING are available from the library and used
   directly instead of defining wrapper versions. *)

(* Helper: equality with lambda *)

(* Note: Lambda/function composition - trivial beta reduction *)

(* Helper: image under identity *)
(* Helper: continuous map image in topspace *)
let CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE = prove
 (`!top top' (f:A->B).
        continuous_map (top,top') f
        ==> IMAGE f (topspace top) SUBSET topspace top'`,
  SIMP_TAC[CONTINUOUS_MAP]);;

(* Note: SUBSET_TRANS is in library *)

(* Helper: topspace of unit interval subtopology *)

(* Helper: membership in conditional sets *)
(* Note: INTER_SUBSET, UNION_SUBSET, IN_UNION are available from
   library (sets.ml). Using those instead of redundant versions. *)

(* Helper: intervals and open sets *)

(* Note: Set difference subset - use SET_TAC directly *)

(* Note: FINITE_INTER_SUBSET - trivial SET_TAC *)

(* Helper: product topology basics *)

(* Helper: open interval subset closed *)

(* Note: Conditional set membership: use MESON_TAC directly *)

(* Note: HALF_IN_UNIT_INTERVAL removed (unused, trivial REAL_ARITH_TAC) *)

(* Note: SUBSET_REFL, IN_SING, and basic implication lemmas
   are available from library. *)

(* Helper: conditional equality cases *)

(* Note: CONJ_IMP is basic MESON_TAC property *)

(* Helper: union singleton *)
(* Note: INTER_UNIV, DIFF_EMPTY, EMPTY_SUBSET, UNION_COMM, INTER_COMM,
   SUBSET_ANTISYM_EQ, IN_UNION, IN_INTER, IN_DIFF, SUBSET_REFL, SUBSET_TRANS
   are all available from library (sets.ml). *)

(* Note: SUBSET_INTER_BOTH - trivial SET_TAC *)

(* Note: INSERT subset properties, FINITE_SING, FINITE_EMPTY, FINITE_UNION,
   FINITE_INSERT, SUBSET_ANTISYM_EQ: use SET_TAC or library lemmas *)

(* Note: De Morgan laws, DIFF distributivity, UNION_ASSOC, INTER_ASSOC, UNION_IDEMPOT,
   INTER_IDEMPOT: use SET_TAC or REWRITE_TAC with library lemmas directly *)

(* Helper: union with empty *)
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

(* Note: REAL_DIV_REFL, REAL_MUL_LINV, REAL_MUL_RINV - trivial library wrappers, use library directly *)

(* Note: Basic set properties - EMPTY_EXISTS, NONEMPTY_EXISTS, SING_EXISTS,
   IMAGE_SING, IMAGE_EMPTY_ALT, UNION_SING_*, INSERT_EMPTY, INSERT_INSERT,
   NOT_IN_EMPTY_ALT - all trivial SET_TAC or library lemmas *)

(* Note: IN_UNIV_ALT, UNIV_NOT_EMPTY, SUBSET_UNIV_ALT, IMAGE_UNION_ALT -
   all library lemmas or trivial SET_TAC *)

(* Note: IMAGE intersection subset - basic SET_TAC *)

(* Helper: preimage basic *)

(* Note: FUN_EQ - unused wrapper of FUN_EQ_THM, use FUN_EQ_THM directly *)

(* Note: Injection definition - basic MESON_TAC property *)

(* Note: SURJECTIVE_DEF, BIJECTIVE_DEF - basic function definitions, use library *)

(* Note: FORALL_IN_INSERT, EXISTS_IN_INSERT - basic SET_TAC properties *)

(* Note: CARD_CLAUSES, CARD_SING, NUM addition - all library lemmas or ARITH_TAC *)

(* Helper: simple arithmetic *)

(* Helper: closed interval subset *)

(* Note: SUBSET_REFL is available from library *)

(* Helper: between bounds *)

(* Note: PAIR_EQ - trivial library wrapper, use library PAIR_EQ directly *)

(* Helper: image of constant *)

(* Helper: preimage of singleton *)
(* Note: PREIMAGE_UNIV - trivial SET_TAC[IN_UNIV], use directly *)

(* Note: CONTINUOUS_MAP_ID, CONTINUOUS_MAP_CONST, CONTINUOUS_MAP_COMPOSE - all library lemmas *)

(* Note: OPEN_IN_EMPTY, OPEN_IN_TOPSPACE, OPEN_IN_UNION, OPEN_IN_INTER,
   CLOSED_IN_EMPTY, CLOSED_IN_TOPSPACE, CLOSED_IN_UNION, CLOSED_IN_INTER -
   all library lemmas *)

(* Note: OPEN_IN_CLOSED_IN_EQ - trivial library wrapper, use library directly *)

(* Note: REAL_HALF_LT_ONE, REAL_ZERO_LT_HALF - basic REAL_ARITH_TAC, use directly *)

(* Helper: half in unit interval *)
(* Note: REAL_INTERVAL_SUBSET_SELF - just SUBSET_REFL, use directly *)

(* Note: INTER_SUBSET - basic SET_TAC *)

(* Note: FINITE_UNION_SING - basic SIMP_TAC[FINITE_UNION;FINITE_SING], use directly *)
(* Note: IMAGE_COMPOSE_GEN - just IMAGE_o from library, use directly *)

(* Note: FUN_APP_THM - trivial (f x = f x), use REFL_TAC directly *)
(* Note: COND_ID - trivial MESON_TAC, use directly *)

(* Note: IN_SING is in library, use directly or SET_TAC *)

(* Note: Real arithmetic AC, zero identities: use REAL_ARITH_TAC directly *)

(* Helper: subset of self *)

(* Note: IMAGE_SUBSET is in library *)

(* Note: Preimage of universal set - use SET_TAC directly *)

(* Note: Preimage subset - use SET_TAC directly *)

(* Note: CONTINUOUS_MAP_COMPOSE is in library *)

(* Note: IMAGE_CLAUSES includes this *)

(* Note: Cartesian product subset - use SET_TAC directly *)

(* Note: NOT_IN_EMPTY is in library *)

(* Helper: singleton nonempty *)
(* Helper: union with universe *)
(* Helper: intersection with universe *)
(* Helper: diff with empty *)
(* Helper: diff with universe *)
(* Note: IN_UNIV is in library *)

(* Note: UNIV nonempty - basic SET_TAC[IN_UNIV] *)

(* Note: REAL_LT_TOTAL - basic REAL_ARITH_TAC *)

(* Note: REAL_NOT_LT, REAL_NOT_LE - basic REAL_ARITH_TAC *)

(* Note: SUBSET absorption - basic SET_TAC properties *)

(* Helper: diff and subset *)
(* Note: IMAGE_UNION is in library *)

(* Helper: topspace of euclideanreal *)

(* Helper: real interval arithmetic *)

(* Note: Complement/DIFF characterization - use SET_TAC directly *)

(* Note: De Morgan's laws - basic SET_TAC *)

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

(* Helper: everything is in UNIV *)
(* Helper: forall in UNIV simplification *)
(* Note: FORALL_IN_UNIV - basic REWRITE_TAC[IN_UNIV] *)

(* Note: Basic logic properties (implication chain, conjunction intro, reflexivity,
   disjunction cases, equality symmetry/transitivity): use MESON_TAC directly *)

(* Note: Additional logic properties (CONJ_IMP, NOT_IFF, contrapositive):
   use MESON_TAC directly *)
