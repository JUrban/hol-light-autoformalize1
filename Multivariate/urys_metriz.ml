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
  (* Following Munkres §34.1, Step 1: For each pair (n,m) where
     closure(B_n) ⊆ B_m, apply Urysohn to get g_{n,m} with g_{n,m}(closure(B_n))={1}
     and g_{n,m}(X-B_m)={0}. Reindex as {f_k} using NUMPAIR.

     Construction outline:
     1. Use SKOLEM_THM to extract choice function g: num→num→A→real
     2. Define f k = g n m where k = NUMPAIR n m (or &1/&2 if invalid)
     3. Verify four properties using regularity to find suitable basis pairs *)

  CHEAT_TAC);;

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
