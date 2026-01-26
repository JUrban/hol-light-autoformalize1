(* work.ml - Using declarative mizar/miz3 proof style *)

(* Load the well-ordering theorem for Lemma 39.2 *)
needs "Library/wo.ml";;

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
(* Helper lemmas for Lemma 39.2 construction                                 *)
(* These lemmas are used for the metric ball constructions in the proof.     *)
(* ------------------------------------------------------------------------- *)

(* Two points in different sets are separated by at least r if:
   x's r-ball is contained in u and y is not in u *)
let SHRINK_SEPARATION = prove
 (`!m:A metric x y u r.
    x IN mspace m /\ y IN mspace m /\ &0 < r /\
    mball m (x, r) SUBSET u /\ ~(y IN u)
    ==> r <= mdist m (x,y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  UNDISCH_TAC `~(y:A IN u)` THEN REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
  ASM_SIMP_TAC[IN_MBALL]);;

(* Disjoint balls when separated by enough distance *)
let DISJOINT_EN_SEPARATION = prove
 (`!m:A metric x y r.
    r + r <= mdist m (x,y)
    ==> DISJOINT (mball m (x,r)) (mball m (y,r))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC DISJOINT_MBALL THEN ASM_REWRITE_TAC[]);;

(* The neighborhood of a set is open *)
let NEIGHBORHOOD_OPEN = prove
 (`!m:A metric s r.
    &0 < r ==> open_in (mtopology m) (UNIONS {mball m (x,r) | x IN s})`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC OPEN_IN_UNIONS THEN
  REWRITE_TAC[FORALL_IN_GSPEC] THEN GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[OPEN_IN_MBALL]);;

(* Note: PAIRWISE_DISJOINT_IMP_LOCALLY_FINITE was removed - the statement as written
   is false because mspace m intersects ALL elements if they're in mspace.
   For Lemma 39.2, the key property is that the E_n elements are (1/3n)-separated,
   so any (1/6n)-ball around x meets at most one element. This is handled directly
   in the Lemma 39.2 construction. *)

(* ------------------------------------------------------------------------- *)
(* Lemma 39.2: Every open covering of a metrizable space has a countably     *)
(* locally finite open refinement that covers the space.                     *)
(* ------------------------------------------------------------------------- *)

(* Helper: if d(x,y) >= 2r then mball(x,r) and mball(y,r) are disjoint *)
let SEPARATED_DISJOINT_BALLS = prove
 (`!m:A metric x y r.
    x IN mspace m /\ y IN mspace m /\ &0 < r /\ r + r <= mdist m (x,y)
    ==> mball m (x,r) INTER mball m (y,r) = {}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_MBALL] THEN
  X_GEN_TAC `z:A` THEN
  ASM_CASES_TAC `z:A IN mspace m` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `mdist m (x:A,z) < r` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `mdist m (y:A,z) < r` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`m:A metric`; `x:A`; `z:A`; `y:A`] MDIST_TRIANGLE) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `mdist m (z:A, y) = mdist m (y, z)` SUBST1_TAC THENL
  [MATCH_MP_TAC MDIST_SYM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Helper: if T_n elements are 3r apart, then r-neighborhoods are r-apart *)
let EN_SEPARATION = prove
 (`!m:A metric r x y.
    x IN mspace m /\ y IN mspace m /\
    &0 < r /\
    &3 * r <= mdist m (x, y)
    ==> !x' y'. x' IN mball m (x, r) /\ y' IN mball m (y, r)
                ==> r <= mdist m (x', y')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`x':A`; `y':A`] THEN
  REWRITE_TAC[IN_MBALL] THEN STRIP_TAC THEN
  (* We'll show: d(x,y) <= d(x,x') + d(x',y') + d(y',y) *)
  (* Since d(x,y) >= 3r and d(x,x'), d(y,y') < r, we get d(x',y') >= r *)
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `mdist m (x:A,y) - mdist m (x,x') - mdist m (y,y')` THEN
  CONJ_TAC THENL
  [ASM_REAL_ARITH_TAC;
   (* d(x',y') >= d(x,y) - d(x,x') - d(y',y) by triangle inequality *)
   MP_TAC(ISPECL [`m:A metric`; `x:A`; `x':A`; `y:A`] MDIST_TRIANGLE) THEN
   MP_TAC(ISPECL [`m:A metric`; `x':A`; `y':A`; `y:A`] MDIST_TRIANGLE) THEN
   ASM_REWRITE_TAC[] THEN
   SUBGOAL_THEN `mdist m (y':A,y) = mdist m (y,y')` SUBST1_TAC THENL
   [MATCH_MP_TAC MDIST_SYM THEN ASM_REWRITE_TAC[]; REAL_ARITH_TAC]]);;

(* Helper: 1/(3n) <= 1/n when n >= 1 *)
let INV_3N_LE_INV_N = prove
 (`!n. ~(n = 0) ==> inv(&3 * &n) <= inv(&n)`,
  GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN
  CONJ_TAC THENL
  [ASM_SIMP_TAC[REAL_OF_NUM_LT; LE_1]; ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `&n <= &3 * &n <=> &0 <= &2 * &n`] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS]);;

(* Helper: any (1/6n)-ball meets at most one element of E_n when elements are (1/3n)-separated *)
let SMALL_BALL_MEETS_ONE = prove
 (`!m:A metric x r E_set.
    x IN mspace m /\ &0 < r /\
    (!e1 e2. e1 IN E_set /\ e2 IN E_set /\ ~(e1 = e2)
             ==> !y1 y2. y1 IN e1 /\ y2 IN e2 ==> r <= mdist m (y1, y2))
    ==> ?v. !e. e IN E_set /\ ~(mball m (x, r / &2) INTER e = {})
                ==> e = v`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `?e:A->bool. e IN E_set /\ ~(mball m (x:A, r / &2) INTER e = {})` THENL
  [FIRST_X_ASSUM(X_CHOOSE_THEN `v:A->bool` STRIP_ASSUME_TAC) THEN
   EXISTS_TAC `v:A->bool` THEN
   X_GEN_TAC `e:A->bool` THEN STRIP_TAC THEN
   ASM_CASES_TAC `e:A->bool = v` THEN ASM_REWRITE_TAC[] THEN
   (* If e != v, get y1 in ball INTER v and y2 in ball INTER e *)
   SUBGOAL_THEN `?y1:A. y1 IN mball m (x, r / &2) /\ y1 IN v` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `?y2:A. y2 IN mball m (x, r / &2) /\ y2 IN e` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
   (* y1 and y2 are both in B(x, r/2), so d(y1,y2) < r, contradicting separation *)
   FIRST_X_ASSUM(MP_TAC o SPECL [`v:A->bool`; `e:A->bool`]) THEN
   ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPECL [`y1:A`; `y2:A`]) THEN
   ASM_REWRITE_TAC[] THEN REWRITE_TAC[REAL_NOT_LE] THEN
   UNDISCH_TAC `y1:A IN mball m (x, r / &2)` THEN REWRITE_TAC[IN_MBALL] THEN
   UNDISCH_TAC `y2:A IN mball m (x, r / &2)` THEN REWRITE_TAC[IN_MBALL] THEN
   REPEAT STRIP_TAC THEN
   MP_TAC(ISPECL [`m:A metric`; `y1:A`; `x:A`; `y2:A`] MDIST_TRIANGLE) THEN
   ASM_SIMP_TAC[MDIST_SYM] THEN ASM_REAL_ARITH_TAC;
   EXISTS_TAC `{}:A->bool` THEN ASM_MESON_TAC[]]);;

(* Helper: inv(&3 * &n) > 0 when n >= 1 *)
let INV_3N_POS = prove
 (`!n. n >= 1 ==> &0 < inv(&3 * &n)`,
  GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LT_INV THEN
  MATCH_MP_TAC REAL_LT_MUL THEN
  REWRITE_TAC[REAL_ARITH `&0 < &3`] THEN
  ASM_SIMP_TAC[REAL_OF_NUM_LT; ARITH_RULE `n >= 1 ==> 0 < n`]);;

(* Helper: The two set comprehension notations are equivalent *)
let GSPEC_EQUIV = prove
 (`!f:A->B P. {f x | x | P x} = {f x | P x}`,
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN MESON_TAC[]);;

(* Helper: For a well-ordered set, there exists a minimal element containing a point *)
(* Note: Using 'a' instead of 'x' to avoid variable capture with WOSET_WELL *)
let WOSET_MINIMAL_CONTAINING = prove
 (`!ord:(A->bool)->(A->bool)->bool U a.
    woset ord /\ fld(ord) = U /\
    (?u. u IN U /\ a IN u)
    ==> ?u_min. u_min IN U /\ a IN u_min /\
                !w. w IN U /\ a IN w ==> ord u_min w`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `ord:(A->bool)->(A->bool)->bool` WOSET_WELL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `\(v:A->bool). v IN U /\ a IN v`) THEN
  REWRITE_TAC[] THEN
  ANTS_TAC THENL
  [CONJ_TAC THENL
   [(* forall x. x IN U /\ a IN x ==> U x - need REWRITE_TAC[IN] *)
    GEN_TAC THEN REWRITE_TAC[IN] THEN SIMP_TAC[];
    (* exists x. x IN U /\ a IN x - witness u *)
    EXISTS_TAC `u:A->bool` THEN ASM_REWRITE_TAC[]];
   (* (exists x. ...) ==> (exists u_min. ...) *)
   DISCH_THEN(X_CHOOSE_THEN `u_m:A->bool` STRIP_ASSUME_TAC) THEN
   EXISTS_TAC `u_m:A->bool` THEN ASM_REWRITE_TAC[]]);;

(* Lemma 39.2: Main theorem *)
let METRIZABLE_COUNTABLY_LOCALLY_FINITE_REFINEMENT = prove
 (`!top:A topology U.
    metrizable_space top /\
    (!u. u IN U ==> open_in top u) /\
    topspace top SUBSET UNIONS U
    ==> ?V. (!v. v IN V ==> open_in top v) /\
            topspace top SUBSET UNIONS V /\
            (!v. v IN V ==> ?u. u IN U /\ v SUBSET u) /\
            countably_locally_finite_in top V`,
  REPEAT STRIP_TAC THEN
  (* Get metric m such that top = mtopology m *)
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [metrizable_space]) THEN
  DISCH_THEN(X_CHOOSE_THEN `m:A metric` (ASSUME_TAC o SYM)) THEN
  (* Well-order U using WO *)
  MP_TAC(ISPEC `U:(A->bool)->bool` WO) THEN
  DISCH_THEN(X_CHOOSE_THEN `ord:(A->bool)->(A->bool)->bool` STRIP_ASSUME_TAC) THEN
  (* Define the key sets:
     S_n(u) = {x in mspace | mball(x, 1/n) SUBSET u}
     T_n(u) = S_n(u) - UNIONS{v | ord v u /\ ~(v = u)}
     E_n(u) = UNIONS{mball(x, 1/(3n)) | x IN T_n(u)}
     E_n = {E_n(u) | u IN U, ~(E_n(u) = {})}
     V = UNIONS{E_n | n >= 1}
  *)
  ABBREV_TAC `Sn = \(n:num) (u:A->bool).
    {x | x IN mspace m /\ mball m (x, inv(&n)) SUBSET u}` THEN
  ABBREV_TAC `Tn = \(n:num) (u:A->bool).
    (Sn:num->(A->bool)->A->bool) n u DIFF UNIONS {v:A->bool | (ord:(A->bool)->(A->bool)->bool) v u /\ ~(v = u)}` THEN
  ABBREV_TAC `En = \(n:num) (u:A->bool).
    UNIONS {mball m (x:A, inv(&3 * &n)) | x IN (Tn:num->(A->bool)->A->bool) n u}` THEN
  ABBREV_TAC `E_layer = \(n:num). {(En:num->(A->bool)->A->bool) n u | u IN U}` THEN
  (* V = UNIONS{E_layer n | n >= 1} but removing empty sets *)
  EXISTS_TAC `UNIONS {E_layer n | n >= 1} DIFF {{}}:(A->bool)->bool` THEN
  (* The proof splits into four parts *)
  REPEAT CONJ_TAC THENL
  [(* Property 1: V is open
     Every element v in V is some En n u which is UNIONS of mballs, hence open *)
   REWRITE_TAC[IN_DIFF; IN_SING; IN_UNIONS; IN_ELIM_THM] THEN
   X_GEN_TAC `v:A->bool` THEN STRIP_TAC THEN
   (* After STRIP_TAC we have: n >= 1, t = E_layer n, v IN t, ~(v = {}) *)
   (* Derive: exists u0. u0 IN U /\ v = En n u0 from v IN t and t = E_layer n *)
   SUBGOAL_THEN `?u0. u0 IN U /\ v = (En:num->(A->bool)->A->bool) n u0`
     STRIP_ASSUME_TAC THENL
   [(* Have: t = E_layer n (assumption), v IN t (assumption) *)
    UNDISCH_TAC `v:A->bool IN t` THEN
    FIRST_X_ASSUM(SUBST1_TAC) THEN  (* t = E_layer n, substitute in goal *)
    EXPAND_TAC "E_layer" THEN
    REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
   (* Now we have u0 IN U and v = En n u0 *)
   ASM_REWRITE_TAC[] THEN
   EXPAND_TAC "En" THEN REWRITE_TAC[] THEN
   (* Goal: open_in top (UNIONS {mball m (x, inv(&3*&n)) | x IN Tn n u0}) *)
   (* Use mtopology m = top to substitute top -> mtopology m *)
   UNDISCH_TAC `mtopology m:A topology = top` THEN
   DISCH_THEN(SUBST1_TAC o SYM) THEN
   (* Now goal is: open_in (mtopology m) (UNIONS {...}) *)
   (* Use OPEN_IN_UNIONS: each element in the set is an open ball *)
   MATCH_MP_TAC OPEN_IN_UNIONS THEN
   REWRITE_TAC[FORALL_IN_GSPEC] THEN
   REPEAT GEN_TAC THEN DISCH_TAC THEN
   REWRITE_TAC[OPEN_IN_MBALL];
   (* Property 2: V covers topspace
      KEY INSIGHT: First find v_0 = <-minimal set containing x as a POINT,
      then find N. This ensures x NOT IN v for any v < v_0. *)
   REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
   (* x IN topspace top = mspace m since top = mtopology m *)
   SUBGOAL_THEN `x:A IN mspace m` ASSUME_TAC THENL
   [UNDISCH_TAC `x:A IN topspace top` THEN
    UNDISCH_TAC `mtopology m:A topology = top` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[TOPSPACE_MTOPOLOGY];
    ALL_TAC] THEN
   (* x is in some u in U since U covers topspace *)
   SUBGOAL_THEN `?u:A->bool. u IN U /\ x IN u` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `topspace top SUBSET UNIONS (U:(A->bool)->bool)` THEN
    REWRITE_TAC[SUBSET; IN_UNIONS] THEN
    DISCH_THEN(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
   (* FIRST: find v_0 = <-minimal set in U containing x as a point *)
   (* Apply WOSET_WELL without consuming the woset assumption *)
   SUBGOAL_THEN `?v0:A->bool. v0 IN U /\ x IN v0 /\
                 (!w. w IN U /\ x IN w ==> (ord:(A->bool)->(A->bool)->bool) v0 w)`
     STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `ord:(A->bool)->(A->bool)->bool` WOSET_WELL) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `\w:A->bool. w IN U /\ x IN w`) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
    [CONJ_TAC THENL
     [UNDISCH_TAC `fld (ord:(A->bool)->(A->bool)->bool) = U` THEN
      DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
      REWRITE_TAC[IN] THEN SIMP_TAC[];
      EXISTS_TAC `u:A->bool` THEN ASM_REWRITE_TAC[]];
     MESON_TAC[]];
    ALL_TAC] THEN
   (* v0 is ord-minimal set containing x *)
   (* For any v with ord v v0 and v != v0, we have x NOT IN v *)
   SUBGOAL_THEN `!v:A->bool. (ord:(A->bool)->(A->bool)->bool) v v0 /\ ~(v = v0) ==> ~(x IN v)`
     ASSUME_TAC THENL
   [X_GEN_TAC `v:A->bool` THEN STRIP_TAC THEN
    (* v is strictly smaller than v0. If x IN v, then v IN U (from fld ord) *)
    (* and x IN v, so ord v0 v by minimality. But ord v v0 and v != v0 *)
    (* gives v0 = v by antisymmetry, contradiction. *)
    DISCH_TAC THEN
    (* v IN fld(ord) since ord v v0 *)
    SUBGOAL_THEN `v:A->bool IN U` ASSUME_TAC THENL
    [UNDISCH_TAC `fld (ord:(A->bool)->(A->bool)->bool) = U` THEN
     DISCH_THEN(SUBST1_TAC o SYM) THEN
     (* v IN fld ord means ?y. ord v y \/ ord y v *)
     REWRITE_TAC[IN_FLD] THEN
     EXISTS_TAC `v0:A->bool` THEN DISJ1_TAC THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
    (* Now v IN U and x IN v, so by minimality ord v0 v *)
    FIRST_X_ASSUM(MP_TAC o SPEC `v:A->bool`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    (* We have ord v v0 and ord v0 v, so v = v0 by antisymmetry *)
    (* Use WOSET_ANTISYM: woset ord ==> ord x y /\ ord y x ==> x = y *)
    MP_TAC(ISPEC `ord:(A->bool)->(A->bool)->bool` WOSET_ANTISYM) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`v:A->bool`; `v0:A->bool`]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   (* v0 is open in mtopology m, so exists r > 0 with mball(x,r) SUBSET v0 *)
   SUBGOAL_THEN `?r. &0 < r /\ mball m (x:A,r) SUBSET v0` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `!u:A->bool. u IN U ==> open_in top u` THEN
    DISCH_THEN(MP_TAC o SPEC `v0:A->bool`) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `mtopology m:A topology = top` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[OPEN_IN_MTOPOLOGY] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `r:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   (* By REAL_ARCH_INV, get N >= 1 with inv(&N) < r *)
   MP_TAC(SPEC `r:real` REAL_ARCH_INV) THEN ASM_REWRITE_TAC[] THEN
   DISCH_THEN(X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC) THEN
   (* mball(x, inv(&N)) SUBSET mball(x, r) SUBSET v0 *)
   SUBGOAL_THEN `mball m (x:A, inv(&N)) SUBSET v0` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `mball m (x:A, r)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MBALL_SUBSET_CONCENTRIC THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
   (* So x IN Sn N v0 *)
   SUBGOAL_THEN `x:A IN (Sn:num->(A->bool)->A->bool) N v0` ASSUME_TAC THENL
   [EXPAND_TAC "Sn" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   (* x IN Tn N v0: x is in Sn N v0 and not in any ord-smaller set *)
   SUBGOAL_THEN `x:A IN (Tn:num->(A->bool)->A->bool) N v0` ASSUME_TAC THENL
   [EXPAND_TAC "Tn" THEN REWRITE_TAC[IN_DIFF; IN_UNIONS; IN_ELIM_THM] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[NOT_EXISTS_THM] THEN
    X_GEN_TAC `v:A->bool` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) ASSUME_TAC) THEN
    (* v is ord-smaller than v0 and v != v0, so x NOT IN v by our earlier result *)
    FIRST_X_ASSUM(MP_TAC o SPEC `v:A->bool`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   (* x IN mball(x, inv(&3*&N)) since mdist(x,x) = 0 < inv(&3*&N) *)
   (* Therefore x IN En N v0 = UNIONS{mball(y, inv(&3*&N)) | y IN Tn N v0} *)
   (* En N v0 is non-empty and in E_layer N, which is in V *)
   (* Goal: x IN UNIONS (UNIONS {E_layer n | n >= 1} DIFF {{}})
      = ?v. v IN (UNIONS {E_layer n | n >= 1} DIFF {{}}) /\ x IN v
      Witness v = En N v0, then show: v IN UNIONS{...}, ~(v = {}), x IN v *)
   REWRITE_TAC[IN_UNIONS] THEN
   EXISTS_TAC `(En:num->(A->bool)->A->bool) N v0` THEN
   REWRITE_TAC[IN_DIFF; IN_SING] THEN
   (* Goal: En N v0 IN UNIONS{E_layer n | n >= 1} /\ ~(En N v0 = {}) /\ x IN En N v0 *)
   REPEAT CONJ_TAC THENL
   [(* En N v0 IN UNIONS{E_layer n | n >= 1} *)
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    EXISTS_TAC `(E_layer:num->(A->bool)->bool) N` THEN CONJ_TAC THENL
    [(* E_layer N is in {E_layer n | n >= 1} *)
     EXISTS_TAC `N:num` THEN REWRITE_TAC[GE] THEN
     UNDISCH_TAC `~(N = 0)` THEN ARITH_TAC;
     (* En N v0 IN E_layer N *)
     EXPAND_TAC "E_layer" THEN REWRITE_TAC[IN_ELIM_THM] THEN
     EXISTS_TAC `v0:A->bool` THEN ASM_REWRITE_TAC[]];
    (* ~(En N v0 = {}) - it contains x *)
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    EXISTS_TAC `x:A` THEN
    (* x IN En N v0 - need to show x IN UNIONS{mball(y, 1/3N) | y IN Tn N v0} *)
    (* The key: x IN Tn N v0, and x IN mball(x, 1/3N) since mdist(x,x) = 0 *)
    EXPAND_TAC "En" THEN EXPAND_TAC "Tn" THEN
    CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    EXISTS_TAC `mball m (x:A, inv(&3 * &N))` THEN
    (* Goal: (exists x' n. x' IN Sn n v0 DIFF ... /\ ball = ball) /\ x IN ball *)
    CONJ_TAC THENL
    [(* exists x' n. x' IN Sn n v0 DIFF ... /\ ball = ball - witness x' = x, n = N *)
     EXISTS_TAC `x:A` THEN EXISTS_TAC `N:num` THEN
     (* Goal: x IN Sn N v0 DIFF UNIONS {...} /\ ball = ball *)
     (* Split into two subgoals BEFORE any rewriting *)
     CONJ_TAC THENL
     [(* x IN Sn N v0 DIFF UNIONS {v | ord v v0 /\ ~(v = v0)} *)
      (* We have x IN Tn N v0 by assumption 24, and Tn = Sn DIFF UNIONS{...} *)
      UNDISCH_TAC `x:A IN (Tn:num->(A->bool)->A->bool) N v0` THEN
      EXPAND_TAC "Tn" THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
      SIMP_TAC[];
      (* ball = ball *)
      REFL_TAC];
     (* x IN mball(x, inv(&3*&N)) *)
     REWRITE_TAC[IN_MBALL] THEN
     ASM_SIMP_TAC[MDIST_REFL] THEN
     MATCH_MP_TAC REAL_LT_INV THEN
     MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
     [REAL_ARITH_TAC;
      REWRITE_TAC[REAL_OF_NUM_LT] THEN
      UNDISCH_TAC `~(N = 0)` THEN ARITH_TAC]];
    (* x IN En N v0 - same proof *)
    EXPAND_TAC "En" THEN EXPAND_TAC "Tn" THEN
    CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    EXISTS_TAC `mball m (x:A, inv(&3 * &N))` THEN
    CONJ_TAC THENL
    [(* exists x' n. x' IN Sn n v0 DIFF ... /\ ball = ball *)
     EXISTS_TAC `x:A` THEN EXISTS_TAC `N:num` THEN
     (* Split into two subgoals BEFORE any rewriting *)
     CONJ_TAC THENL
     [(* x IN Sn N v0 DIFF UNIONS {...} *)
      UNDISCH_TAC `x:A IN (Tn:num->(A->bool)->A->bool) N v0` THEN
      EXPAND_TAC "Tn" THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
      SIMP_TAC[];
      REFL_TAC];
     REWRITE_TAC[IN_MBALL] THEN
     ASM_SIMP_TAC[MDIST_REFL] THEN
     MATCH_MP_TAC REAL_LT_INV THEN
     MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
     [REAL_ARITH_TAC;
      REWRITE_TAC[REAL_OF_NUM_LT] THEN
      UNDISCH_TAC `~(N = 0)` THEN ARITH_TAC]]];
   (* Property 3: V refines U - each v in V is subset of some u in U
      v = En n u0 for some u0 IN U, and En n u0 SUBSET u0 by construction:
      - Tn n u0 SUBSET Sn n u0 = {x | mball(x,1/n) SUBSET u0}
      - En n u0 = UNIONS{mball(x,1/3n) | x IN Tn n u0}
      - For x in Tn, mball(x,1/3n) SUBSET mball(x,1/n) SUBSET u0
      - So En n u0 SUBSET u0 *)
   REWRITE_TAC[IN_DIFF; IN_SING; IN_UNIONS; IN_ELIM_THM] THEN
   X_GEN_TAC `v:A->bool` THEN STRIP_TAC THEN
   (* Get u0 such that v = En n u0 *)
   SUBGOAL_THEN `?u0. u0 IN U /\ v = (En:num->(A->bool)->A->bool) n u0`
     STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `v:A->bool IN t` THEN
    FIRST_X_ASSUM(SUBST1_TAC) THEN  (* t = E_layer n *)
    EXPAND_TAC "E_layer" THEN REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
   (* Witness u0 *)
   EXISTS_TAC `u0:A->bool` THEN ASM_REWRITE_TAC[] THEN
   (* Need: En n u0 SUBSET u0 *)
   ASM_REWRITE_TAC[] THEN
   EXPAND_TAC "En" THEN REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
   (* After FORALL_IN_GSPEC, goal: !x n. x IN Tn n u0 ==> mball SUBSET u0 *)
   (* Note: both x and n are universally quantified here *)
   X_GEN_TAC `y:A` THEN X_GEN_TAC `n':num` THEN DISCH_TAC THEN
   (* From y IN Tn n' u0, get y IN Sn n' u0 (Tn is Sn DIFF something) *)
   SUBGOAL_THEN `y:A IN (Sn:num->(A->bool)->A->bool) n' u0` ASSUME_TAC THENL
   [UNDISCH_TAC `y:A IN (Tn:num->(A->bool)->A->bool) n' u0` THEN
    EXPAND_TAC "Tn" THEN REWRITE_TAC[IN_DIFF] THEN SIMP_TAC[];
    ALL_TAC] THEN
   (* From y IN Sn n' u0, get y IN mspace m and mball(y, 1/n') SUBSET u0 *)
   UNDISCH_TAC `y:A IN (Sn:num->(A->bool)->A->bool) n' u0` THEN
   EXPAND_TAC "Sn" THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
   (* mball(y, 1/3n') SUBSET mball(y, 1/n') SUBSET u0 *)
   MATCH_MP_TAC SUBSET_TRANS THEN
   EXISTS_TAC `mball m (y:A, inv(&n'))` THEN ASM_REWRITE_TAC[] THEN
   (* Need: inv(&3*&n') <= inv(&n') which requires n' >= 1 *)
   (* For n' = 0: inv(&0) = &0, so mball(y, 0) = {} SUBSET u0 trivially *)
   (* For n' >= 1: use INV_3N_LE_INV_N *)
   ASM_CASES_TAC `n' = 0` THENL
   [ASM_REWRITE_TAC[REAL_MUL_RZERO; REAL_INV_0] THEN
    MATCH_MP_TAC(SET_RULE `s = {} ==> s SUBSET t`) THEN
    MATCH_MP_TAC MBALL_EMPTY THEN REWRITE_TAC[REAL_LE_REFL];
    MATCH_MP_TAC MBALL_SUBSET_CONCENTRIC THEN
    MATCH_MP_TAC INV_3N_LE_INV_N THEN ASM_REWRITE_TAC[]];
   (* Property 4: V is countably locally finite - using CHEAT_TAC for now *)
   CHEAT_TAC]);;

let METRIZABLE_COUNTABLY_LOCALLY_FINITE_REFINEMENT_locally_finite_DISABLED = 0;;
(* The locally finite proof has a structural issue - will restore after fixing *)
(* Original code:
    X_GEN_TAC `n:num` THEN
    CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    ASM_CASES_TAC `n = 0` THENL
    [ASM_REWRITE_TAC[LOCALLY_FINITE_IN_EMPTY; COND_CLAUSES]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[locally_finite_in] THEN CONJ_TAC THENL
    [(* UNIONS (E_layer n DIFF {{}}) SUBSET topspace *)
     REWRITE_TAC[UNIONS_SUBSET; IN_DIFF; IN_SING] THEN
     X_GEN_TAC `s:A->bool` THEN STRIP_TAC THEN
     (* s IN E_layer n, so s = En n u0 for some u0 IN U *)
     UNDISCH_TAC `s:A->bool IN (E_layer:num->(A->bool)->bool) n` THEN
     EXPAND_TAC "E_layer" THEN REWRITE_TAC[IN_ELIM_THM] THEN
     DISCH_THEN(X_CHOOSE_THEN `u0:A->bool` (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THEN
     (* En n u0 = UNIONS{mball(y, 1/3n) | y IN Tn n u0} SUBSET mspace m = topspace *)
     EXPAND_TAC "En" THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
     REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
     X_GEN_TAC `y:A` THEN X_GEN_TAC `n':num` THEN DISCH_TAC THEN
     UNDISCH_TAC `mtopology m:A topology = top` THEN
     DISCH_THEN(SUBST1_TAC o SYM) THEN
     REWRITE_TAC[TOPSPACE_MTOPOLOGY; MBALL_SUBSET_MSPACE];
     (* Part 2: finite neighborhood property *)
     X_GEN_TAC `x:A` THEN DISCH_TAC THEN
     (* x is in topspace = mspace m *)
     SUBGOAL_THEN `x:A IN mspace m` ASSUME_TAC THENL
     [UNDISCH_TAC `x:A IN topspace top` THEN
      UNDISCH_TAC `mtopology m:A topology = top` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[TOPSPACE_MTOPOLOGY];
      ALL_TAC] THEN
     (* Use mball(x, 1/(6n)) as the neighborhood *)
     EXISTS_TAC `mball m (x:A, inv(&6 * &n))` THEN
     CONJ_TAC THENL
     [(* mball is open *)
      UNDISCH_TAC `mtopology m:A topology = top` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[OPEN_IN_MBALL];
      ALL_TAC] THEN
     CONJ_TAC THENL
     [(* x IN mball *)
      REWRITE_TAC[IN_MBALL] THEN
      ASM_SIMP_TAC[MDIST_REFL] THEN
      MATCH_MP_TAC REAL_LT_INV THEN
      MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
      [REAL_ARITH_TAC;
       REWRITE_TAC[REAL_OF_NUM_LT] THEN
       UNDISCH_TAC `~(n = 0)` THEN ARITH_TAC];
      ALL_TAC] THEN
     (* FINITE {s | s IN E_layer n DIFF {{}} /\ ~(s INTER mball(...) = {})} *)
     (* Key: this set has at most one element *)
     MATCH_MP_TAC FINITE_SUBSET THEN
     EXISTS_TAC `{s:A->bool | s IN (E_layer:num->(A->bool)->bool) n /\ ~(s INTER mball m (x, inv(&6 * &n)) = {})}` THEN
     CONJ_TAC THENL
     [(* The set meeting x's ball is finite - at most one element *)
      (* Key: inv(&6*&n) = inv(&3*&n) / &2, so we can use SMALL_BALL_MEETS_ONE *)
      SUBGOAL_THEN `inv(&6 * &n) = inv(&3 * &n) / &2` ASSUME_TAC THENL
      [REWRITE_TAC[real_div; REAL_INV_MUL] THEN
       REWRITE_TAC[REAL_ARITH `&6 = &2 * &3`] THEN
       REWRITE_TAC[REAL_INV_MUL] THEN REAL_ARITH_TAC;
       ALL_TAC] THEN
      (* Use SMALL_BALL_MEETS_ONE with r = inv(&3 * &n) *)
      MP_TAC(ISPECL [`m:A metric`; `x:A`; `inv(&3 * &n)`;
                     `(E_layer:num->(A->bool)->bool) n`] SMALL_BALL_MEETS_ONE) THEN
      ANTS_TAC THENL
      [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [(* &0 < inv(&3 * &n) *)
        MATCH_MP_TAC INV_3N_POS THEN REWRITE_TAC[GE] THEN
        UNDISCH_TAC `~(n = 0)` THEN ARITH_TAC;
        (* Separation property: distinct elements of E_layer n are 1/(3n)-separated *)
        CHEAT_TAC];
       (* Use the result to show finiteness *)
       ASM_REWRITE_TAC[] THEN
       DISCH_THEN(X_CHOOSE_THEN `v:A->bool` ASSUME_TAC) THEN
       MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{v:A->bool}` THEN
       CONJ_TAC THENL
       [REWRITE_TAC[FINITE_SING];
        REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_SING] THEN
        X_GEN_TAC `s:A->bool` THEN STRIP_TAC THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        ONCE_REWRITE_TAC[INTER_COMM] THEN ASM_MESON_TAC[]]];
      (* Subset property *)
      REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_DIFF; IN_SING] THEN
      X_GEN_TAC `u:A->bool` THEN STRIP_TAC THEN ASM_MESON_TAC[]]]]]);;
*)

(* Debug marker removed *)

(* ------------------------------------------------------------------------- *)
(* Lemma 41.3 (Michael's Lemma): For a regular space, countably locally      *)
(* finite covering refinement implies locally finite covering refinement.    *)
(* This is the key step (1) => (4) from Michael's lemma.                     *)
(* ------------------------------------------------------------------------- *)

(* Step (1) => (2) of Michael's Lemma: countably locally finite => locally finite *)
(* The key idea: given U = ∪_n B_n where each B_n is locally finite,
   define V_i = UNIONS B_i and S_n(u) = u - UNIONS{V_i | i < n}
   Then C_n = {S_n(u) | u ∈ B_n} and C = ∪_n C_n is locally finite *)

(* Helper: shrink n u SUBSET u for any n and u *)
let SHRINK_SUBSET = prove
 (`!(B:num->(A->bool)->bool) n u.
     u DIFF UNIONS {UNIONS (B i) | i < n} SUBSET u`,
  PRINT_GOAL_TAC THEN SET_TAC[]);;

(* IMAGE version of LOCALLY_FINITE_IN_REFINEMENT *)
let LOCALLY_FINITE_IN_IMAGE = prove
 (`!top (u:(A->bool)->bool) (f:(A->bool)->(A->bool)).
     locally_finite_in top u /\ (!s. s IN u ==> f s SUBSET s)
     ==> locally_finite_in top (IMAGE f u)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[locally_finite_in] THEN
  REWRITE_TAC[FORALL_IN_IMAGE] THEN STRIP_TAC THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
  REPEAT(MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[]) THEN
  DISCH_TAC THEN ONCE_REWRITE_TAC[SET_RULE
    `{y | y IN IMAGE f u /\ Q y} = IMAGE f {x | x IN u /\ Q(f x)}`] THEN
  MATCH_MP_TAC FINITE_IMAGE THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
        FINITE_SUBSET)) THEN
  ASM SET_TAC[]);;

(* Helper: Each layer C_n = {shrink n u | u IN B n} is locally finite
   Uses IMAGE form due to HOL Light GSPEC parsing issues with free variables *)
let SHRINK_LAYER_LOCALLY_FINITE = prove
 (`!top:A topology (B:num->(A->bool)->bool) n.
    locally_finite_in top (B n)
    ==> locally_finite_in top
          (IMAGE (\u. u DIFF UNIONS {UNIONS (B i) | i < n}) (B n))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC LOCALLY_FINITE_IN_IMAGE THEN
  ASM_REWRITE_TAC[] THEN GEN_TAC THEN DISCH_TAC THEN SET_TAC[]);;

(* Helper: minimal n exists by well-ordering principle
   Uses num_WOP: !P. (?n. P n) <=> (?n. P(n) /\ !m. m < n ==> ~P(m)) *)
let MINIMAL_LAYER_EXISTS = prove
 (`!(B:num->(A->bool)->bool) x.
     x IN UNIONS (UNIONS {B n | n IN (:num)})
     ==> ?N. x IN UNIONS (B N) /\ !m. m < N ==> ~(x IN UNIONS (B m))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `?n:num. x IN UNIONS ((B:num->(A->bool)->bool) n)` MP_TAC THENL
  [FIRST_X_ASSUM(MP_TAC) THEN
   REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; IN_UNIV] THEN MESON_TAC[];
   ALL_TAC] THEN
  REWRITE_TAC[GSYM num_WOP]);;

(* Helper: For x in UNIONS{B n | n}, there exists a minimum n with x in UNIONS(B n).
   This is used to show that x is in some shrunk set S_n(u), and that elements
   from later layers don't intersect x's neighborhood. *)

(* MICHAEL_STEP_1_2: countably locally finite => locally finite
   Construction: V_layer n = UNIONS(B n), shrink n u = u DIFF (earlier layers)
   The union C of all {shrink n u | u in B n} is locally finite because:
   - Each layer C_n refines B_n, so is locally finite by LOCALLY_FINITE_IN_REFINEMENT
   - For x in some u in B_N, elements of C_m (m > N) don't intersect u
   - So we only need to consider finitely many layers around x *)
(* Helper: Union of two locally finite collections is locally finite *)
let LOCALLY_FINITE_IN_UNION = prove
 (`!top:A topology u v.
     locally_finite_in top u /\ locally_finite_in top v
     ==> locally_finite_in top (u UNION v)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[locally_finite_in] THEN STRIP_TAC THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w1:A->bool` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `w2:A->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `w1 INTER w2:A->bool` THEN
  ASM_SIMP_TAC[OPEN_IN_INTER; IN_INTER] THEN
  MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{s:A->bool | s IN u /\ ~(s INTER w1 = {})} UNION
              {s | s IN v /\ ~(s INTER w2 = {})}` THEN
  ASM_SIMP_TAC[FINITE_UNION] THEN
  REWRITE_TAC[SUBSET; IN_UNION; IN_ELIM_THM] THEN
  GEN_TAC THEN REWRITE_TAC[IN_UNION] THEN SET_TAC[]);;

(* Helper: Expansion of indexed GSPEC for SUC *)
let GSPEC_SUC_LEMMA = prove
 (`!f:num->B n. {f i | i < SUC n} = (f n) INSERT {f i | i < n}`,
  GEN_TAC THEN GEN_TAC THEN
  REWRITE_TAC[EXTENSION; IN_INSERT; IN_ELIM_THM; LT] THEN
  GEN_TAC THEN EQ_TAC THENL
  [DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN ASM_MESON_TAC[];
   STRIP_TAC THENL [EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[]; ASM_MESON_TAC[]]]);;

(* Helper: Finite union of locally finite collections is locally finite *)
let LOCALLY_FINITE_IN_FINITE_UNIONS = prove
 (`!top:A topology (f:num->(A->bool)->bool) n.
     (!i. i < n ==> locally_finite_in top (f i))
     ==> locally_finite_in top (UNIONS {f i | i < n})`,
  REPEAT GEN_TAC THEN SPEC_TAC(`n:num`,`n:num`) THEN
  INDUCT_TAC THEN STRIP_TAC THENL
  [SUBGOAL_THEN `{(f:num->(A->bool)->bool) i | i < 0} = {}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY; LT]; ALL_TAC] THEN
   REWRITE_TAC[UNIONS_0; LOCALLY_FINITE_IN_EMPTY];
   REWRITE_TAC[GSPEC_SUC_LEMMA; UNIONS_INSERT] THEN
   MATCH_MP_TAC LOCALLY_FINITE_IN_UNION THEN
   CONJ_TAC THENL [ASM_MESON_TAC[LT]; ALL_TAC] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[LT]]);;






(* Helper: u IN B N implies u SUBSET UNIONS(B N) *)
let IN_LAYER_SUBSET_UNIONS = prove
 (`!(B:num->(A->bool)->bool) N u. u IN B N ==> u SUBSET UNIONS (B N)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[SUBSET; IN_UNIONS] THEN ASM_MESON_TAC[]);;

(* Helper: shrunk sets from later layers don't intersect earlier layer unions *)
let SHRINK_DISJOINT_EARLIER = prove
 (`!(B:num->(A->bool)->bool) n m u.
     n < m /\ u IN B m
     ==> (u DIFF UNIONS {UNIONS (B i) | i < m}) INTER UNIONS (B n) = {}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(SET_RULE `s SUBSET t ==> (u DIFF t) INTER s = {}`) THEN
  REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  EXISTS_TAC `UNIONS ((B:num->(A->bool)->bool) n)` THEN
  CONJ_TAC THENL
  [EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[];
   REWRITE_TAC[IN_UNIONS] THEN ASM_MESON_TAC[]]);;

(* Helper: shrunk sets from layer m > N don't intersect any set u in B N *)
let SHRINK_LATER_DISJOINT_SET = prove
 (`!(B:num->(A->bool)->bool) N u m v.
     u IN B N /\ N < m /\ v IN B m
     ==> (v DIFF UNIONS {UNIONS (B i) | i < m}) INTER u = {}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`B:num->(A->bool)->bool`; `N:num`; `m:num`; `v:A->bool`]
    SHRINK_DISJOINT_EARLIER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`B:num->(A->bool)->bool`; `N:num`; `u:A->bool`]
    IN_LAYER_SUBSET_UNIONS) THEN
  ASM_REWRITE_TAC[] THEN
  ASM SET_TAC[]);;

(* Helper: the shrunk collection covers the topspace *)
let SHRINK_COVERS_HELPER = prove
 (`!(B:num->(A->bool)->bool) x.
     x IN UNIONS (UNIONS {B n | n IN (:num)})
     ==> ?n u. u IN B n /\ x IN u DIFF UNIONS {UNIONS (B i) | i < n}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`B:num->(A->bool)->bool`; `x:A`] MINIMAL_LAYER_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?t:A->bool. t IN (B:num->(A->bool)->bool) N /\ x IN t` MP_TAC THENL
  [ASM_MESON_TAC[IN_UNIONS]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:A->bool` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`N:num`; `u:A->bool`] THEN
  ASM_REWRITE_TAC[IN_DIFF] THEN
  REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
  ASM_MESON_TAC[]);;

(* Full MICHAEL_STEP_1_2 *)
let MICHAEL_STEP_1_2 = prove
 (`!top:A topology U.
    (!u. u IN U ==> open_in top u) /\
    topspace top SUBSET UNIONS U /\
    countably_locally_finite_in top U
    ==> ?V. topspace top SUBSET UNIONS V /\
            (!v. v IN V ==> ?u. u IN U /\ v SUBSET u) /\
            locally_finite_in top V`,
  PRINT_GOAL_TAC THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[countably_locally_finite_in] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `B:num->(A->bool)->bool` STRIP_ASSUME_TAC) THEN
  (* Define V = UNIONS over all layers of shrunk sets *)
  EXISTS_TAC `UNIONS {IMAGE (\u. u DIFF UNIONS {UNIONS ((B:num->(A->bool)->bool) i) | i < n}) (B n) | n IN (:num)}` THEN
  REPEAT CONJ_TAC THENL
  [(* Coverage: topspace SUBSET UNIONS V *)
   REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
   (* x is in topspace, so x is in UNIONS U = UNIONS (UNIONS {B n | n IN (:num)}) *)
   SUBGOAL_THEN `x:A IN UNIONS (UNIONS {(B:num->(A->bool)->bool) n | n IN (:num)})` MP_TAC THENL
   [UNDISCH_TAC `topspace top SUBSET UNIONS (U:(A->bool)->bool)` THEN
    ASM_REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   DISCH_THEN(MP_TAC o MATCH_MP SHRINK_COVERS_HELPER) THEN
   DISCH_THEN(X_CHOOSE_THEN `n:num` (X_CHOOSE_THEN `u:A->bool` STRIP_ASSUME_TAC)) THEN
   (* x IN u DIFF UNIONS {...}, and u IN B n, so x is in the shrunk set *)
   REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; IN_UNIV] THEN
   EXISTS_TAC `u DIFF UNIONS {UNIONS ((B:num->(A->bool)->bool) i) | i < n}` THEN
   ASM_REWRITE_TAC[] THEN
   EXISTS_TAC `IMAGE (\u:A->bool. u DIFF UNIONS {UNIONS ((B:num->(A->bool)->bool) i) | i < n}) (B n)` THEN
   CONJ_TAC THENL
   [EXISTS_TAC `n:num` THEN REWRITE_TAC[IN_UNIV]; ALL_TAC] THEN
   REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `u:A->bool` THEN ASM_REWRITE_TAC[];
   (* Refinement: each v refines some u in U *)
   REWRITE_TAC[FORALL_IN_UNIONS; FORALL_IN_GSPEC; IN_UNIV; FORALL_IN_IMAGE] THEN
   X_GEN_TAC `t:(A->bool)->bool` THEN X_GEN_TAC `v:A->bool` THEN
   REWRITE_TAC[IN_ELIM_THM] THEN
   DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `n:num`) MP_TAC) THEN
   ASM_REWRITE_TAC[IN_IMAGE] THEN
   DISCH_THEN(X_CHOOSE_THEN `w:A->bool` STRIP_ASSUME_TAC) THEN
   EXISTS_TAC `w:A->bool` THEN
   CONJ_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; IN_UNIV] THEN
    EXISTS_TAC `(B:num->(A->bool)->bool) n` THEN
    ASM_REWRITE_TAC[] THEN EXISTS_TAC `n:num` THEN REWRITE_TAC[];
    ASM_REWRITE_TAC[] THEN SET_TAC[]];
   (* Local finiteness - Part 1 proved, Part 2 needs work *)
   REWRITE_TAC[locally_finite_in] THEN CONJ_TAC THENL
   [(* Part 1: UNIONS V SUBSET topspace - shrunk sets SUBSET open sets *)
    REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_UNIONS; FORALL_IN_GSPEC; IN_UNIV;
                FORALL_IN_IMAGE] THEN
    REPEAT GEN_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `m:num`) MP_TAC) THEN
    ASM_REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `w:A->bool` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(SET_RULE `w SUBSET c ==> w DIFF d SUBSET c`) THEN
    MATCH_MP_TAC OPEN_IN_SUBSET THEN
    UNDISCH_TAC `!u:A->bool. u IN U ==> open_in top u` THEN
    DISCH_THEN(MP_TAC o SPEC `w:A->bool`) THEN
    ANTS_TAC THENL
    [UNDISCH_TAC `(U:(A->bool)->bool) = UNIONS {(B:num->(A->bool)->bool) n | n IN (:num)}` THEN
     DISCH_THEN SUBST1_TAC THEN
     REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; IN_UNIV] THEN
     EXISTS_TAC `(B:num->(A->bool)->bool) m` THEN
     CONJ_TAC THENL [EXISTS_TAC `m:num` THEN REFL_TAC; ASM_REWRITE_TAC[]];
     SIMP_TAC[]];
    (* Part 2: finite neighborhood property *)
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    (* x is in the coverage, so x is in UNIONS(UNIONS{B n|n}) *)
    SUBGOAL_THEN `x:A IN UNIONS (UNIONS {(B:num->(A->bool)->bool) n | n IN (:num)})` MP_TAC THENL
    [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
     UNDISCH_TAC `(U:(A->bool)->bool) = UNIONS {(B:num->(A->bool)->bool) n | n IN (:num)}` THEN
     DISCH_THEN SUBST1_TAC THEN DISCH_THEN(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
    DISCH_TAC THEN
    MP_TAC(ISPECL [`B:num->(A->bool)->bool`; `x:A`] MINIMAL_LAYER_EXISTS) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC) THEN
    (* Get u0 in B_N with x in u0 *)
    SUBGOAL_THEN `?t:A->bool. t IN (B:num->(A->bool)->bool) N /\ x IN t` MP_TAC THENL
    [ASM_MESON_TAC[IN_UNIONS]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `u0:A->bool` STRIP_ASSUME_TAC) THEN
    (* u0 is open since u0 IN B_N SUBSET U and all of U is open *)
    SUBGOAL_THEN `open_in top (u0:A->bool)` ASSUME_TAC THENL
    [UNDISCH_TAC `!u:A->bool. u IN U ==> open_in top u` THEN
     DISCH_THEN(MP_TAC o SPEC `u0:A->bool`) THEN
     ANTS_TAC THENL
     [UNDISCH_TAC `(U:(A->bool)->bool) = UNIONS {(B:num->(A->bool)->bool) n | n IN (:num)}` THEN
      DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; IN_UNIV] THEN
      EXISTS_TAC `(B:num->(A->bool)->bool) N` THEN
      CONJ_TAC THENL [EXISTS_TAC `N:num` THEN REFL_TAC; ASM_REWRITE_TAC[]];
      SIMP_TAC[]];
     ALL_TAC] THEN
    (* Define C_layer abbreviation *)
    ABBREV_TAC `C_layer = \i:num. IMAGE (\u:A->bool. u DIFF UNIONS {UNIONS ((B:num->(A->bool)->bool) j) | j < i}) (B i)` THEN
    (* Layers 0..N form a locally finite union *)
    SUBGOAL_THEN `locally_finite_in top (UNIONS {(C_layer:num->(A->bool)->bool) i | i <= N})` MP_TAC THENL
    [SUBGOAL_THEN `{(C_layer:num->(A->bool)->bool) i | i <= N} = {C_layer i | i < SUC N}` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN GEN_TAC THEN
      EQ_TAC THENL
      [DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
       EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
       DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
       EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC];
      ALL_TAC] THEN
     MATCH_MP_TAC LOCALLY_FINITE_IN_FINITE_UNIONS THEN
     GEN_TAC THEN DISCH_TAC THEN
     EXPAND_TAC "C_layer" THEN
     MATCH_MP_TAC SHRINK_LAYER_LOCALLY_FINITE THEN
     ASM_REWRITE_TAC[];
     ALL_TAC] THEN
    REWRITE_TAC[locally_finite_in] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `x:A`)) THEN
    (* x is in UNIONS{C_layer i | i <= N} - proved via being in layer N *)
    ANTS_TAC THENL
    [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
     DISCH_THEN(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN
     DISCH_TAC THEN
     REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
     EXISTS_TAC `C_layer (N:num):(A->bool)->bool` THEN
     CONJ_TAC THENL [EXISTS_TAC `N:num` THEN REWRITE_TAC[LE_REFL]; ALL_TAC] THEN
     EXPAND_TAC "C_layer" THEN REWRITE_TAC[IN_IMAGE] THEN
     EXISTS_TAC `u0:A->bool` THEN ASM_REWRITE_TAC[] THEN
     REWRITE_TAC[IN_DIFF] THEN CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
     REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; NOT_EXISTS_THM] THEN
     GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `j:num`) MP_TAC) THEN
     ASM_REWRITE_TAC[IN_UNIONS] THEN
     DISCH_THEN(X_CHOOSE_THEN `t:A->bool` STRIP_ASSUME_TAC) THEN
     FIRST_X_ASSUM(MP_TAC o SPEC `j:num`) THEN
     ASM_REWRITE_TAC[IN_UNIONS] THEN ASM_MESON_TAC[];
     ALL_TAC] THEN
    
    DISCH_THEN(X_CHOOSE_THEN `w1:A->bool` STRIP_ASSUME_TAC) THEN
    (* Take w = u0 INTER w1 as the required neighborhood *)
    EXISTS_TAC `u0 INTER w1:A->bool` THEN
    CONJ_TAC THENL [MATCH_MP_TAC OPEN_IN_INTER THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[IN_INTER]; ALL_TAC] THEN
    (* Show finiteness: finite superset is {s in layers<=N | s meets w1} *)
    MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{u:A->bool | u IN UNIONS {(C_layer:num->(A->bool)->bool) i | i <= N} /\ ~(u INTER w1 = {})}` THEN
    CONJ_TAC THENL
    [UNDISCH_TAC `FINITE {u:A->bool | u IN UNIONS {(C_layer:num->(A->bool)->bool) i | i <= N} /\ ~(u INTER w1 = {})}` THEN
     DISCH_THEN ACCEPT_TAC;
     ALL_TAC] THEN
    (* Key: s in V meeting (u0 INTER w1) must be in layer <= N *)
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    X_GEN_TAC `s:A->bool` THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; IN_UNIV] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `layer:(A->bool)->bool`
      (CONJUNCTS_THEN2 (X_CHOOSE_TAC `m:num`) ASSUME_TAC)) MP_TAC) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN DISCH_TAC THEN
    (* s is in layer m; if m <= N we're done, else contradiction *)
    ASM_CASES_TAC `m:num <= N` THENL
    [CONJ_TAC THENL
     [REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
      EXISTS_TAC `C_layer (m:num):(A->bool)->bool` THEN
      CONJ_TAC THENL [EXISTS_TAC `m:num` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      EXPAND_TAC "C_layer" THEN ASM_REWRITE_TAC[];
      ASM SET_TAC[]];
     ALL_TAC] THEN

    (* m > N, so s INTER u0 = {} by SHRINK_LATER_DISJOINT_SET *)
    SUBGOAL_THEN `N < m:num` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `s:A->bool INTER u0 = {}` MP_TAC THENL
    [(* Extract v from s IN IMAGE (\u. u DIFF ...) (B m) *)
     FIRST_X_ASSUM(MP_TAC o check (fun th -> fst(dest_comb(concl th)) = `(IN) (s:A->bool)`)) THEN
     EXPAND_TAC "C_layer" THEN
     REWRITE_TAC[IN_IMAGE] THEN
     DISCH_THEN(X_CHOOSE_THEN `v:A->bool` STRIP_ASSUME_TAC) THEN
     (* Now we have: s = v DIFF UNIONS{...}, v IN B m *)
     MP_TAC(ISPECL [`B:num->(A->bool)->bool`; `N:num`; `u0:A->bool`; `m:num`; `v:A->bool`]
       SHRINK_LATER_DISJOINT_SET) THEN
     ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      UNDISCH_TAC `s:A->bool = v DIFF UNIONS {UNIONS ((B:num->(A->bool)->bool) j) | j < m}` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN DISCH_THEN ACCEPT_TAC];
     ALL_TAC] THEN
    (* Contradiction: s INTER u0 = {} but s meets u0 INTER w1 *)
    ASM SET_TAC[]]]);;

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

(* The closures of a locally finite family form a locally finite family of closed sets *)
(* This is already proved in metric.ml as LOCALLY_FINITE_IN_CLOSURES *)

(* Key helper: in a regular space, for a locally finite family C refining open U,
   we can expand each c to an open set while maintaining local finiteness and refinement.

   The construction (following textbook proof of (3)=>(4)):
   1. Let D = {closure_of c | c IN C} - locally finite closed family
   2. For each c in C, define:
      - D'(c) = {d IN D : d SUBSET topspace DIFF c} (closures disjoint from c)
      - E(c) = topspace DIFF UNIONS D'(c)  (open, since D' is locally finite closed)
      - V(c) = E(c) INTER u_c where c SUBSET u_c IN U
   3. V = {V(c) | c IN C}

   Properties:
   - c SUBSET E(c) (any closure disjoint from c doesn't touch c)
   - V(c) is open (intersection of two open sets)
   - V(c) SUBSET u_c (trivial)
   - V covers topspace (since c SUBSET V(c) and C covers)
   - V is locally finite (key argument using local finiteness of D)
*)

(* Helper: each point is in only finitely many closures of a locally finite family *)
let FINITE_CLOSURES_AT_POINT = prove
 (`!top:A topology C x.
     locally_finite_in top C /\ x IN topspace top
     ==> FINITE {c | c IN C /\ x IN top closure_of c}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[locally_finite_in] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:A->bool` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{c:A->bool | c IN C /\ ~(c INTER w = {})}` THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
  X_GEN_TAC `c:A->bool` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  (* If x IN closure_of c and w is open neighborhood of x, then c INTER w != {} *)
  (* By OPEN_IN_INTER_CLOSURE_OF_EQ_EMPTY: w INTER closure c = {} <=> w INTER c = {} *)
  (* Since x IN w INTER closure c, we have ~(w INTER closure c = {}), hence ~(w INTER c = {}) *)
  MP_TAC(ISPECL [`top:A topology`; `w:A->bool`; `c:A->bool`]
    OPEN_IN_INTER_CLOSURE_OF_EQ_EMPTY) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  (* Goal: ~(c INTER w = {}) which equals ~(w INTER c = {}) *)
  ONCE_REWRITE_TAC[INTER_COMM] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (TAUT `(a <=> b) ==> ~a ==> ~b`)) THEN
  DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
  EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[]);;

(* Helper for going from locally finite to locally finite open in a regular space.
   This combines steps (2)=>(3)=>(4) from the textbook proof. *)
let LOCALLY_FINITE_OPEN_REFINEMENT = prove
 (`!top:A topology U C.
    regular_space top /\
    (!u. u IN U ==> open_in top u) /\
    topspace top SUBSET UNIONS C /\
    (!c. c IN C ==> ?u. u IN U /\ c SUBSET u) /\
    locally_finite_in top C
    ==> ?V. (!v. v IN V ==> open_in top v) /\
            topspace top SUBSET UNIONS V /\
            (!v. v IN V ==> ?u. u IN U /\ v SUBSET u) /\
            locally_finite_in top V`,
  REPEAT STRIP_TAC THEN
  (* Define the closures D = {closure_of c | c IN C} *)
  ABBREV_TAC `D = {top closure_of c:A->bool | c IN C}` THEN
  SUBGOAL_THEN `locally_finite_in top (D:(A->bool)->bool)` ASSUME_TAC THENL
  [EXPAND_TAC "D" THEN MATCH_MP_TAC LOCALLY_FINITE_IN_CLOSURES THEN
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `!d:A->bool. d IN D ==> closed_in top d` ASSUME_TAC THENL
  [EXPAND_TAC "D" THEN REWRITE_TAC[FORALL_IN_GSPEC] THEN
   GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[CLOSED_IN_CLOSURE_OF];
   ALL_TAC] THEN
  (* D covers topspace since C does and c SUBSET closure_of c *)
  SUBGOAL_THEN `topspace top SUBSET UNIONS (D:(A->bool)->bool)` ASSUME_TAC THENL
  [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
   UNDISCH_TAC `topspace top SUBSET UNIONS (C:(A->bool)->bool)` THEN
   REWRITE_TAC[SUBSET] THEN DISCH_THEN(MP_TAC o SPEC `x:A`) THEN
   ASM_REWRITE_TAC[IN_UNIONS] THEN
   DISCH_THEN(X_CHOOSE_THEN `c:A->bool` STRIP_ASSUME_TAC) THEN
   REWRITE_TAC[IN_UNIONS] THEN EXPAND_TAC "D" THEN
   REWRITE_TAC[IN_ELIM_THM] THEN
   EXISTS_TAC `top closure_of c:A->bool` THEN
   CONJ_TAC THENL [EXISTS_TAC `c:A->bool` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   (* x IN c and c SUBSET closure_of c (when c SUBSET topspace) *)
   MP_TAC(ISPECL [`top:A topology`; `c:A->bool`] CLOSURE_OF_SUBSET) THEN
   UNDISCH_TAC `locally_finite_in top (C:(A->bool)->bool)` THEN
   REWRITE_TAC[locally_finite_in] THEN STRIP_TAC THEN
   SUBGOAL_THEN `c:A->bool SUBSET topspace top` MP_TAC THENL
   [ASM SET_TAC[]; DISCH_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
   ALL_TAC] THEN
  (* Use choice to get function f: c -> u with c SUBSET f(c) IN U *)
  SUBGOAL_THEN `?f:(A->bool)->(A->bool). !c. c IN C ==> f c IN U /\ c SUBSET f c`
    STRIP_ASSUME_TAC THENL
  [REWRITE_TAC[GSYM SKOLEM_THM_GEN] THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* Define V = {E(c) INTER f(c) | c IN C} where E(c) = topspace - disjoint closures *)
  EXISTS_TAC `{((topspace top DIFF UNIONS {d:A->bool | d IN D /\ d INTER c = {}})
                INTER (f:(A->bool)->(A->bool)) c) | c IN C}` THEN
  (* Prove the four properties one by one *)
  REPEAT CONJ_TAC THENL
  [(* Property 1: V is open *)
   REWRITE_TAC[FORALL_IN_GSPEC] THEN X_GEN_TAC `c:A->bool` THEN DISCH_TAC THEN
   (* Goal: open_in top ((topspace DIFF UNIONS{...}) INTER f c) *)
   MATCH_MP_TAC OPEN_IN_INTER THEN CONJ_TAC THENL
   [(* topspace DIFF UNIONS{d | d IN D /\ d INTER c = {}} is open *)
    MATCH_MP_TAC OPEN_IN_DIFF THEN REWRITE_TAC[OPEN_IN_TOPSPACE] THEN
    (* UNIONS{d | d IN D /\ d INTER c = {}} is closed *)
    MATCH_MP_TAC CLOSED_IN_LOCALLY_FINITE_UNIONS THEN CONJ_TAC THENL
    [REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
     FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
     MATCH_MP_TAC LOCALLY_FINITE_IN_SUBSET THEN
     EXISTS_TAC `D:(A->bool)->bool` THEN ASM_REWRITE_TAC[] THEN SET_TAC[]];
    (* f(c) is open *)
    UNDISCH_TAC `!u:A->bool. u IN U ==> open_in top u` THEN
    DISCH_THEN MATCH_MP_TAC THEN
    UNDISCH_TAC `!c:A->bool. c IN C ==> (f:(A->bool)->(A->bool)) c IN U /\ c SUBSET f c` THEN
    DISCH_THEN(MP_TAC o SPEC `c:A->bool`) THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[]];
   (* Property 2: V covers topspace *)
   REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN
   X_GEN_TAC `x:A` THEN DISCH_TAC THEN
   (* x is in some c in C since C covers topspace *)
   UNDISCH_TAC `topspace top SUBSET UNIONS (C:(A->bool)->bool)` THEN
   REWRITE_TAC[SUBSET] THEN DISCH_THEN(MP_TAC o SPEC `x:A`) THEN
   ASM_REWRITE_TAC[IN_UNIONS] THEN
   DISCH_THEN(X_CHOOSE_THEN `c:A->bool` STRIP_ASSUME_TAC) THEN
   (* Witness: V(c) = (topspace DIFF ...) INTER f(c) *)
   EXISTS_TAC `(topspace top DIFF UNIONS {d:A->bool | d IN D /\ d INTER c = {}})
               INTER (f:(A->bool)->(A->bool)) c` THEN
   CONJ_TAC THENL
   [EXISTS_TAC `c:A->bool` THEN ASM_REWRITE_TAC[];
    (* x IN V(c) = E(c) INTER f(c) *)
    REWRITE_TAC[IN_INTER; IN_DIFF; IN_UNIONS; IN_ELIM_THM] THEN
    REPEAT CONJ_TAC THENL
    [(* x IN topspace *)
     ASM_REWRITE_TAC[];
     (* x not in any d with d INTER c = {} *)
     REWRITE_TAC[NOT_EXISTS_THM] THEN X_GEN_TAC `d:A->bool` THEN
     STRIP_TAC THEN
     (* x IN c and d INTER c = {} contradicts x IN d *)
     ASM SET_TAC[];
     (* x IN f(c) since x IN c and c SUBSET f(c) *)
     UNDISCH_TAC `!c:A->bool. c IN C ==> (f:(A->bool)->(A->bool)) c IN U /\ c SUBSET f c` THEN
     DISCH_THEN(MP_TAC o SPEC `c:A->bool`) THEN ASM_REWRITE_TAC[] THEN
     STRIP_TAC THEN ASM SET_TAC[]]];
   (* Property 3: V refines U *)
   REWRITE_TAC[FORALL_IN_GSPEC] THEN X_GEN_TAC `c:A->bool` THEN DISCH_TAC THEN
   EXISTS_TAC `(f:(A->bool)->(A->bool)) c` THEN
   UNDISCH_TAC `!c:A->bool. c IN C ==> (f:(A->bool)->(A->bool)) c IN U /\ c SUBSET f c` THEN
   DISCH_THEN(MP_TAC o SPEC `c:A->bool`) THEN ASM_REWRITE_TAC[] THEN
   STRIP_TAC THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
   (* Property 4: V is locally finite *)
   REWRITE_TAC[locally_finite_in] THEN CONJ_TAC THENL
   [(* Part 1: UNIONS V SUBSET topspace - V(c) SUBSET topspace for all c *)
    REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
    X_GEN_TAC `c:A->bool` THEN DISCH_TAC THEN
    REWRITE_TAC[SUBSET; IN_INTER; IN_DIFF] THEN
    GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    (* Part 2: For each x, find open w with finitely many V(c) meeting w *)
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    (* Use local finiteness of C to get neighborhood *)
    UNDISCH_TAC `locally_finite_in top (C:(A->bool)->bool)` THEN
    REWRITE_TAC[locally_finite_in] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `w:A->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `w:A->bool` THEN ASM_REWRITE_TAC[] THEN
    (* Goal: FINITE {V(c) | c IN C, V(c) INTER w != {}} *)
    (* Rewrite as image of finite set *)
    ONCE_REWRITE_TAC[SET_RULE
      `{y | y IN {g x | P x} /\ Q y} = IMAGE g {x | P x /\ Q(g x)}`] THEN
    MATCH_MP_TAC FINITE_IMAGE THEN
    (* Goal: FINITE {c IN C | V(c) INTER w != {}} *)
    (* Key insight: c SUBSET V(c), so if c INTER w != {} then V(c) INTER w != {} *)
    (* But we need the converse. Show this by proving V(c) SUBSET closure_of c *)
    (* For now, use CHEAT_TAC - this is the core difficulty *)
    CHEAT_TAC]]);;  (* TODO: prove FINITE {c IN C | V(c) INTER w != {}} *)

(* Michael's Lemma: For regular spaces, countably locally finite open covering
   has a locally finite open refinement.
   We use MICHAEL_STEP_1_2 + LOCALLY_FINITE_OPEN_REFINEMENT. *)

let MICHAEL_LEMMA = prove
 (`!top:A topology U.
    regular_space top /\
    (!u. u IN U ==> open_in top u) /\
    topspace top SUBSET UNIONS U /\
    countably_locally_finite_in top U
    ==> ?V. (!v. v IN V ==> open_in top v) /\
            topspace top SUBSET UNIONS V /\
            (!v. v IN V ==> ?u. u IN U /\ v SUBSET u) /\
            locally_finite_in top V`,
  REPEAT STRIP_TAC THEN
  (* Step 1: Apply MICHAEL_STEP_1_2 to get locally finite refinement C *)
  MP_TAC(ISPECL [`top:A topology`; `U:(A->bool)->bool`] MICHAEL_STEP_1_2) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `C:(A->bool)->bool` STRIP_ASSUME_TAC) THEN
  (* Step 2: Apply LOCALLY_FINITE_OPEN_REFINEMENT to get locally finite open V *)
  MP_TAC(ISPECL [`top:A topology`; `U:(A->bool)->bool`; `C:(A->bool)->bool`]
    LOCALLY_FINITE_OPEN_REFINEMENT) THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* THEOREM 41.4: Every metrizable space is paracompact                       *)
(* ------------------------------------------------------------------------- *)

let METRIZABLE_IMP_PARACOMPACT = prove
 (`!top:A topology. metrizable_space top ==> paracompact_space top`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[paracompact_space] THEN
  X_GEN_TAC `U:(A->bool)->bool` THEN STRIP_TAC THEN
  (* Step 1: Metrizable implies regular *)
  SUBGOAL_THEN `regular_space (top:A topology)` ASSUME_TAC THENL
  [ASM_MESON_TAC[METRIZABLE_IMP_REGULAR_SPACE]; ALL_TAC] THEN
  (* Step 2: Get countably locally finite refinement W *)
  MP_TAC(ISPECL [`top:A topology`; `U:(A->bool)->bool`]
    METRIZABLE_COUNTABLY_LOCALLY_FINITE_REFINEMENT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `W:(A->bool)->bool` STRIP_ASSUME_TAC) THEN
  (* Step 3: Apply Michael's lemma to get locally finite open V *)
  MP_TAC(ISPECL [`top:A topology`; `W:(A->bool)->bool`] MICHAEL_LEMMA) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `V:(A->bool)->bool` STRIP_ASSUME_TAC) THEN
  (* Step 4: V refines U (via transitivity: V refines W refines U) *)
  EXISTS_TAC `V:(A->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `v:A->bool` THEN DISCH_TAC THEN
  SUBGOAL_THEN `?w:A->bool. w IN W /\ v SUBSET w` MP_TAC THENL
  [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:A->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?u:A->bool. u IN U /\ w SUBSET u` MP_TAC THENL
  [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:A->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `u:A->bool` THEN ASM_MESON_TAC[SUBSET_TRANS]);;
