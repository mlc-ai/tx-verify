module

public import Core.Assembly.Execution

/-!
# Litmus tests of the dependency order (DEP-ORDER, DEP-CANONICAL-SPIN, ERR-POLL-SHAPE)

The litmus list of the dependency design, in three groups.

Waiting cycles (L1–L8, L5x, L5c, L7b). In each program some threads get stuck: each of them waits
for an event that another stuck thread performs only after its own stuck point. The rejection of
such a program is that its stuck prefix is `Maximal` and not `Complete`. Proving `Maximal` for a
concrete prefix needs the thread-run lemmas of `Lemmas/`, which a test of Core cannot import, so
each test proves the key fact instead: every execution `Y` that contains the events the stuck
threads would perform past their stuck points (stated as hypotheses) has a dependency cycle, so
`¬ DependencyOk L K Y`. No consistent execution extends the stuck prefix past those points.

Scope restriction (L10–L13, L15, L21, L22). Each program reads a poll result outside a canonical
spin. Each test proves `PollShapeUnsafe K X` for an execution that contains the poll, so the
rejection happens in `Correct.safe` and the execution itself stays allowed.

Kept executions (K1–K11, K9b). Each test proves the fields of `Consistent` that the dependency
design changes (`DependencyOk`, `ObservationCausal`, `ObjectCoherent`, `AsyncObjectOrdered`) or the
dependency facts the litmus list names (a canonical spin, a witness, a dependency path, the absence
of a `Resumes` edge). K9 also shows that its release/acquire variant violates `ObjectCoherent`.
-/

namespace PTX.Tests.DependencyLitmus
open PTX

/-! ## Launches, locations and instructions -/

def L32 : Launch where
  grid := 1
  block := 32
  params _ := none

def L64 : Launch where
  grid := 1
  block := 64
  params _ := none

def L128 : Launch where
  grid := 1
  block := 128
  params _ := none

/-- Two CTAs of 32 threads in one cluster. -/
def LPair : Launch where
  grid := 2
  block := 32
  params _ := none
  clusterSize := 2

def A : Loc := ⟨.shared, 0, 0⟩
def B : Loc := ⟨.shared, 0, 8⟩
def C : Loc := ⟨.shared, 0, 16⟩
def M : Loc := ⟨.shared, 0, 24⟩

/-- `mbarrier.try_wait.parity.relaxed.cta.shared::cta.b64 p, [base + off], 0`. -/
def pollI (p base : Nat) (off : Int) : Instr := { op := .mbarWait p base off (.imm 0) false .cta }
/-- `mbarrier.arrive.relaxed.cta.shared::cta.b64 _, [base + off]`. -/
def arriveI (base : Nat) (off : Int) : Instr :=
  { op := .mbarArrive base off (.imm 0) (.imm 1) false false .cta }
def braI (t : Nat) (uni : Bool := false) : Instr := { op := .bra t uni }
/-- `@p bra t` (`neg` false) or `@!p bra t` (`neg` true). -/
def braIf (p : Nat) (neg : Bool) (t : Nat) (uni : Bool := false) : Instr :=
  { guard := some (p, neg), op := .bra t uni }
def exitI : Instr := { op := .exit }
/-- `vote.sync.all.pred d, a, 3`. -/
def voteI (d a : Nat) : Instr :=
  { op := .warp ⟨.vote .all false, some .pred, [some d], [.reg a], some (.imm 3)⟩ }
def allocI (group : CtaGroup) (base : Nat) : Instr := { op := .tcAlloc group base 0 (.imm 512) }
def deallocI (group : CtaGroup) (taddr : Nat) : Instr :=
  { op := .tcDealloc group (.reg taddr) (.imm 512) }

/-! ## Machinery: dependency steps and cycles -/

section Machinery
variable {L : Launch} {K : Kernel} {X : Execution}

/-- One step of the relation `DependencyOk.acyclic` excludes cycles of. -/
abbrev Step (L : Launch) (K : Kernel) (X : Execution) (o : OrderObject) :
    AsyncCopy.Ref × Bool → AsyncCopy.Ref × Bool → Prop :=
  fun a c => DepStep L K X a c ∨ ObjectOrder L X o a c

/-- A cycle of dependency steps and the order of one object of `OrderObject.Enabling` refutes
`DependencyOk`. -/
theorem not_ok_of_cycle (o : OrderObject) (ho : o.Enabling) {n : AsyncCopy.Ref × Bool}
    (h : Relation.TransGen (Step L K X o) n n) : ¬ DependencyOk L K X :=
  fun hd => hd.acyclic o ho n h

theorem step_stage (o : OrderObject) {e : EvId} {ev : Event} (h : X.get e = some ev) :
    Step L K X o (.thread e, false) (.thread e, true) :=
  .inl (.inl (.inl ⟨rfl, rfl, rfl, ev, h⟩))

theorem traceBefore_of {w f : EvId} {ev : Event} (hf : X.get f = some ev) (h1 : w.1 = f.1)
    (h2 : w.2 < f.2) : TraceBefore X w f :=
  ⟨h1, h2, (List.getElem?_eq_some_iff.mp hf).1⟩

/-- A blocking event resumes before every later event of its thread. -/
theorem step_resume (o : OrderObject) {w f : EvId} {pc : Nat} {k : Kind} {c : Bool}
    {ev : Event} (hw : X.get w = some ⟨pc, k⟩) (hk : k.resume = .blocking c)
    (hf : X.get f = some ev) (h1 : w.1 = f.1) (h2 : w.2 < f.2) :
    Step L K X o (.thread w, true) (.thread f, false) :=
  .inl (.inr (.inr (.inr ⟨rfl, rfl, w, f, rfl, rfl, traceBefore_of hf h1 h2,
    by simp [hw, hk]⟩)))

/-- The successful poll of a canonical spin resumes before every later event of its thread. -/
theorem step_spin (o : OrderObject) {w f : EvId} {pc ex q : Nat} {m : Loc} {acq : Bool}
    {sc : MbarScope} {ev : Event} (hw : X.get w = some ⟨pc, .wait m q true acq sc⟩)
    (hs : K.CanonicalSpin pc ex) (hf : X.get f = some ev) (h1 : w.1 = f.1) (h2 : w.2 < f.2) :
    Step L K X o (.thread w, true) (.thread f, false) :=
  .inl (.inr (.inr (.inr ⟨rfl, rfl, w, f, rfl, rfl, traceBefore_of hf h1 h2, by
    simp only [hw, Option.map_some, Kind.resume]
    exact ⟨pc, ex, m, q, acq, sc, hw, hs, traceBefore_of hf h1 h2⟩⟩)))

theorem step_witness (o : OrderObject) {x e : EvId} (h : Witness L X (.thread x) e) :
    Step L K X o (.thread x, false) (.thread e, true) :=
  .inl (.inr (.inr (.inl ⟨rfl, rfl, e, rfl, h⟩)))

theorem step_mbar {m : Loc} {a c : AsyncCopy.Ref} (h : MBarrier.Before (X.objects m) a c) :
    Step L K X (.mbar m) (a, true) (c, true) :=
  .inr ⟨rfl, rfl, h⟩

theorem witness_of {e x : EvId} {fills : AsyncCopy.Ref → Prop} {ev : Event}
    (hn : Need.node fills ∈ Needs L X e) (hx : X.get x = some ev) (hf : fills (.thread x)) :
    Witness L X (.thread x) e :=
  ⟨fills, hn, ⟨ev, hx⟩, hf⟩

/-- The need of a masked warp collective for lane `l` of its member mask. -/
theorem mask_need {Q V : Type} (c : Kind → Option (WarpPart Q V)) {e : EvId} {pc : Nat}
    {k : Kind} {p : WarpPart Q V} {l : Nat} (he : X.get e = some ⟨pc, k⟩)
    (hK : KindNeeds L X k e = maskNeeds L c X e) (hc : c k = some p) (hl : l < 32)
    (hb : p.mask.testBit l = true) :
    Need.node (fun x => ∃ j, x = .thread (warpLane L e.1 l, j) ∧
      MaskWait L c X (warpLane L e.1 l, j) e) ∈ Needs L X e := by
  simp only [Needs, he, hK, maskNeeds, Option.bind_some, hc]
  exact List.mem_map.mpr ⟨l, List.mem_filter.mpr ⟨List.mem_range.mpr hl, hb⟩, rfl⟩

/-- A lane's vote of the same instance is a witness of a vote with member mask 3. -/
theorem vote_witness {e x : EvId} {pc pc' : Nat} {mo : VoteMode} {a d a' d' : Bool} {l : Nat}
    (he : X.get e = some ⟨pc, .voteMode mo 3 a d⟩) (hx : X.get x = some ⟨pc', .voteMode mo 3 a' d'⟩)
    (hl : l < 2) (hxl : x.1 = warpLane L e.1 l) (hw : SameWarp L x.1 e.1)
    (hne : ((X.tr e.1).take e.2).countP (fun ev => (voteClass ev.kind).any (·.mask == 3)) = 0)
    (hnx : ((X.tr x.1).take x.2).countP (fun ev => (voteClass ev.kind).any (·.mask == 3)) = 0) :
    Witness L X (.thread x) e := by
  obtain ⟨g, j⟩ := x
  simp only at hxl
  subst hxl
  refine witness_of (mask_need voteClass he rfl rfl (l := l) (by omega) ?_) hx
    ⟨j, rfl, hw, 3, 0, mo, ⟨⟨⟨_, _, he, rfl, rfl⟩, hne⟩, _, _, he, rfl, rfl⟩,
      .inl ⟨⟨⟨_, _, hx, rfl, rfl⟩, hnx⟩, _, _, hx, rfl, rfl⟩⟩
  show (3 : Nat).testBit l = true
  rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> decide

/-- A counter update that a successful poll observed is a witness of the poll. -/
theorem poll_witness {e x : EvId} {pc q : Nat} {m : Loc} {acq : Bool} {sc : MbarScope}
    (he : X.get e = some ⟨pc, .wait m q true acq sc⟩)
    (hx : MbarObserved X (.thread x) (.thread e)) :
    Witness L X (.thread x) e := by
  have hx' := hx
  obtain ⟨hp, j, m', a', ws, hj, ⟨⟨pc', par, hg⟩, i, k, r, w, ph, hi, hrid, -⟩, -⟩ := hx'
  cases hj
  rw [he] at hg
  cases hg
  refine ⟨(· = .thread x), ?_, hp, rfl⟩
  simp only [Needs, he, KindNeeds, ite_true, pollNeeds]
  refine List.mem_flatMap.mpr ⟨r, List.mem_of_getElem? hi, ?_⟩
  rw [needsIf, ite_eq_left_of_eq_true _ _ (eq_true (hrid ▸ hx))]
  simp [hrid]

/-- The need of a CTA barrier arrival for lane `l` of its warp. -/
theorem bar_need {e : EvId} {pc id : Nat} {cnt : Option Nat} {mode : BarMode} {l : Nat}
    (he : X.get e = some ⟨pc, .bar id cnt mode⟩) (hl : l < warpSize L e.1) :
    Need.node (fun x => ∃ i, ∃ r : CtaBarrier.Record EvId, ∃ y,
      (X.barriers (e.1 / L.block))[i]? = some r ∧ e ∈ r.refs ∧ x = .thread y ∧
      y.1 = warpLane L e.1 l ∧ (y ∈ r.refs ∨ ∃ (j g : Nat), j < i ∧
        (X.barriers (e.1 / L.block))[j]? = some (CtaBarrier.Record.exit g y))) ∈ Needs L X e := by
  simp only [Needs, he, KindNeeds, ctaBarNeeds]
  refine List.mem_append_left _ ?_
  simp only [ctaBarWarpNeeds, warpLanes]
  exact List.mem_map.mpr ⟨_, List.mem_map.mpr ⟨l, List.mem_range.mpr hl, rfl⟩, rfl⟩

/-- The need of a cluster barrier operation for lane `l` of its warp. -/
theorem cluster_need {e : EvId} {pc : Nat} {op : ClusterOp} {l : Nat}
    (he : X.get e = some ⟨pc, .cluster op⟩) (hl : l < warpSize L e.1) :
    Need.node (fun x => ∃ i, ∃ r : ClusterBarrier.Record EvId, ∃ y,
      (X.clusters (L.clusterOfCta (e.1 / L.block)))[i]? = some r ∧ e ∈ r.refs ∧
      x = .thread y ∧ y.1 = warpLane L e.1 l ∧
      (y ∈ r.refs ∨ ∃ (j g : Nat), j < i ∧ (X.clusters (L.clusterOfCta (e.1 / L.block)))[j]? =
        some (ClusterBarrier.Record.exit g y))) ∈ Needs L X e := by
  simp only [Needs, he, KindNeeds, clusterNeeds]
  refine List.mem_append_left _ ?_
  simp only [clusterWarpNeeds, warpLanes]
  exact List.mem_map.mpr ⟨_, List.mem_map.mpr ⟨l, List.mem_range.mpr hl, rfl⟩, rfl⟩

/-- A lane's matrix event of the same ordinal is a witness of a warp-level matrix event. -/
theorem matrix_witness {e x : EvId} {pc pc' : Nat} {op op' : MatrixOp}
    {own recv own' recv' : List (Option Byte)} {l : Nat}
    (he : X.get e = some ⟨pc, .matrix op own recv⟩)
    (hx : X.get x = some ⟨pc', .matrix op' own' recv'⟩)
    (hl : l < 32) (hxl : x.1 = warpLane L e.1 l)
    (hn : ((X.tr x.1).take x.2).countP isMatrix = ((X.tr e.1).take e.2).countP isMatrix) :
    Witness L X (.thread x) e := by
  obtain ⟨g, j⟩ := x
  simp only at hxl
  subst hxl
  have hm : Need.node (fun x => ∃ j, x = .thread (warpLane L e.1 l, j) ∧
      (X.MatrixK (warpLane L e.1 l, j) (((X.tr e.1).take e.2).countP isMatrix) ∨
        X.ExitedShort isMatrix (warpLane L e.1 l, j) (((X.tr e.1).take e.2).countP isMatrix)))
      ∈ Needs L X e := by
    simp only [Needs, he, KindNeeds]
    exact List.mem_map.mpr ⟨l, List.mem_range.mpr hl, rfl⟩
  exact witness_of hm hx ⟨j, rfl, .inl ⟨⟨_, hx, rfl⟩, hn⟩⟩

/-- A lane's same `setmaxnreg` request is a witness of a request. -/
theorem setMaxReg_witness {e x : EvId} {pc : Nat} {inc : Bool} {n i i' : Nat} {l : Nat}
    (he : X.get e = some ⟨pc, .setMaxReg inc n i⟩) (hx : X.get x = some ⟨pc, .setMaxReg inc n i'⟩)
    (hl : l < 32) (hxl : x.1 = warpLane L e.1 l) (hw : SameWarp L e.1 x.1)
    (hn : SetMaxNReg.ordinal X e = SetMaxNReg.ordinal X x) :
    Witness L X (.thread x) e := by
  obtain ⟨g, j⟩ := x
  simp only at hxl
  subst hxl
  have hm : Need.node (fun x => ∃ j, x = .thread (warpLane L e.1 l, j) ∧
      SetMaxNReg.SameRequest L X e (warpLane L e.1 l, j)) ∈ Needs L X e := by
    simp only [Needs, he, KindNeeds]
    exact List.mem_map.mpr ⟨l, List.mem_range.mpr hl, rfl⟩
  exact witness_of hm hx ⟨j, rfl, hw, hn, pc, inc, n, i, i', he, hx⟩

/-- The lanes of a release that last freed a column of an allocation's range are witnesses of
the allocation. -/
theorem reuse_witness {e x : EvId} {pc n : Nat} {group : CtaGroup} {dst : Option Loc} {j : Nat}
    {d : Tmem.Pair.Requests} {ev : Event} (l : Fin 32)
    (he : X.get e = some ⟨pc, .tc (.resource group dst (.alloc n))⟩)
    (hr : ReuseRelease L X e j) (hj : (X.tmemHistory (e.1 / L.block))[j]? = some d)
    (hev : d.own.event L l = x) (hx : X.get x = some ev) :
    Witness L X (.thread x) e := by
  classical
  have hmw : Tmem.Pair.MustWait X e := ⟨pc, group, dst, .alloc n, he, trivial⟩
  refine witness_of (fills := fun x => ∃ d, (X.tmemHistory (e.1 / L.block))[j]? = some d ∧
    x = .thread (d.own.event L l)) ?_ hx ⟨d, hj, by rw [hev]⟩
  simp only [Needs, he, KindNeeds, resourceNeeds, needsIf, hmw, ite_true]
  refine List.mem_append_left _ (List.mem_append_right _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ (List.mem_append_right _ ?_))))
  refine List.mem_flatMap.mpr ⟨j, List.mem_range.mpr (List.getElem?_eq_some_iff.mp hj).1, ?_⟩
  simp only [hr, ite_true]
  exact List.mem_map.mpr ⟨l, List.mem_finRange l, rfl⟩

end Machinery

theorem sameWarp_L128 {g h : Nat} (hg : g < 32) (hh : h < 32) : SameWarp L128 g h := by
  simp only [SameWarp, SameCta, Launch.threads, L128]; omega

theorem sameWarp_L32 {g h : Nat} (hg : g < 32) (hh : h < 32) : SameWarp L32 g h := by
  simp only [SameWarp, SameCta, Launch.threads, L32]; omega

theorem sameWarp_L64 {g h : Nat} (hg : g < 32) (hh : h < 32) : SameWarp L64 g h := by
  simp only [SameWarp, SameCta, Launch.threads, L64]; omega

/-- The prefix of a trace up to an index whose events are known. -/
theorem take_one {X : Execution} {g : Nat} {ev : Event} (h : X.get (g, 0) = some ev) :
    (X.tr g).take 1 = [ev] := by
  simp only [Execution.get] at h; simp [List.take_add_one, h]

/-! ## Waiting cycles -/

/-- L1: lane 0 runs `vote.sync.all.pred q, p, 3; redux.sync.add.u32 r, 1, 3`, lane 1 the two
instructions in the opposite order. Every execution in which both lanes get past their first
instruction has a dependency cycle: each lane's second instruction follows the return of its first
and is a witness of the other lane's first instruction. -/
theorem l1_cycle (K : Kernel) (Y : Execution) (pv pr : Nat) (a0 a1 d0 d1 : Bool)
    (r0 r1 : BitVec 32)
    (h00 : Y.get (0, 0) = some ⟨pv, .voteMode .all 3 a0 d0⟩)
    (h01 : Y.get (0, 1) = some ⟨pr, .redux .add false 3 1 r0⟩)
    (h10 : Y.get (1, 0) = some ⟨pr, .redux .add false 3 1 r1⟩)
    (h11 : Y.get (1, 1) = some ⟨pv, .voteMode .all 3 a1 d1⟩) : ¬ DependencyOk L32 K Y := by
  have t0 := take_one h00
  have t1 := take_one h10
  have w1 : Witness L32 Y (.thread (1, 1)) (0, 0) :=
    vote_witness h00 h11 (l := 1) (by decide) rfl (sameWarp_L32 (by decide) (by decide))
      (by simp) (by simp [t1, voteClass])
  have w0 : Witness L32 Y (.thread (0, 1)) (1, 0) := by
    refine witness_of (mask_need reduxClass h10 rfl rfl (l := 0) (by decide)
      (show (3 : Nat).testBit 0 = true by decide)) h01
      ⟨1, rfl, sameWarp_L32 (by decide) (by decide), 3, 0, (.add, false),
        ⟨⟨⟨_, _, h10, rfl, rfl⟩, by simp⟩, _, _, h10, rfl, rfl⟩,
        .inl ⟨⟨⟨_, _, h01, rfl, rfl⟩, by simp [show warpLane L32 1 0 = 0 from rfl, t0,
          reduxClass]⟩, _, _, h01, rfl, rfl⟩⟩
  refine not_ok_of_cycle (.mbar M) trivial (n := (.thread (0, 0), true)) ?_
  exact .tail (.tail (.tail (.single (step_resume _ h00 rfl h01 rfl (by decide)))
    (step_witness _ w0)) (step_resume _ h10 rfl h11 rfl (by decide))) (step_witness _ w1)

/-- L2: in a 64-thread CTA, warp 0 runs `bar.sync 1, 64; bar.sync 2, 64` and warp 1 runs
`bar.sync 2, 64; bar.sync 1, 64`. In every execution in which both warps get past their first
`bar.sync`, the release of each first `bar.sync` counts the other warp's second arrival (the
hypotheses `hc0` and `hc1`, which the barrier history forces: no thread exits before its second
arrival), and the second arrivals follow the returns of the first: a cycle. Thread 0 and thread 32
stand for their warps. -/
theorem l2_cycle (K : Kernel) (Y : Execution) (p0 p1 p2 p3 : Nat)
    (h00 : Y.get (0, 0) = some ⟨p0, .bar 1 (some 64) .sync⟩)
    (h01 : Y.get (0, 1) = some ⟨p1, .bar 2 (some 64) .sync⟩)
    (h10 : Y.get (32, 0) = some ⟨p2, .bar 2 (some 64) .sync⟩)
    (h11 : Y.get (32, 1) = some ⟨p3, .bar 1 (some 64) .sync⟩)
    (hc0 : CtaBarCounted L64 Y (0, 0) (32, 1)) (hc1 : CtaBarCounted L64 Y (32, 0) (0, 1)) :
    ¬ DependencyOk L64 K Y := by
  have mem : ∀ {e y : EvId}, CtaBarCounted L64 Y e y →
      y ∈ (Y.barriers (e.1 / L64.block)).flatMap CtaBarrier.Record.refs := by
    rintro e y ⟨-, -, -, -, i, r, hi, hy, -⟩
    exact List.mem_flatMap.mpr ⟨r, List.mem_of_getElem? hi, hy⟩
  have w0 : Witness L64 Y (.thread (32, 1)) (0, 0) :=
    witness_of (ctaBarCounted_witnessed L64 Y _ _ h00 (mem hc0) hc0) h11 rfl
  have w1 : Witness L64 Y (.thread (0, 1)) (32, 0) :=
    witness_of (ctaBarCounted_witnessed L64 Y _ _ h10 (mem hc1) hc1) h01 rfl
  refine not_ok_of_cycle (.mbar M) trivial (n := (.thread (0, 0), true)) ?_
  exact .tail (.tail (.tail (.single (step_resume _ h00 rfl h01 rfl (by decide)))
    (step_witness _ w1)) (step_resume _ h10 rfl h11 rfl (by decide))) (step_witness _ w0)

/-- L3 code: thread 0 runs positions 0–3 (spin on `A`, arrive on `B`), thread 1 runs positions
4–7 (spin on `B`, arrive on `A`); the selection of the region by thread index is left out.
Register 0 is the poll predicate and register 1 holds the address of `A` (`B` is 8 bytes
above). Both spins have shape B (`@!p bra L`). -/
def l3Code : Kernel where
  name := "l3"
  params := []
  code := [pollI 0 1 0, braIf 0 true 0, arriveI 1 8, exitI,
    pollI 0 1 8, braIf 0 true 4, arriveI 1 0, exitI]

theorem l3_spin0 : l3Code.CanonicalSpin 0 2 := ⟨rfl, 0, rfl, rfl⟩
theorem l3_spin4 : l3Code.CanonicalSpin 4 6 := ⟨rfl, 0, rfl, rfl⟩

/-- L3: thread 0 spins on `A` (parity 0) and then arrives on `B`; thread 1 spins on `B` and then
arrives on `A` (count 1 each, no other arrivals). In every execution in which both spins exit, the
arrival on `A` precedes thread 0's successful poll in `A`'s order (`hA`), and thread 0's arrival
on `B` is an update thread 1's successful poll observed (`hB`); both facts are forced, since each
phase completes only by the other thread's arrival. The order of `A` with the dependency order has
a cycle. -/
theorem l3_cycle (L : Launch) (Y : Execution) (a a' b b' : Nat) (ha : a < a') (hb : b < b')
    (h0p : Y.get (0, a) = some ⟨0, .wait A 0 true false .cta⟩)
    (h0a : Y.get (0, a') = some ⟨2, .arrive B 0 1 false .cta⟩)
    (h1p : Y.get (1, b) = some ⟨4, .wait B 0 true false .cta⟩)
    (h1a : Y.get (1, b') = some ⟨6, .arrive A 0 1 false .cta⟩)
    (hA : MBarrier.Before (Y.objects A) (.thread (1, b')) (.thread (0, a)))
    (hB : MbarObserved Y (.thread (0, a')) (.thread (1, b))) :
    ¬ DependencyOk L l3Code Y := by
  refine not_ok_of_cycle (.mbar A) trivial (n := (.thread (0, a), true)) ?_
  exact .tail (.tail (.tail (.tail (.single (step_spin _ h0p l3_spin0 h0a rfl ha))
    (step_witness _ (poll_witness h1p hB))) (step_spin _ h1p l3_spin4 h1a rfl hb))
    (step_stage _ h1a)) (step_mbar hA)

/-- L4 code: lane 0 runs positions 0–2 (`vote.sync.all.pred` with member mask 3, a relaxed arrive
on `M`, exit), lane 1 positions 3–6 (spin on `M`, the same vote, exit). Register 0 is the poll
predicate, register 1 the address of `M`. -/
def l4Code : Kernel where
  name := "l4"
  params := []
  code := [voteI 2 3, arriveI 1 0, exitI, pollI 0 1 0, braIf 0 true 3, voteI 2 3, exitI]

theorem l4_spin : l4Code.CanonicalSpin 3 5 := ⟨rfl, 0, rfl, rfl⟩

/-- L4: lane 0 runs `vote.sync` (mask 3) and then a relaxed arrive on `M`; lane 1 spins on `M`
and then runs the vote. In every execution in which lane 1's spin exits and both lanes vote, the
arrival precedes lane 1's successful poll in `M`'s order (forced: it is the only arrival), lane 1
has voted before only in the instance of lane 0's vote (`hn`), and the cycle closes through `M`'s
order. -/
theorem l4_cycle (Y : Execution) (a b : Nat) (hab : a < b) (a0 d0 a1 d1 : Bool)
    (h00 : Y.get (0, 0) = some ⟨0, .voteMode .all 3 a0 d0⟩)
    (h01 : Y.get (0, 1) = some ⟨1, .arrive M 0 1 false .cta⟩)
    (h1p : Y.get (1, a) = some ⟨3, .wait M 0 true false .cta⟩)
    (h1v : Y.get (1, b) = some ⟨5, .voteMode .all 3 a1 d1⟩)
    (hn : ((Y.tr 1).take b).countP (fun ev => (voteClass ev.kind).any (·.mask == 3)) = 0)
    (hM : MBarrier.Before (Y.objects M) (.thread (0, 1)) (.thread (1, a))) :
    ¬ DependencyOk L32 l4Code Y := by
  have w : Witness L32 Y (.thread (1, b)) (0, 0) :=
    vote_witness h00 h1v (l := 1) (by decide) rfl
      (sameWarp_L32 (show 1 < 32 by decide) (show 0 < 32 by decide)) (by simp) hn
  refine not_ok_of_cycle (.mbar M) trivial (n := (.thread (0, 0), true)) ?_
  exact .tail (.tail (.tail (.tail (.single (step_resume _ h00 rfl h01 rfl (by decide)))
    (step_stage _ h01)) (step_mbar hM)) (step_spin _ h1p l4_spin h1v rfl hab))
    (step_witness _ w)

/-- L5: in a 64-thread CTA, lane 0 runs `barrier.cta.arrive 1, 64` and then `vote.sync` (mask 3),
lane 1 the two in the opposite order. In every execution in which lane 0 gets past its arrival and
lane 1 past its vote, lane 1's arrival is in the record of lane 0's arrival (`hr`, forced: lane 1
does not exit before it), and the cycle closes. -/
theorem l5_cycle (K : Kernel) (Y : Execution) (pa pv : Nat) (a0 d0 a1 d1 : Bool) (i : Nat)
    (r : CtaBarrier.Record EvId)
    (h00 : Y.get (0, 0) = some ⟨pa, .bar 1 (some 64) .arrive⟩)
    (h01 : Y.get (0, 1) = some ⟨pv, .voteMode .all 3 a0 d0⟩)
    (h10 : Y.get (1, 0) = some ⟨pv, .voteMode .all 3 a1 d1⟩)
    (h11 : Y.get (1, 1) = some ⟨pa, .bar 1 (some 64) .arrive⟩)
    (hr : (Y.barriers 0)[i]? = some r) (hr0 : (0, 0) ∈ r.refs) (hr1 : (1, 1) ∈ r.refs) :
    ¬ DependencyOk L64 K Y := by
  have t0 := take_one h00
  have wb : Witness L64 Y (.thread (1, 1)) (0, 0) :=
    witness_of (bar_need h00 (l := 1) (by decide)) h11 ⟨i, r, (1, 1), hr, hr0, rfl, rfl, .inl hr1⟩
  have wv : Witness L64 Y (.thread (0, 1)) (1, 0) :=
    vote_witness h10 h01 (l := 0) (by decide) rfl (sameWarp_L64 (by decide) (by decide))
      (by simp) (by simp [t0, voteClass])
  refine not_ok_of_cycle (.mbar M) trivial (n := (.thread (0, 0), true)) ?_
  exact .tail (.tail (.tail (.single (step_resume _ h00 rfl h01 rfl (by decide)))
    (step_witness _ wv)) (step_resume _ h10 rfl h11 rfl (by decide))) (step_witness _ wb)

/-- L5x, the history that records lane 1's exit before lane 0's arrival record: in a 32-thread
CTA lane 0 runs `barrier.cta.arrive 1, 32; vote.sync 3; exit`, lane 1 `vote.sync 3; exit`. Lane
1's exit is then a witness of the return of lane 0's arrival (`ctaBarWarpNeeds`), and the exit
follows lane 1's vote, whose return waits for lane 0's vote. -/
theorem l5x_exit_first (K : Kernel) (Y : Execution) (pa pv px : Nat) (a0 d0 a1 d1 : Bool)
    (i j g : Nat) (r : CtaBarrier.Record EvId)
    (h00 : Y.get (0, 0) = some ⟨pa, .bar 1 (some 32) .arrive⟩)
    (h01 : Y.get (0, 1) = some ⟨pv, .voteMode .all 3 a0 d0⟩)
    (h10 : Y.get (1, 0) = some ⟨pv, .voteMode .all 3 a1 d1⟩)
    (h11 : Y.get (1, 1) = some ⟨px, .exit⟩)
    (hr : (Y.barriers 0)[i]? = some r) (hr0 : (0, 0) ∈ r.refs) (hji : j < i)
    (hx : (Y.barriers 0)[j]? = some (.exit g (1, 1))) :
    ¬ DependencyOk L32 K Y := by
  have t0 := take_one h00
  have wb : Witness L32 Y (.thread (1, 1)) (0, 0) :=
    witness_of (bar_need h00 (l := 1) (by decide)) h11
      ⟨i, r, (1, 1), hr, hr0, rfl, rfl, .inr ⟨j, g, hji, hx⟩⟩
  have wv : Witness L32 Y (.thread (0, 1)) (1, 0) :=
    vote_witness h10 h01 (l := 0) (by decide) rfl (sameWarp_L32 (by decide) (by decide))
      (by simp) (by simp [t0, voteClass])
  refine not_ok_of_cycle (.mbar M) trivial (n := (.thread (0, 0), true)) ?_
  exact .tail (.tail (.tail (.single (step_resume _ h00 rfl h01 rfl (by decide)))
    (step_witness _ wv)) (step_resume _ h10 rfl h11 rfl (by decide))) (step_witness _ wb)

/-- L5x for every history: when lane 0 gets past its arrival, its arrival has returned, so some
present event of lane 1 fills the need of lane 1 (`DependencyOk.ready`). Lane 1's vote is no
record of the barrier history (`hv`, a fact of every valid history), so the witness is a later
event of lane 1, which follows the return of lane 1's vote: a cycle in every history. -/
theorem l5x_cycle (K : Kernel) (Y : Execution) (pa pv : Nat) (a0 d0 a1 d1 : Bool)
    (h00 : Y.get (0, 0) = some ⟨pa, .bar 1 (some 32) .arrive⟩)
    (h01 : Y.get (0, 1) = some ⟨pv, .voteMode .all 3 a0 d0⟩)
    (h10 : Y.get (1, 0) = some ⟨pv, .voteMode .all 3 a1 d1⟩)
    (hv : ∀ r ∈ Y.barriers 0, (1, 0) ∉ r.refs) :
    ¬ DependencyOk L32 K Y := by
  intro hd
  have t0 := take_one h00
  have hret : Returned Y (0, 0) := by
    simp only [Returned, h00, Kind.resume]
    exact (List.getElem?_eq_some_iff.mp h01).1
  obtain ⟨x, hxp, i, r, y, hr, hr0, rfl, hy1, hy⟩ :=
    hd.ready _ hret _ (bar_need h00 (l := 1) (by decide))
  obtain ⟨g', k⟩ := y
  simp only [show warpLane L32 0 1 = 1 from rfl] at hy1
  subst hy1
  obtain ⟨ev, hev⟩ := hxp
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · exfalso
      rcases hy with hy | ⟨j, g, -, hj⟩
      · exact hv r (List.mem_of_getElem? hr) hy
      · exact hv _ (List.mem_of_getElem? hj) (by simp [CtaBarrier.Record.refs])
    · exact hk
  have wb : Witness L32 Y (.thread (1, k)) (0, 0) :=
    witness_of (bar_need h00 (l := 1) (by decide)) hev ⟨i, r, (1, k), hr, hr0, rfl, rfl, hy⟩
  have wv : Witness L32 Y (.thread (0, 1)) (1, 0) :=
    vote_witness h10 h01 (l := 0) (by decide) rfl (sameWarp_L32 (by decide) (by decide))
      (by simp) (by simp [t0, voteClass])
  refine not_ok_of_cycle (.mbar M) trivial (n := (.thread (0, 0), true)) ?_ hd
  exact .tail (.tail (.tail (.single (step_resume _ h00 rfl h01 rfl (by decide)))
    (step_witness _ wv)) (step_resume _ h10 rfl hev rfl hk)) (step_witness _ wb)

/-- L5c: the cluster analogue of L5 with a non-aligned `barrier.cluster.arrive`. Lane 1's arrival
is in the record of lane 0's arrival (`hr`, forced: lane 1 does not exit before it). -/
theorem l5c_cycle (K : Kernel) (Y : Execution) (pa pv : Nat) (rel : Bool) (a0 d0 a1 d1 : Bool)
    (i : Nat) (r : ClusterBarrier.Record EvId)
    (h00 : Y.get (0, 0) = some ⟨pa, .cluster (.arrive rel false)⟩)
    (h01 : Y.get (0, 1) = some ⟨pv, .voteMode .all 3 a0 d0⟩)
    (h10 : Y.get (1, 0) = some ⟨pv, .voteMode .all 3 a1 d1⟩)
    (h11 : Y.get (1, 1) = some ⟨pa, .cluster (.arrive rel false)⟩)
    (hr : (Y.clusters (L32.clusterOfCta 0))[i]? = some r) (hr0 : (0, 0) ∈ r.refs)
    (hr1 : (1, 1) ∈ r.refs) :
    ¬ DependencyOk L32 K Y := by
  have t0 := take_one h00
  have wb : Witness L32 Y (.thread (1, 1)) (0, 0) :=
    witness_of (cluster_need h00 (l := 1) (by decide)) h11
      ⟨i, r, (1, 1), hr, hr0, rfl, rfl, .inl hr1⟩
  have wv : Witness L32 Y (.thread (0, 1)) (1, 0) :=
    vote_witness h10 h01 (l := 0) (by decide) rfl (sameWarp_L32 (by decide) (by decide))
      (by simp) (by simp [t0, voteClass])
  refine not_ok_of_cycle (.mbar M) trivial (n := (.thread (0, 0), true)) ?_
  exact .tail (.tail (.tail (.single (step_resume _ h00 rfl h01 rfl (by decide)))
    (step_witness _ wv)) (step_resume _ h10 rfl h11 rfl (by decide))) (step_witness _ wb)

/-- L6: all 32 lanes of a warp reach one `ldmatrix` position and one `vote.sync` position (mask 3)
through a loop, lane 0 the matrix instruction first and lane 1 the vote first. In every execution
in which lane 0 gets past its matrix instruction and lane 1 past its vote, the cycle closes: the
matrix need of lane 1 is its first matrix event, which follows its vote. -/
theorem l6_cycle (K : Kernel) (Y : Execution) (pm pv : Nat) (op : MatrixOp)
    (own0 recv0 own1 recv1 : List (Option Byte)) (a0 d0 a1 d1 : Bool)
    (h00 : Y.get (0, 0) = some ⟨pm, .matrix op own0 recv0⟩)
    (h01 : Y.get (0, 1) = some ⟨pv, .voteMode .all 3 a0 d0⟩)
    (h10 : Y.get (1, 0) = some ⟨pv, .voteMode .all 3 a1 d1⟩)
    (h11 : Y.get (1, 1) = some ⟨pm, .matrix op own1 recv1⟩) : ¬ DependencyOk L32 K Y := by
  have t0 := take_one h00
  have t1 := take_one h10
  have wm : Witness L32 Y (.thread (1, 1)) (0, 0) :=
    matrix_witness h00 h11 (l := 1) (by decide) rfl (by simp [t1, isMatrix])
  have wv : Witness L32 Y (.thread (0, 1)) (1, 0) :=
    vote_witness h10 h01 (l := 0) (by decide) rfl (sameWarp_L32 (by decide) (by decide))
      (by simp) (by simp [t0, voteClass])
  refine not_ok_of_cycle (.mbar M) trivial (n := (.thread (0, 0), true)) ?_
  exact .tail (.tail (.tail (.single (step_resume _ h00 rfl h01 rfl (by decide)))
    (step_witness _ wv)) (step_resume _ h10 rfl h11 rfl (by decide))) (step_witness _ wm)

/-- L7 code: warp W0 runs positions 0–4 (allocate 512 columns, spin on `M`, deallocate, exit),
warp W1 positions 5–7 (allocate 512 columns, relaxed arrive on `M`, exit); the selection of the
region by warp is left out. Register 0 is the poll predicate, register 1 the address of `M`,
register 4 the address the allocation writes and register 5 the Tensor Memory address. -/
def l7Code : Kernel where
  name := "l7"
  params := []
  code := [allocI .one 4, pollI 0 1 0, braIf 0 true 1, deallocI .one 5, exitI,
    allocI .one 4, arriveI 1 0, exitI]

theorem l7_spin : l7Code.CanonicalSpin 1 3 := ⟨rfl, 0, rfl, rfl⟩

/-- L7 (Tensor Memory reuse, §4.6 of the design): in a 64-thread CTA, W0 allocates 512 columns,
spins on `M` and deallocates; W1 allocates 512 columns and then arrives on `M`. In every execution
in which W1's allocation returns and W0's spin exits, W0's deallocation is the release that last
freed a column of W1's range (`hreuse`, `hd`, `hev`: forced, since the 512 columns are held by
W0 until then), and W1's arrival is the update W0's successful poll observed (`hobs`, forced: it
is the only arrival). The cycle W1 allocation return, W1 arrival, W0 poll, W0 deallocation, W1
allocation return closes. Thread 0 and thread 32 (lane 0 of each warp) carry the cycle. -/
theorem l7_cycle (Y : Execution) (a dd j base : Nat) (dst : Option Loc) (had : a < dd)
    (dr : Tmem.Pair.Requests)
    (h0p : Y.get (0, a) = some ⟨1, .wait M 0 true false .cta⟩)
    (h0d : Y.get (0, dd) = some ⟨3, .tc (.resource .one none (.dealloc base 512))⟩)
    (h1a : Y.get (32, 0) = some ⟨5, .tc (.resource .one dst (.alloc 512))⟩)
    (h1r : Y.get (32, 1) = some ⟨6, .arrive M 0 1 false .cta⟩)
    (hreuse : ReuseRelease L64 Y (32, 0) j) (hd : (Y.tmemHistory 0)[j]? = some dr)
    (hev : dr.own.event L64 0 = (0, dd))
    (hobs : MbarObserved Y (.thread (32, 1)) (.thread (0, a))) :
    ¬ DependencyOk L64 l7Code Y := by
  have wr : Witness L64 Y (.thread (0, dd)) (32, 0) := reuse_witness 0 h1a hreuse hd hev h0d
  refine not_ok_of_cycle (.mbar M) trivial (n := (.thread (32, 0), true)) ?_
  exact .tail (.tail (.tail (.single (step_resume _ h1a rfl h1r rfl (by decide)))
    (step_witness _ (poll_witness h0p hobs))) (step_spin _ h0p l7_spin h0d rfl had))
    (step_witness _ wr)

/-- L7b code: the warp of CTA 0 runs positions 0–2 (`cta_group::2` allocation, relaxed arrive on
`M`, exit), the warp of CTA 1 positions 3–6 (spin on `M`, `cta_group::2` allocation, exit); the
selection of the region by CTA is left out. -/
def l7bCode : Kernel where
  name := "l7b"
  params := []
  code := [allocI .two 4, arriveI 1 0, exitI, pollI 0 1 0, braIf 0 true 3, allocI .two 4, exitI]

theorem l7b_spin : l7bCode.CanonicalSpin 3 5 := ⟨rfl, 0, rfl, rfl⟩

/-- L7b (`cta_group::2` allocation): CTA 0's warp allocates and then arrives on `M` (relaxed);
CTA 1's warp spins on `M` and then allocates. The peer need of an allocation is unconditional
(`Tmem.Pair.MustWait` holds for every allocation), so in every execution in which the allocation
of CTA 0 returns and CTA 1's spin exits, CTA 1's request is paired with CTA 0's (`hq`, `hp`,
`hev`), the arrival precedes CTA 1's successful poll in `M`'s order (`hM`, forced: it is the only
arrival), and the cycle closes through `M`'s order. -/
theorem l7b_cycle (Y : Execution) (a c : Nat) (hac : a < c) (dst0 dst1 : Option Loc)
    (q : Tmem.Pair.WarpRequest × Tmem.Pair.WarpRequest)
    (h00 : Y.get (0, 0) = some ⟨0, .tc (.resource .two dst0 (.alloc 512))⟩)
    (h01 : Y.get (0, 1) = some ⟨1, .arrive M 0 1 false .cta⟩)
    (h1p : Y.get (32, a) = some ⟨3, .wait M 0 true false .cta⟩)
    (h1c : Y.get (32, c) = some ⟨5, .tc (.resource .two dst1 (.alloc 512))⟩)
    (hq : q ∈ Y.tmemPairing) (hp : Tmem.Pair.Participates LPair q.1 (0, 0))
    (hev : q.2.event LPair 0 = (32, c))
    (hM : MBarrier.Before (Y.objects M) (.thread (0, 1)) (.thread (32, a))) :
    ¬ DependencyOk LPair l7bCode Y := by
  have wp : Witness LPair Y (.thread (32, c)) (0, 0) :=
    witness_of (covered_witnessed LPair Y _ h00 ⟨0, .two, dst0, .alloc 512, h00, trivial⟩ 0) h1c
      ⟨q, hq, .inl ⟨hp, by rw [hev]⟩⟩
  refine not_ok_of_cycle (.mbar M) trivial (n := (.thread (0, 0), true)) ?_
  exact .tail (.tail (.tail (.tail (.single (step_resume _ h00 rfl h01 rfl (by decide)))
    (step_stage _ h01)) (step_mbar hM)) (step_spin _ h1p l7b_spin h1c rfl hac))
    (step_witness _ wp)

/-- L8: in a warp of a 128-thread warpgroup, lane 0 runs `setmaxnreg.inc.sync.aligned.u32 240`
and then `vote.sync` (mask 3), lane 1 the two in the opposite order, both at the same positions
(reached through a loop). The `.sync` wait of `setmaxnreg` closes the cycle: lane 1's request is
the same request as lane 0's and follows lane 1's vote. -/
theorem l8_cycle (K : Kernel) (Y : Execution) (ps pv i0 i1 : Nat) (a0 d0 a1 d1 : Bool)
    (h00 : Y.get (0, 0) = some ⟨ps, .setMaxReg true 240 i0⟩)
    (h01 : Y.get (0, 1) = some ⟨pv, .voteMode .all 3 a0 d0⟩)
    (h10 : Y.get (1, 0) = some ⟨pv, .voteMode .all 3 a1 d1⟩)
    (h11 : Y.get (1, 1) = some ⟨ps, .setMaxReg true 240 i1⟩) : ¬ DependencyOk L128 K Y := by
  have t0 := take_one h00
  have t1 := take_one h10
  have ws : Witness L128 Y (.thread (1, 1)) (0, 0) :=
    setMaxReg_witness h00 h11 (l := 1) (by decide) rfl (sameWarp_L128 (by decide) (by decide))
      (by simp [SetMaxNReg.ordinal, SetMaxNReg.isRequest, t1])
  have wv : Witness L128 Y (.thread (0, 1)) (1, 0) :=
    vote_witness h10 h01 (l := 0) (by decide) rfl (sameWarp_L128 (by decide) (by decide))
      (by simp) (by simp [t0, voteClass])
  refine not_ok_of_cycle (.mbar M) trivial (n := (.thread (0, 0), true)) ?_
  exact .tail (.tail (.tail (.single (step_resume _ h00 rfl h01 rfl (by decide)))
    (step_witness _ wv)) (step_resume _ h10 rfl h11 rfl (by decide))) (step_witness _ ws)

/-! ## Scope restriction -/

/-- A poll at a position whose predicate some instruction reads other than as the branch of a
canonical spin is neither a canonical spin nor unused, so every execution containing it is
unsafe. -/
theorem pollShapeUnsafe_of {K : Kernel} {X : Execution} {e : EvId} {pc q p : Nat} {m : Loc}
    {ok acq : Bool} {sc : MbarScope} (he : X.get e = some ⟨pc, .wait m q ok acq sc⟩)
    (hreg : K.pollReg pc = some p) (hdst : K.pollDst pc = none ∨ K.pollDst pc = some p)
    (hsp : K.spinPred p = false) : PollShapeUnsafe K X := by
  refine ⟨e, pc, m, q, ok, acq, sc, he, ?_, ?_⟩
  · rintro ⟨ex, -, p', hp', hs⟩
    rcases hdst with h | h <;> rw [h] at hp' <;> cases hp'
    exact absurd hs (by simp [Kernel.SpinPred, hsp])
  · rintro ⟨⟨p', hp', hs⟩, -⟩
    rw [hreg] at hp'
    cases hp'
    exact absurd hs (by simp [Kernel.SpinPred, hsp])

/-- An execution whose thread 0 performs one poll of `A` at position `pc`. -/
def onePoll (pc : Nat) (ok : Bool) : Execution where
  tr
    | 0 => [⟨pc, .wait A 0 ok false .cta⟩]
    | _ => []
  rf _ _ := none

/-- L10 code (thread 0; thread 1 runs the same code with the objects exchanged): a loop that polls
`A0` (address in register 1) and `A1` (8 bytes above) and, when either poll succeeds, arrives on
`B0` and `B1`. -/
def l10Code : Kernel where
  name := "l10"
  params := []
  code := [pollI 0 1 0, braIf 0 false 5, pollI 0 1 8, braIf 0 false 5, braI 0,
    arriveI 1 16, arriveI 1 24, exitI]

/-- L10: the polls of several objects in one loop are no canonical spin; an execution with the
first poll is unsafe. -/
theorem l10_unsafe : PollShapeUnsafe l10Code (onePoll 0 false) :=
  pollShapeUnsafe_of (e := (0, 0)) rfl rfl (.inr rfl) rfl

/-- L11 code: one poll whose result a branch reads, both arms executing the same arrive. -/
def l11Code : Kernel where
  name := "l11"
  params := []
  code := [pollI 0 1 0, braIf 0 false 4, arriveI 1 8, braI 5, arriveI 1 8, exitI]

/-- L11: unsafe. -/
theorem l11_unsafe : PollShapeUnsafe l11Code (onePoll 0 true) :=
  pollShapeUnsafe_of (e := (0, 0)) rfl rfl (.inr rfl) rfl

/-- L12 code: nested retry loops, `L0: poll p; @p bra D; L1: poll p; @!p bra L1; bra L0; D:
arrive`. -/
def l12Code : Kernel where
  name := "l12"
  params := []
  code := [pollI 0 1 0, braIf 0 false 5, pollI 0 1 0, braIf 0 true 2, braI 0, arriveI 1 8, exitI]

/-- The inner loop has the shape of a spin. -/
theorem l12_shape : l12Code.SpinShape 2 4 := rfl

/-- L12: the inner poll is still no canonical spin, because the outer branch reads its predicate;
an execution with it is unsafe. -/
theorem l12_unsafe : PollShapeUnsafe l12Code (onePoll 2 true) :=
  pollShapeUnsafe_of (e := (0, 0)) rfl rfl (.inr rfl) rfl

/-- L13 code: `selp r2, r3, r4, p; mbarrier.arrive [r2]` after the poll. -/
def l13Code : Kernel where
  name := "l13"
  params := []
  code := [pollI 0 1 0,
    { op := .int ⟨.selp, .int .u 32, false, [some 2], [.reg 3, .reg 4, .reg 0]⟩ },
    arriveI 2 0, exitI]

/-- L13: unsafe. -/
theorem l13_unsafe : PollShapeUnsafe l13Code (onePoll 0 true) :=
  pollShapeUnsafe_of (e := (0, 0)) rfl rfl (.inr rfl) rfl

/-- L15 code, the `saved` example of the codex design review round 6:
`outer: i = 0; saved = false; inner: first = (i == 0); addr = first ? A : C; P: poll(addr) -> p;
@first mov saved, p; i++; if i < 2 goto inner; if !saved goto outer; arrive B`. Registers: 0 the
poll predicate `p`, 2 the address, 3 and 4 the addresses of `A` and `C`, 5 the address of `B`, 6
the counter `i`, 7 `saved`, 8 `first`, 9 the loop condition. -/
def l15Code : Kernel where
  name := "l15"
  params := []
  code := [{ op := .move ⟨.scalar, .int .u 32, [some 6], [.imm 0]⟩ },
    { op := .move ⟨.scalar, .pred, [some 7], [.imm 0]⟩ },
    { op := .int ⟨.setp .eq none, .int .u 32, false, [some 8], [.reg 6, .imm 0]⟩ },
    { op := .int ⟨.selp, .int .u 32, false, [some 2], [.reg 3, .reg 4, .reg 8]⟩ },
    pollI 0 2 0,
    { guard := some (8, false), op := .move ⟨.scalar, .pred, [some 7], [.reg 0]⟩ },
    { op := .int ⟨.add, .int .u 32, false, [some 6], [.reg 6, .imm 1]⟩ },
    { op := .int ⟨.setp .lt none, .int .u 32, false, [some 9], [.reg 6, .imm 2]⟩ },
    braIf 9 false 2, braIf 7 true 0, arriveI 5 0, exitI]

/-- L15: unsafe. -/
theorem l15_unsafe : PollShapeUnsafe l15Code (onePoll 4 true) :=
  pollShapeUnsafe_of (e := (0, 0)) rfl rfl (.inr rfl) rfl

/-- L21 code, the guarded `test_wait` chain of the codex design review round 7:
`loop: q = true; test_wait A -> p; @p test_wait C -> q; @q bra loop; arrive B`. Registers: 0 is
`p`, 1 is `q`, 2, 3 and 4 hold the addresses of `A`, `C` and `B`. -/
def l21Code : Kernel where
  name := "l21"
  params := []
  code := [{ op := .move ⟨.scalar, .pred, [some 1], [.imm 1]⟩ }, pollI 0 2 0,
    { guard := some (0, false), op := .mbarWait 1 3 0 (.imm 0) false .cta }, braIf 1 false 0,
    arriveI 4 0, exitI]

/-- L21: the first poll is unsafe. -/
theorem l21_unsafe : PollShapeUnsafe l21Code (onePoll 1 true) :=
  pollShapeUnsafe_of (e := (0, 0)) rfl rfl (.inr rfl) rfl

/-- L21: the guarded poll is unsafe too. -/
theorem l21_guarded_unsafe : PollShapeUnsafe l21Code (onePoll 2 false) :=
  pollShapeUnsafe_of (e := (0, 0)) rfl rfl (.inl rfl) rfl

/-- L22 code, the loop of Examples 1a, 2 and 5 of §9.7.15.16.19 with a `nanosleep.u32` between
the poll and the branch: `waitLoop: test_wait A -> p; @!p nanosleep.u32 20; @!p bra waitLoop;
exit`. Register 0 is `p`, register 1 holds the address of `A`. -/
def l22Code : Kernel where
  name := "l22"
  params := []
  code := [pollI 0 1 0, { guard := some (0, true), op := .misc (.nanosleep (.imm 20)) },
    braIf 0 true 0, exitI]

/-- L22: the branch is not right after the poll, so the loop is no canonical spin, and the
guarded `nanosleep` reads the predicate; an execution with the poll is unsafe (ERR-POLL-SHAPE). -/
theorem l22_unsafe : PollShapeUnsafe l22Code (onePoll 0 false) :=
  pollShapeUnsafe_of (e := (0, 0)) rfl rfl (.inr rfl) rfl

/-! ## Machinery for the kept executions -/

/-- A relation that a rank function increases has no cycle. -/
theorem acyclic_of_rank {α : Type} {R : α → α → Prop} (f : α → Nat)
    (h : ∀ a b, R a b → f a < f b) (n : α) : ¬ Relation.TransGen R n n := by
  have key : ∀ a b, Relation.TransGen R a b → f a < f b := by
    intro a b hab
    induction hab with
    | single h' => exact h _ _ h'
    | tail _ h' ih => exact ih.trans (h _ _ h')
  exact fun hc => lt_irrefl _ (key _ _ hc)

/-- The rank of a node from a rank of thread events: issue `2 * rk e`, completion one more. -/
def prank (rk : EvId → Nat) : AsyncCopy.Ref × Bool → Nat
  | (.thread e, b) => 2 * rk e + b.toNat
  | (.async _ _, _) => 0

section Kept
variable {L : Launch} {K : Kernel} {X : Execution}

theorem not_stageEdge (hna : ∀ i p, ¬ X.AsyncPresent i p) (a c : AsyncCopy.Ref) :
    ¬ StageEdge X a c := by
  intro h
  unfold StageEdge at h
  split at h <;> simp_all

/-- Without asynchronous effects, a stage step is the issue and completion of one thread event. -/
theorem stageOrder_thread (hna : ∀ i p, ¬ X.AsyncPresent i p) {a c : AsyncCopy.Ref}
    {b b' : Bool} (h : StageOrder X (a, b) (c, b')) :
    ∃ e ev, a = .thread e ∧ c = .thread e ∧ b = false ∧ b' = true ∧ X.get e = some ev := by
  rcases h with ⟨rfl, rfl, rfl, hp⟩ | ⟨-, -, h⟩
  · cases a with
    | thread e => obtain ⟨ev, hev⟩ := hp; exact ⟨e, ev, rfl, rfl, rfl, rfl, hev⟩
    | async i p => exact absurd hp (hna i p)
  · exact absurd h (not_stageEdge hna _ _)

/-- The dependency order with the order of any object has no cycle when a rank of thread events
grows along each thread, every witness has at most the rank of the event it fills, and the order
of every object grows the node rank. -/
theorem acyclic_pos (hna : ∀ i p, ¬ X.AsyncPresent i p) (rk : EvId → Nat)
    (hrk : ∀ e f : EvId, e.1 = f.1 → e.2 < f.2 → rk e < rk f)
    (hw : ∀ x e, Witness L X (.thread x) e → rk x ≤ rk e)
    (hobj : ∀ o, o.Enabling → ∀ a c, ObjectOrder L X o a c → prank rk a < prank rk c) :
    ∀ o, o.Enabling → ∀ n, ¬ Relation.TransGen (Step L K X o) n n := by
  intro o ho
  refine acyclic_of_rank (prank rk) fun ⟨a, b⟩ ⟨c, b'⟩ h => ?_
  rcases h with h | h
  · rcases h with h | ⟨-, -, i, p, -, rfl, -, hp, -⟩ | ⟨rfl, rfl, j, rfl, hx⟩ |
        ⟨rfl, rfl, w, j, rfl, rfl, ⟨h1, h2, -⟩, -⟩
    · obtain ⟨e, -, rfl, rfl, rfl, rfl, -⟩ := stageOrder_thread hna h
      simp [prank]
    · exact absurd hp (hna i p)
    · cases a with
      | thread x => have := hw x j hx; simp only [prank]; simp; omega
      | async i p => obtain ⟨-, -, hpr, -⟩ := hx; exact absurd hpr (hna i p)
    · have := hrk w j h1 h2
      simp only [prank]; simp; omega
  · exact hobj o ho _ _ h

/-- Record positions in a history with distinct identities follow its order. -/
theorem before_idxOf {log : List (MBarrier.Record AsyncCopy.Ref)}
    (hnd : (log.map MBarrier.Record.id).Nodup) {a c : AsyncCopy.Ref} (h : MBarrier.Before log a c) :
    (log.map MBarrier.Record.id).idxOf a < (log.map MBarrier.Record.id).idxOf c := by
  obtain ⟨i, j, r, s, hr, rfl, hs, rfl, hij⟩ := h
  have hi : (log.map MBarrier.Record.id)[i]? = some r.id := by simp [hr]
  have hj : (log.map MBarrier.Record.id)[j]? = some s.id := by simp [hs]
  obtain ⟨hil, hie⟩ := List.getElem?_eq_some_iff.mp hi
  obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp hj
  rw [← hie, ← hje, List.Nodup.idxOf_getElem hnd, List.Nodup.idxOf_getElem hnd]
  exact hij

/-- Without asynchronous effects, barrier histories and `Resumes` edges, and with histories of
distinct identities, every dependency step goes from an issue to a completion and every object
step forward in the object's history, so there is no cycle. -/
theorem acyclic_flat (hna : ∀ i p, ¬ X.AsyncPresent i p) (hres : ∀ w f, ¬ Resumes K X w f)
    (hnd : ∀ m, ((X.objects m).map MBarrier.Record.id).Nodup)
    (hbar : ∀ c, X.barriers c = []) (hcl : ∀ c, X.clusters c = []) :
    ∀ o, o.Enabling → ∀ n, ¬ Relation.TransGen (Step L K X o) n n := by
  intro o ho
  let r : AsyncCopy.Ref × Bool → Nat := fun n => match o with
    | .mbar m => if n.2 then 1 + ((X.objects m).map MBarrier.Record.id).idxOf n.1 else 0
    | _ => n.2.toNat
  refine acyclic_of_rank r fun ⟨a, b⟩ ⟨c, b'⟩ h => ?_
  rcases h with h | h
  · rcases h with h | ⟨-, -, i, p, -, rfl, -, hp, -⟩ | ⟨rfl, rfl, -⟩ |
        ⟨-, -, w, j, -, -, hr⟩
    · obtain ⟨e, -, rfl, rfl, rfl, rfl, -⟩ := stageOrder_thread hna h
      cases o <;> simp [r]
    · exact absurd hp (hna i p)
    · cases o <;> simp [r]
    · exact absurd hr (hres w j)
  · cases o with
    | mbar m =>
      obtain ⟨rfl, rfl, hb⟩ := h
      have := before_idxOf (hnd m) hb
      simp only [r, ite_true]
      omega
    | ctaBar c id =>
      obtain ⟨-, -, -, -, -, -, -, -, k, -, x, -, hx, -⟩ := h
      simp [hbar] at hx
    | cluster c =>
      obtain ⟨-, -, -, -, -, -, k, -, x, -, hx, -⟩ := h
      simp [hcl] at hx
    | tmem cta => exact ho.elim

/-- Every need of a successful poll is a present update. -/
theorem ready_poll {e : EvId} {pc q : Nat} {m : Loc} {acq : Bool} {sc : MbarScope}
    (he : X.get e = some ⟨pc, .wait m q true acq sc⟩) : Ready L X e := by
  classical
  intro n hn
  simp only [Needs, he, KindNeeds, ite_true, pollNeeds, List.mem_flatMap] at hn
  obtain ⟨r, -, hn⟩ := hn
  rw [needsIf] at hn
  split_ifs at hn with ho
  · simp only [List.mem_singleton] at hn
    subst hn
    exact ⟨r.id, ho.1, rfl⟩
  · simp at hn

/-- Only events of a kind that is not free can be returned. -/
theorem ready_of (h : ∀ e pc k, X.get e = some ⟨pc, k⟩ → k.resume ≠ .free → Ready L X e) :
    ∀ e, Returned X e → Ready L X e := by
  intro e hr
  cases he : X.get e with
  | none => simp [Returned, he] at hr
  | some ev =>
    obtain ⟨pc, k⟩ := ev
    refine h e pc k he fun hk => ?_
    simp only [Returned, he] at hr
    cases k <;> simp_all [Kind.resume]

/-- No event resumes another when every event is free or a poll at a position that is no spin. -/
theorem no_resumes (h : ∀ w pc k, X.get w = some ⟨pc, k⟩ →
    k.resume = .free ∨ ∃ m q ok acq sc, k = .wait m q ok acq sc ∧ K.spinExit? pc = none)
    (w f : EvId) : ¬ Resumes K X w f := by
  rintro ⟨-, hr⟩
  cases hw : X.get w with
  | none => simp [hw] at hr
  | some ev =>
    obtain ⟨pc, k⟩ := ev
    rcases h w pc k hw with hk | ⟨m, q, ok, acq, sc, rfl, hs⟩
    · simp [hw, hk] at hr
    · simp only [hw, Option.map_some, Kind.resume] at hr
      obtain ⟨pc', ex, _, _, _, _, hw', ⟨hsh, -⟩, -⟩ := hr
      rw [hw] at hw'
      cases hw'
      simp [Kernel.SpinShape, hs] at hsh

/-- A poll whose predicate no instruction reads, at a position that is no spin, is unused. -/
theorem pollUnused_of {pc p : Nat} (hreg : K.pollReg pc = some p) (hsp : K.spinPred p = true)
    (hs : K.spinExit? pc = none) : K.PollUnused pc :=
  ⟨⟨p, hreg, hsp⟩, fun ⟨_, hsh, _⟩ => by simp [Kernel.SpinShape, hs] at hsh⟩

theorem not_pollShapeUnsafe (h : ∀ e pc m q ok acq sc, X.get e = some ⟨pc, .wait m q ok acq sc⟩ →
    (∃ ex, K.CanonicalSpin pc ex) ∨ K.PollUnused pc) : ¬ PollShapeUnsafe K X := by
  rintro ⟨e, pc, m, q, ok, acq, sc, he, h1, h2⟩
  rcases h e pc m q ok acq sc he with h3 | h3
  · exact h1 h3
  · exact h2 h3

/-- Only an event with needs has witnesses, and a free event has none. -/
theorem witness_kind {x : AsyncCopy.Ref} {e : EvId} (h : Witness L X x e) :
    ∃ pc k, X.get e = some ⟨pc, k⟩ ∧ k.resume ≠ .free := by
  obtain ⟨fills, hn, -⟩ := h
  cases he : X.get e with
  | none => simp [Needs, he] at hn
  | some ev =>
    obtain ⟨pc, k⟩ := ev
    refine ⟨pc, k, rfl, fun hk => ?_⟩
    simp [Needs, he, kindNeeds_free L X k e hk] at hn

/-- A witness of a masked warp collective is a waiting dependency of it. -/
theorem witness_mask {Q V : Type} (c : Kind → Option (WarpPart Q V)) {x e : EvId} {pc : Nat}
    {k : Kind} (he : X.get e = some ⟨pc, k⟩) (hK : KindNeeds L X k e = maskNeeds L c X e)
    (h : Witness L X (.thread x) e) : MaskWait L c X x e := by
  obtain ⟨fills, hn, -, hf⟩ := h
  simp only [Needs, he, hK, maskNeeds] at hn
  split at hn
  · obtain ⟨l, -, heq⟩ := List.mem_map.mp hn
    cases heq
    obtain ⟨j, hj, hw⟩ := hf
    cases hj
    exact hw
  · simp at hn

/-- A masked warp collective is ready when every lane of its mask has a present waiting
dependency. -/
theorem ready_mask {Q V : Type} (c : Kind → Option (WarpPart Q V)) {e : EvId} {pc : Nat}
    {k : Kind} {p : WarpPart Q V} (he : X.get e = some ⟨pc, k⟩)
    (hK : KindNeeds L X k e = maskNeeds L c X e) (hc : c k = some p)
    (h : ∀ l < 32, p.mask.testBit l = true → ∃ j ev, X.get (warpLane L e.1 l, j) = some ev ∧
      MaskWait L c X (warpLane L e.1 l, j) e) : Ready L X e := by
  intro n hn
  simp only [Needs, he, hK, maskNeeds, Option.bind_some, hc] at hn
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hn
  obtain ⟨hl, hb⟩ := List.mem_filter.mp hl
  obtain ⟨j, ev, hj, hw⟩ := h l (List.mem_range.mp hl) hb
  exact ⟨.thread (warpLane L e.1 l, j), ⟨ev, hj⟩, j, rfl, hw⟩

/-- The lanes of member mask 3. -/
theorem mask3 : ∀ l < 32, (3 : Nat).testBit l = true → l = 0 ∨ l = 1 := by decide

/-- An execution whose asynchronous records are empty has no asynchronous stage. -/
theorem noAsync_of (h1 : X.async = {}) (h2 : X.tensor = fun _ => none)
    (h3 : X.tensorStores = fun _ => none) (h4 : X.clc = fun _ => {})
    (h5 : X.tcNotified = fun _ => ∅) : ∀ i p, ¬ X.AsyncPresent i p := by
  intro i p h
  unfold Execution.AsyncPresent at h
  split at h <;> simp_all [Execution.MmaRead]

/-- An execution with no asynchronous effect, barrier history, warp barrier, thread fence,
release arrival, acquire poll or Tensor Memory history, and only thread operations in its
mbarrier histories. -/
structure Plain (X : Execution) : Prop where
  async : ∀ i p, ¬ X.AsyncPresent i p
  noAcq : ∀ e pc m q ok acq sc, X.get e = some ⟨pc, .wait m q ok acq sc⟩ → acq = false
  noRel : ∀ e m tx c s, ¬ X.Arrive e m tx c true s
  noWarpBar : ∀ e m i, ¬ X.WarpBar e m i
  noFence : ∀ e sem s, ¬ X.ThreadFence e sem s
  barriers : ∀ c, X.barriers c = []
  clusters : ∀ c, X.clusters c = []
  tmem : ∀ c, X.tmemHistory c = []
  ids : ∀ m r, r ∈ X.objects m → ∃ e, r.id = .thread e

/-- In a plain execution, base causality is program order and release/acquire synchronization,
so a rank that both increase increases along it. -/
theorem Plain.baseCausality_rank (hp : Plain X) (rk : EvId → Nat)
    (hpo : ∀ e f, po X e f → rk e < rk f) (hms : ∀ e f, synchronizesWith L X e f → rk e < rk f)
    {e f : EvId} (h : baseCausality L X e f) : rk e < rk f := by
  have base : ∀ {e f : EvId}, (po X e f ∨ CtaBarSync L X e f ∨ MSync L X e f ∨
      ClusterSync L X e f ∨ WarpBarSync L X e f ∨ synchronizesWith L X e f ∨ FenceSync L X e f) →
      rk e < rk f := by
    intro e f h
    rcases h with h | ⟨-, _, _, _, ⟨-, -, _, _, _, _, _, _, hi, -⟩, -⟩ |
        ⟨_, _, _, _, _, ⟨_, _, hr⟩, -⟩ | ⟨-, _, _, ⟨_, ⟨_, _, _, _, _, _, _, hi, -⟩, -⟩, -⟩ |
        ⟨_, _, ⟨-, _, _, hw, -⟩, -⟩ | h | h
    · exact hpo _ _ h
    · simp [hp.barriers] at hi
    · exact absurd hr (hp.noRel _ _ _ _ _)
    · simp [hp.clusters] at hi
    · exact absurd hw (hp.noWarpBar _ _ _)
    · exact hms _ _ h
    · exact absurd h (not_fenceSync_of_noFence hp.noFence _ _)
  induction h with
  | single h => exact base h
  | tail _ h ih => exact ih.trans (base h)

theorem Plain.cause_rank (hp : Plain X) (rk : EvId → Nat) (hpo : ∀ e f, po X e f → rk e < rk f)
    (hms : ∀ e f, synchronizesWith L X e f → rk e < rk f) {a c : AsyncCopy.Ref × Bool}
    (h : stageCausality L X a c) : prank rk a < prank rk c := by
  obtain ⟨e, b⟩ := a
  obtain ⟨f, b'⟩ := c
  rcases h with h | ⟨rfl, rfl, i, j, rfl, rfl, h⟩ |
      ⟨-, -, j, -, hcr⟩
  · obtain ⟨e, -, rfl, rfl, rfl, rfl, -⟩ := stageOrder_thread hp.async h
    simp [prank]
  · have := hp.baseCausality_rank rk hpo hms h
    simp only [prank]; simp; omega
  · obtain ⟨i, p, w, ws, -, -, ⟨n, m, -, ⟨pc, par, hg⟩, -⟩, -⟩ := hcr
    exact absurd (hp.noAcq _ _ _ _ _ _ _ hg) (by simp)

/-- A plain execution has no synchronizing observation. -/
theorem Plain.observationCausal (hp : Plain X) : ObservationCausal L X := by
  rintro x w (⟨-, j, m, pc, q, ws, us, g, rfl, hg, -⟩ | ⟨i, p, j, k, rfl, -, hpr, -⟩) -
  · exact absurd (hp.noAcq _ _ _ _ _ _ _ hg) (by simp)
  · exact hp.async _ _ hpr

/-- In a plain execution, per-object coherence follows from a rank that program order,
release/acquire synchronization and the pairs of each mbarrier history with its initialization or
of one thread increase. -/
theorem Plain.objectCoherent (hp : Plain X) (rk : EvId → Nat)
    (hpo : ∀ e f, po X e f → rk e < rk f) (hms : ∀ e f, synchronizesWith L X e f → rk e < rk f)
    (hobj : ∀ m e f, MBarrier.Before (X.objects m) (.thread e) (.thread f) →
      (MbarLifetimeRecord X m (.thread e) ∨ MbarLifetimeRecord X m (.thread f) ∨ e.1 = f.1) →
      rk e < rk f) : ObjectCoherent L X := by
  intro o
  refine acyclic_of_rank (prank rk) fun ⟨a, b⟩ ⟨c, b'⟩ h => ?_
  rcases h with h | h
  · exact hp.cause_rank rk hpo hms h
  · cases o with
    | mbar m =>
      obtain ⟨⟨rfl, rfl, hb⟩, hs⟩ := h
      have hb' := hb
      obtain ⟨i, j, r, s, hr, rfl, hs', rfl, -⟩ := hb'
      obtain ⟨e, he⟩ := hp.ids m r (List.mem_of_getElem? hr)
      obtain ⟨f, hf⟩ := hp.ids m s (List.mem_of_getElem? hs')
      rw [he, hf] at hb hs ⊢
      have nsync : ∀ x s g, ¬ MbarSyncRecord X m (.thread x) s g := by
        rintro x s g (⟨-, ⟨_, tx, cnt, -, hrel⟩ | ⟨_, _, hx⟩⟩ | ⟨_, pc, q, -, -, hg⟩)
        · exact hp.noRel _ _ _ _ _ hrel
        · cases hx
        · exact absurd (hp.noAcq _ _ _ _ _ _ _ hg) (by simp)
      have := hobj m e f hb (by
        rcases hs with ⟨_, _, _, _, h1, -, -⟩ | h | h | ⟨_, _, h1, h2, h⟩
        · exact absurd h1 (nsync _ _ _)
        · exact .inl h
        · exact .inr (.inl h)
        · cases h1; cases h2; exact .inr (.inr h))
      simp only [prank]; simp; omega
    | ctaBar c id =>
      obtain ⟨-, -, -, -, -, -, -, -, k, -, x, -, hx, -⟩ := h
      simp [hp.barriers] at hx
    | cluster c =>
      obtain ⟨-, -, -, -, -, -, k, -, x, -, hx, -⟩ := h
      simp [hp.clusters] at hx
    | tmem cta =>
      obtain ⟨-, -, -, -, -, -, -, k, -, x, -, hx, -⟩ := h
      simp [hp.tmem] at hx

end Kept

/-- Program order increases a rank of the shape `scale * index + offset of the thread`. -/
theorem rk_po {X : Execution} (S : Nat) (hS : 0 < S) (off : Nat → Nat) {e f : EvId}
    (h : po X e f) : S * e.2 + off e.1 < S * f.2 + off f.1 := by
  obtain ⟨h1, h2, -⟩ := h
  rw [h1]
  have := Nat.mul_lt_mul_of_pos_left h2 hS
  omega

theorem rk_trace (S : Nat) (hS : 0 < S) (off : Nat → Nat) (e f : EvId) (h1 : e.1 = f.1)
    (h2 : e.2 < f.2) : S * e.2 + off e.1 < S * f.2 + off f.1 := by
  rw [h1]
  have := Nat.mul_lt_mul_of_pos_left h2 hS
  omega

/-! ## K1: load buffering through two mbarriers with single relaxed polls -/

/-- The mbarrier states of the K1 histories: initialized with count 1, after the arrival, and
after the successful poll. -/
def st0 : MBarrier.State := ⟨0, 1, 1, 0, true⟩
def st1 : MBarrier.State := ⟨1, 1, 1, 0, false⟩
def st2 : MBarrier.State := ⟨1, 1, 1, 0, true⟩

/-- Thread 2 initializes `A`; thread 0 arrives; thread 1's poll observes phase 0. -/
def k1A : List (MBarrier.Record AsyncCopy.Ref) := [
  ⟨.thread (2, 0), .init 1, ⟨some st0, none, none⟩, none⟩,
  ⟨.thread (0, 1), .arrive 1 0, ⟨some st1, none, none⟩, none⟩,
  ⟨.thread (1, 0), .pollParity 0 true, ⟨some st2, some true, some 0⟩, none⟩]

/-- Thread 2 initializes `B`; thread 1 arrives; thread 0's poll observes phase 0. -/
def k1B : List (MBarrier.Record AsyncCopy.Ref) := [
  ⟨.thread (2, 1), .init 1, ⟨some st0, none, none⟩, none⟩,
  ⟨.thread (1, 1), .arrive 1 0, ⟨some st1, none, none⟩, none⟩,
  ⟨.thread (0, 0), .pollParity 0 true, ⟨some st2, some true, some 0⟩, none⟩]

/-- Both histories are sequences of the object transitions of OBJ-MBAR-STATE. -/
theorem k1A_checked : MBarrier.CheckedLog k1A :=
  ⟨by decide, _, .cons ⟨rfl, rfl⟩ (.cons ⟨rfl, rfl⟩ (.cons ⟨rfl, rfl⟩ (.nil _)))⟩

theorem k1B_checked : MBarrier.CheckedLog k1B :=
  ⟨by decide, _, .cons ⟨rfl, rfl⟩ (.cons ⟨rfl, rfl⟩ (.cons ⟨rfl, rfl⟩ (.nil _)))⟩

/-- K1: thread 0 polls `B` once (relaxed) and arrives on `A` (relaxed); thread 1 polls `A` once
and arrives on `B`; thread 2 initializes both. Both polls succeed, each observing the other
thread's arrival. -/
def k1X : Execution where
  tr
    | 0 => [⟨0, .wait B 0 true false .cta⟩, ⟨1, .arrive A 0 1 false .cta⟩]
    | 1 => [⟨2, .wait A 0 true false .cta⟩, ⟨3, .arrive B 0 1 false .cta⟩]
    | 2 => [⟨4, .mbInit A 1⟩, ⟨5, .mbInit B 1⟩]
    | _ => []
  rf _ _ := none
  objects m := if m = A then k1A else if m = B then k1B else []

/-- K1 code: each thread polls once and arrives whatever the poll returned. Register 0 is the
poll predicate, register 1 the address of `A` (`B` is 8 bytes above). -/
def k1Code : Kernel where
  name := "k1"
  params := []
  code := [pollI 0 1 8, arriveI 1 0, pollI 0 1 0, arriveI 1 8,
    { op := .mbarInit 1 0 (.imm 1) }, { op := .mbarInit 1 8 (.imm 1) }]

theorem A_ne_B : A ≠ B := by decide

theorem k1X_A : k1X.objects A = k1A := by simp [k1X]
theorem k1X_B : k1X.objects B = k1B := by simp [k1X, A_ne_B.symm]

/-- The events of K1. -/
theorem k1X_get {e : EvId} {ev : Event} (h : k1X.get e = some ev) :
    (e = (0, 0) ∧ ev = ⟨0, .wait B 0 true false .cta⟩) ∨
    (e = (0, 1) ∧ ev = ⟨1, .arrive A 0 1 false .cta⟩) ∨
    (e = (1, 0) ∧ ev = ⟨2, .wait A 0 true false .cta⟩) ∨
    (e = (1, 1) ∧ ev = ⟨3, .arrive B 0 1 false .cta⟩) ∨
    (e = (2, 0) ∧ ev = ⟨4, .mbInit A 1⟩) ∨ (e = (2, 1) ∧ ev = ⟨5, .mbInit B 1⟩) := by
  obtain ⟨t, n⟩ := e
  rcases t with _ | _ | _ | t <;> rcases n with _ | _ | n <;>
    simp [Execution.get, k1X] at h <;> simp [h]

theorem k1X_plain : Plain k1X where
  async := noAsync_of rfl rfl rfl rfl rfl
  noAcq e pc m q ok acq sc h := by
    rcases k1X_get h with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ <;> cases h <;> rfl
  noRel e m tx c s := by
    rintro ⟨pc, h⟩
    rcases k1X_get h with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ <;> cases h
  noWarpBar e m i := by
    rintro ⟨pc, h⟩
    rcases k1X_get h with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ <;> cases h
  noFence e sem s := by
    rintro ⟨pc, h⟩
    rcases k1X_get h with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ <;> cases h
  barriers _ := rfl
  clusters _ := rfl
  tmem _ := rfl
  ids m r hr := by
    simp only [k1X] at hr
    split_ifs at hr <;> simp [k1A, k1B] at hr <;> rcases hr with rfl | rfl | rfl <;> exact ⟨_, rfl⟩

/-- K1 satisfies DEP-ORDER: the polls are no spins (`spinExit?` is none at positions 0 and
2), so no event resumes another, every need of a successful poll is present, and every step goes
from an issue to a completion or forward in one history. -/
theorem k1_dependencyOk (L : Launch) : DependencyOk L k1Code k1X where
  ready := ready_of fun e pc k h hk => by
    rcases k1X_get h with ⟨-, h'⟩ | ⟨-, h'⟩ | ⟨-, h'⟩ | ⟨-, h'⟩ | ⟨-, h'⟩ | ⟨-, h'⟩ <;>
      cases h' <;> first | exact ready_poll h | exact absurd rfl hk
  acyclic := acyclic_flat k1X_plain.async (no_resumes fun w pc k h => by
      rcases k1X_get h with ⟨-, h'⟩ | ⟨-, h'⟩ | ⟨-, h'⟩ | ⟨-, h'⟩ | ⟨-, h'⟩ | ⟨-, h'⟩ <;>
        cases h' <;> first | exact .inl rfl | exact .inr ⟨_, _, _, _, _, rfl, rfl⟩)
    (fun m => by
      by_cases hA : m = A
      · subst hA; rw [k1X_A]; decide
      · by_cases hB : m = B
        · subst hB; rw [k1X_B]; decide
        · simp [k1X, hA, hB])
    k1X_plain.barriers k1X_plain.clusters

/-- K1 satisfies the observation axiom: a relaxed poll is no synchronizing observation. -/
theorem k1_observationCausal (L : Launch) : ObservationCausal L k1X :=
  k1X_plain.observationCausal

/-- The thread offsets of K1: thread 2 initializes before the others. -/
def k1Off (g : Nat) : Nat := if g = 2 then 0 else 2

/-- K1 satisfies per-object coherence: only the pairs with the initializations enter, and they
go forward. -/
theorem k1_objectCoherent (L : Launch) : ObjectCoherent L k1X := by
  refine k1X_plain.objectCoherent (fun e => 1 * e.2 + k1Off e.1)
    (fun e f h => rk_po 1 (by decide) k1Off h) (fun e f h => ?_) (fun m e f hb hs => ?_)
  · obtain ⟨a, b, bs, cs, hw, -⟩ := h
    rcases hw with ⟨pc, hw⟩ | ⟨old, pc, hw⟩ <;>
      rcases k1X_get hw with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ <;> cases h
  · obtain ⟨i, j, r, s, hr, hre, hs', hse, hij⟩ := hb
    by_cases hA : m = A
    · subst hA
      rw [k1X_A] at hr hs'
      rcases i with _ | _ | _ | i <;> rcases j with _ | _ | _ | j <;>
        simp [k1A] at hr hs' hij <;> subst hr hs' <;> cases hre <;> cases hse <;>
        simp [k1Off] at hs ⊢
      simp [MbarLifetimeRecord, Execution.MbInit, Execution.MbInval, Execution.get, k1X] at hs
    · by_cases hB : m = B
      · subst hB
        rw [k1X_B] at hr hs'
        rcases i with _ | _ | _ | i <;> rcases j with _ | _ | _ | j <;>
          simp [k1B] at hr hs' hij <;> subst hr hs' <;> cases hre <;> cases hse <;>
          simp [k1Off] at hs ⊢
        simp [MbarLifetimeRecord, Execution.MbInit, Execution.MbInval, Execution.get, k1X] at hs
      · simp [k1X, hA, hB] at hr

/-- Neither poll of K1 is unsafe: no instruction reads the poll predicate, so both polls are
unused. -/
theorem k1_not_pollShapeUnsafe : ¬ PollShapeUnsafe k1Code k1X :=
  not_pollShapeUnsafe fun e pc m q ok acq sc h => by
    rcases k1X_get h with ⟨-, h'⟩ | ⟨-, h'⟩ | ⟨-, h'⟩ | ⟨-, h'⟩ | ⟨-, h'⟩ | ⟨-, h'⟩ <;> cases h'
    · exact .inr (pollUnused_of rfl rfl rfl)
    · exact .inr (pollUnused_of rfl rfl rfl)

/-! ## K2 and K3: a weak or release/acquire message across a vote -/

/-- A launch of one CTA of two threads: one warp of two lanes. -/
def L2 : Launch where
  grid := 1
  block := 2
  params _ := none

def xLoc : Loc := ⟨.global, 0, 64⟩
def one : Byte := (.bits 8 1, 0)

/-- K2 (`sync = false`) and K3 (`sync = true`): lane 0 runs `vote.sync.all.pred` (mask 3) and
then stores 1 to `x` (weak, or `st.release.cta`); lane 1 loads `x` (weak, or `ld.acquire.cta`)
reading 1 and then runs the vote. -/
def k2X (sync : Bool) : Execution where
  tr
    | 0 => [⟨0, .voteMode .all 3 true true⟩,
        ⟨1, .wr { loc := xLoc, size := 1, release := sync } [one]⟩]
    | 1 => [⟨2, .rd { loc := xLoc, size := 1, acquire := sync } [some one]⟩,
        ⟨3, .voteMode .all 3 true true⟩]
    | _ => []
  rf r _ := if r = .thread (1, 0) then some (.thread (0, 1)) else none

theorem k2X_get {sync : Bool} {e : EvId} {ev : Event} (h : (k2X sync).get e = some ev) :
    (e = (0, 0) ∧ ev = ⟨0, .voteMode .all 3 true true⟩) ∨
    (e = (0, 1) ∧ ev = ⟨1, .wr { loc := xLoc, size := 1, release := sync } [one]⟩) ∨
    (e = (1, 0) ∧ ev = ⟨2, .rd { loc := xLoc, size := 1, acquire := sync } [some one]⟩) ∨
    (e = (1, 1) ∧ ev = ⟨3, .voteMode .all 3 true true⟩) := by
  obtain ⟨t, n⟩ := e
  rcases t with _ | _ | t <;> rcases n with _ | _ | n <;>
    simp [Execution.get, k2X] at h <;> simp [h]

theorem k2X_plain (sync : Bool) : Plain (k2X sync) where
  async := noAsync_of rfl rfl rfl rfl rfl
  noAcq e pc m q ok acq sc h := by
    rcases k2X_get h with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ <;> cases h
  noRel e m tx c s := by
    rintro ⟨pc, h⟩
    rcases k2X_get h with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ <;> cases h
  noWarpBar e m i := by
    rintro ⟨pc, h⟩
    rcases k2X_get h with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ <;> cases h
  noFence e sem s := by
    rintro ⟨pc, h⟩
    rcases k2X_get h with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ <;> cases h
  barriers _ := rfl
  clusters _ := rfl
  tmem _ := rfl
  ids m r hr := by simp [k2X] at hr

/-- K2 and K3 satisfy DEP-ORDER: each vote has both votes as witnesses, and with lane 0
one position ahead of lane 1 every witness has at most the rank of the vote it fills. -/
theorem k2_dependencyOk (K : Kernel) (sync : Bool) : DependencyOk L2 K (k2X sync) where
  ready := ready_of fun e pc k h hk => by
    have v00 : (k2X sync).MaskAt voteClass (0, 0) 3 0 .all :=
      ⟨⟨⟨_, _, rfl, rfl, rfl⟩, by simp⟩, _, _, rfl, rfl, rfl⟩
    have v11 : (k2X sync).MaskAt voteClass (1, 1) 3 0 .all :=
      ⟨⟨⟨_, _, rfl, rfl, rfl⟩, by simp [k2X, voteClass]⟩, _, _, rfl, rfl, rfl⟩
    have sw : ∀ a b, a < 2 → b < 2 → SameWarp L2 a b := by
      intro a b ha hb; simp only [SameWarp, SameCta, Launch.threads, L2]; omega
    rcases k2X_get h with ⟨rfl, h'⟩ | ⟨-, h'⟩ | ⟨-, h'⟩ | ⟨rfl, h'⟩ <;> cases h'
    · refine ready_mask voteClass h rfl rfl fun l hl hb => ?_
      rcases mask3 l hl hb with rfl | rfl
      · exact ⟨0, _, rfl, sw 0 0 (by decide) (by decide), 3, 0, .all, v00, .inl v00⟩
      · exact ⟨1, _, rfl, sw 1 0 (by decide) (by decide), 3, 0, .all, v00, .inl v11⟩
    · exact absurd rfl hk
    · exact absurd rfl hk
    · refine ready_mask voteClass h rfl rfl fun l hl hb => ?_
      rcases mask3 l hl hb with rfl | rfl
      · exact ⟨0, _, rfl, sw 0 1 (by decide) (by decide), 3, 0, .all, v11, .inl v00⟩
      · exact ⟨1, _, rfl, sw 1 1 (by decide) (by decide), 3, 0, .all, v11, .inl v11⟩
  acyclic := acyclic_pos (noAsync_of rfl rfl rfl rfl rfl) (fun e => 1 * e.2 + (1 - e.1))
    (fun e f h1 h2 => by rw [h1]; omega)
    (fun x e hw => by
      obtain ⟨pc, k, he, hk⟩ := witness_kind hw
      have vote : ∀ {pc}, (k2X sync).get e = some ⟨pc, .voteMode .all 3 true true⟩ →
          1 * x.2 + (1 - x.1) ≤ 1 * e.2 + (1 - e.1) := by
        intro pc he'
        have := witness_mask voteClass he' rfl hw
        rcases this.src with ⟨pc', k', p', hx, hc⟩ | ⟨pc', hx⟩ <;>
          rcases k2X_get hx with ⟨rfl, h'⟩ | ⟨rfl, h'⟩ | ⟨rfl, h'⟩ | ⟨rfl, h'⟩ <;>
          cases h' <;> simp [voteClass] at hc <;>
          rcases k2X_get he' with ⟨rfl, h'⟩ | ⟨rfl, h'⟩ | ⟨rfl, h'⟩ | ⟨rfl, h'⟩ <;> cases h' <;>
          decide
      rcases k2X_get he with ⟨-, h'⟩ | ⟨-, h'⟩ | ⟨-, h'⟩ | ⟨-, h'⟩ <;> cases h'
      · exact vote he
      · exact absurd rfl hk
      · exact absurd rfl hk
      · exact vote he)
    (fun o ho a c h => by
      cases o with
      | mbar m => obtain ⟨-, -, _, _, _, _, hr, -⟩ := h; simp [k2X] at hr
      | ctaBar c id => obtain ⟨-, -, -, -, -, -, -, -, k, -, x, -, hx, -⟩ := h; simp [k2X] at hx
      | cluster c => obtain ⟨-, -, -, -, -, -, k, -, x, -, hx, -⟩ := h; simp [k2X] at hx
      | tmem cta => exact ho.elim)

/-- K2 and K3 satisfy the observation axiom: there is no synchronizing observation. -/
theorem k2_observationCausal (sync : Bool) : ObservationCausal L2 (k2X sync) :=
  (k2X_plain sync).observationCausal

/-- K2 and K3 satisfy per-object coherence: causality is program order and, in K3, the
synchronization of the release store with the acquire load; the vote is in neither. -/
theorem k2_objectCoherent (sync : Bool) : ObjectCoherent L2 (k2X sync) := by
  refine (k2X_plain sync).objectCoherent (fun e => 1 * e.2 + 2 * e.1)
    (fun e f h => rk_po 1 (by decide) (2 * ·) h) (fun e f h => ?_) (fun m e f hb _ => ?_)
  · obtain ⟨a, b, bs, cs, hw, hr, -⟩ := h
    rcases hw with ⟨pc, hw⟩ | ⟨old, pc, hw⟩ <;>
      rcases k2X_get hw with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ <;> cases h
    rcases hr with ⟨pc, hr⟩ | ⟨new, pc, hr⟩ <;>
      rcases k2X_get hr with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ <;> cases h
    decide
  · obtain ⟨_, _, _, _, hr, -⟩ := hb
    simp [k2X] at hr

/-! ## K4: all lanes vote and then reduce in the same order -/

def k4Lane : List Event :=
  [⟨0, .voteMode .all 3 true true⟩, ⟨1, .redux .add false 3 1 2⟩, ⟨2, .exit⟩]

/-- K4: both lanes of a two-lane warp run `vote.sync.all.pred` (mask 3), then
`redux.sync.add.u32` (mask 3), then exit. -/
def k4X : Execution where
  tr g := if g < 2 then k4Lane else []
  rf _ _ := none

theorem k4X_get {e : EvId} {ev : Event} (h : k4X.get e = some ev) :
    e.1 < 2 ∧ ((e.2 = 0 ∧ ev = ⟨0, .voteMode .all 3 true true⟩) ∨
      (e.2 = 1 ∧ ev = ⟨1, .redux .add false 3 1 2⟩) ∨ (e.2 = 2 ∧ ev = ⟨2, .exit⟩)) := by
  obtain ⟨t, n⟩ := e
  simp only [Execution.get, k4X] at h
  split_ifs at h with ht
  · refine ⟨ht, ?_⟩
    rcases n with _ | _ | _ | n <;> simp [k4Lane] at h <;> simp [h]
  · simp at h

theorem k4_tr {h : Nat} (hh : h < 2) : k4X.tr h = k4Lane := by
  simp only [k4X, hh, ↓reduceIte]

theorem k4_vote_at {h : Nat} (hh : h < 2) :
    k4X.get (h, 0) = some ⟨0, .voteMode .all 3 true true⟩ := by
  simp [Execution.get, k4_tr hh, k4Lane]

theorem k4_redux_at {h : Nat} (hh : h < 2) :
    k4X.get (h, 1) = some ⟨1, .redux .add false 3 1 2⟩ := by
  simp [Execution.get, k4_tr hh, k4Lane]

theorem sameWarp_L2 {a b : Nat} (ha : a < 2) (hb : b < 2) : SameWarp L2 a b := by
  simp only [SameWarp, SameCta, Launch.threads, L2]; omega

theorem warpLane_L2 {g : Nat} (l : Nat) (hg : g < 2) : warpLane L2 g l = l := by
  simp only [warpLane, laneOf, L2]; omega

/-- Every witness of an event of K4 is at most at the position of the event: a vote has only
votes as witnesses, a reduction only votes and reductions, and no exit is a witness, because each
lane exits after its vote and its reduction. -/
theorem k4_witness {x e : EvId} (hw : Witness L2 k4X (.thread x) e) : x.2 ≤ e.2 := by
  obtain ⟨pc, k, he, hk⟩ := witness_kind hw
  obtain ⟨hg, ⟨he2, h'⟩ | ⟨he2, h'⟩ | ⟨he2, h'⟩⟩ := k4X_get he <;> cases h'
  · obtain ⟨-, m, n, q, ⟨⟨⟨ev, p, hev, hc, hpm⟩, hn⟩, -⟩, hx⟩ := witness_mask voteClass he rfl hw
    rw [he] at hev; cases hev; simp only [voteClass, Option.some.injEq] at hc; subst hc hpm
    rw [k4_tr hg, he2] at hn; simp at hn; subst hn
    rcases hx with ⟨⟨⟨ev', p', hx', hc', -⟩, -⟩, -⟩ | ⟨-, ⟨pc', hx'⟩, hn'⟩
    · obtain ⟨-, ⟨hx2, rfl⟩ | ⟨hx2, rfl⟩ | ⟨hx2, rfl⟩⟩ := k4X_get hx' <;>
        simp [voteClass] at hc'
      omega
    · obtain ⟨hx1, ⟨hx2, h''⟩ | ⟨hx2, h''⟩ | ⟨hx2, h''⟩⟩ := k4X_get hx' <;> cases h''
      rw [k4_tr hx1, hx2] at hn'; simp [k4Lane, voteClass] at hn'
  · obtain ⟨-, m, n, q, ⟨⟨⟨ev, p, hev, hc, hpm⟩, hn⟩, -⟩, hx⟩ := witness_mask reduxClass he rfl hw
    rw [he] at hev; cases hev; simp only [reduxClass, Option.some.injEq] at hc; subst hc hpm
    rw [k4_tr hg, he2] at hn; simp [k4Lane, reduxClass] at hn; subst hn
    rcases hx with ⟨⟨⟨ev', p', hx', hc', -⟩, -⟩, -⟩ | ⟨-, ⟨pc', hx'⟩, hn'⟩
    · obtain ⟨-, ⟨hx2, rfl⟩ | ⟨hx2, rfl⟩ | ⟨hx2, rfl⟩⟩ := k4X_get hx' <;>
        simp [reduxClass] at hc'
      omega
    · obtain ⟨hx1, ⟨hx2, h''⟩ | ⟨hx2, h''⟩ | ⟨hx2, h''⟩⟩ := k4X_get hx' <;> cases h''
      rw [k4_tr hx1, hx2] at hn'; simp [k4Lane, reduxClass] at hn'
  · exact absurd rfl hk

/-- K4 satisfies DEP-ORDER: every vote and every reduction has the two lanes' events of its
instance as witnesses, all at the same position. -/
theorem k4_dependencyOk (K : Kernel) : DependencyOk L2 K k4X where
  ready := ready_of fun e pc k h hk => by
    obtain ⟨g, i⟩ := e
    obtain ⟨hg, ⟨rfl, h'⟩ | ⟨rfl, h'⟩ | ⟨rfl, h'⟩⟩ := k4X_get h <;> cases h'
    · refine ready_mask voteClass h rfl rfl fun l hl hb => ?_
      have hl2 : l < 2 := by rcases mask3 l hl hb with rfl | rfl <;> decide
      have hv : ∀ h' < 2, k4X.MaskAt voteClass (h', 0) 3 0 .all := fun h' hh =>
        ⟨⟨⟨_, _, k4_vote_at hh, rfl, rfl⟩, by simp⟩, _, _, k4_vote_at hh, rfl, rfl⟩
      rw [warpLane_L2 l hg]
      exact ⟨0, _, k4_vote_at hl2, sameWarp_L2 hl2 hg, 3, 0, .all, hv g hg, .inl (hv l hl2)⟩
    · refine ready_mask reduxClass h rfl rfl fun l hl hb => ?_
      have hl2 : l < 2 := by rcases mask3 l hl hb with rfl | rfl <;> decide
      have hv : ∀ h' < 2, k4X.MaskAt reduxClass (h', 1) 3 0 (.add, false) := fun h' hh =>
        ⟨⟨⟨_, _, k4_redux_at hh, rfl, rfl⟩, by simp [k4_tr hh, k4Lane, reduxClass]⟩, _, _,
          k4_redux_at hh, rfl, rfl⟩
      rw [warpLane_L2 l hg]
      exact ⟨1, _, k4_redux_at hl2, sameWarp_L2 hl2 hg, 3, 0, (.add, false), hv g hg,
        .inl (hv l hl2)⟩
    · exact absurd rfl hk
  acyclic := acyclic_pos (noAsync_of rfl rfl rfl rfl rfl) (fun e => e.2)
    (fun _ _ _ h2 => h2) (fun _ _ hw => k4_witness hw)
    (fun o ho a c h => by
      cases o with
      | mbar m => obtain ⟨-, -, _, _, _, _, hr, -⟩ := h; simp [k4X] at hr
      | ctaBar c id => obtain ⟨-, -, -, -, -, -, -, -, k, -, x, -, hx, -⟩ := h; simp [k4X] at hx
      | cluster c => obtain ⟨-, -, -, -, -, -, k, -, x, -, hx, -⟩ := h; simp [k4X] at hx
      | tmem cta => exact ho.elim)

/-! ## Machinery: node ranks and `bar.sync` witnesses -/

section Nodes
variable {L : Launch} {K : Kernel} {X : Execution}

/-- The dependency order with the order of any object has no cycle when a rank of nodes grows
along the stage of each thread event, from every witness to the return it fills, from every
return to the events that depend on it, and along the order of every object. -/
theorem acyclic_nodes (hna : ∀ i p, ¬ X.AsyncPresent i p) (r : AsyncCopy.Ref × Bool → Nat)
    (hst : ∀ e ev, X.get e = some ev → r (.thread e, false) < r (.thread e, true))
    (hw : ∀ x e, Witness L X (.thread x) e → r (.thread x, false) < r (.thread e, true))
    (hres : ∀ w f, Resumes K X w f → r (.thread w, true) < r (.thread f, false))
    (hobj : ∀ o, o.Enabling → ∀ a c, ObjectOrder L X o a c → r a < r c) :
    ∀ o, o.Enabling → ∀ n, ¬ Relation.TransGen (Step L K X o) n n := by
  intro o ho
  refine acyclic_of_rank r fun ⟨a, b⟩ ⟨c, b'⟩ h => ?_
  rcases h with h | h
  · rcases h with h | ⟨-, -, i, p, -, rfl, -, hp, -⟩ | ⟨rfl, rfl, j, rfl, hx⟩ |
        ⟨rfl, rfl, w, j, rfl, rfl, hr⟩
    · obtain ⟨e, ev, rfl, rfl, rfl, rfl, hev⟩ := stageOrder_thread hna h
      exact hst e ev hev
    · exact absurd hp (hna i p)
    · cases a with
      | thread x => exact hw x j hx
      | async i p => obtain ⟨-, -, hpr, -⟩ := hx; exact absurd hpr (hna i p)
    · exact hres w j hr
  · exact hobj o ho _ _ h

/-- A witness of a `bar.sync` is the arrival of a lane of its warp in its record (or that lane's
exit recorded before the record), or a reference that the release of its generation counts. -/
theorem barSync_witness {e y : EvId} {pc id : Nat} {cnt : Option Nat}
    (he : X.get e = some ⟨pc, .bar id cnt .sync⟩) (h : Witness L X (.thread y) e) :
    (∃ i, ∃ r : CtaBarrier.Record EvId, (X.barriers (e.1 / L.block))[i]? = some r ∧ e ∈ r.refs ∧
      (y ∈ r.refs ∨ ∃ (j g : Nat), j < i ∧
        (X.barriers (e.1 / L.block))[j]? = some (CtaBarrier.Record.exit g y))) ∨
    CtaBarCounted L X e y := by
  classical
  obtain ⟨fills, hn, -, hf⟩ := h
  simp only [Needs, he, KindNeeds, ctaBarNeeds, ctaBarWarpNeeds, warpLanes, List.map_map,
    List.mem_append, List.mem_map, List.mem_cons, List.mem_flatMap, needsIf] at hn
  rcases hn with ⟨h', -, hn⟩ | hn | ⟨y', -, hn⟩
  · cases hn
    obtain ⟨i, r, y', hr, he', hy, -, hy'⟩ := hf
    cases hy
    exact .inl ⟨i, r, hr, he', hy'⟩
  · cases hn
  · split_ifs at hn with hc
    · simp only [List.mem_singleton, Need.node.injEq] at hn
      subst hn
      cases hf
      exact .inr hc
    · simp at hn

end Nodes

/-! ## K5: two warps run `bar.sync 1, 64` twice -/

/-- The arrival record of warp `w` of a 64-thread CTA at its `j`-th `bar.sync 1, 64`. -/
def k5Rec (w j : Nat) : CtaBarrier.Record EvId :=
  .arrival 1 w (some 64) ((List.range 32).map fun l => (32 * w + l, (32 * w + l, j)))

/-- The barrier history of K5: both warps arrive at the first `bar.sync`, then both at the
second. -/
def k5Hist : List (CtaBarrier.Record EvId) := [k5Rec 0 0, k5Rec 1 0, k5Rec 0 1, k5Rec 1 1]

/-- K5: the 64 threads of two warps run `bar.sync 1, 64` twice. -/
def k5X : Execution where
  tr g := if g < 64 then [⟨0, .bar 1 (some 64) .sync⟩, ⟨1, .bar 1 (some 64) .sync⟩] else []
  rf _ _ := none
  barriers _ := k5Hist

theorem k5X_get {e : EvId} {ev : Event} (h : k5X.get e = some ev) :
    e.1 < 64 ∧ e.2 < 2 ∧ ev = ⟨e.2, .bar 1 (some 64) .sync⟩ := by
  obtain ⟨g, j⟩ := e
  simp only [Execution.get, k5X] at h
  split_ifs at h with hg
  · rcases j with _ | _ | j <;> simp at h <;> simp [hg, h]
  · simp at h

theorem k5X_get_of {g j : Nat} (hg : g < 64) (hj : j < 2) :
    k5X.get (g, j) = some ⟨j, .bar 1 (some 64) .sync⟩ := by
  rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl <;> simp [Execution.get, k5X, hg]

theorem k5Hist_get {i : Nat} {r : CtaBarrier.Record EvId} (h : k5Hist[i]? = some r) :
    i < 4 ∧ r = k5Rec (i % 2) (i / 2) := by
  rcases i with _ | _ | _ | _ | i <;> simp [k5Hist] at h <;> simp [h]

theorem k5Rec_refs {w j : Nat} {y : EvId} :
    y ∈ (k5Rec w j).refs ↔ ∃ l < 32, y = (32 * w + l, j) := by
  simp only [k5Rec, CtaBarrier.Record.refs, List.map_map, List.mem_map, List.mem_range,
    Function.comp]
  exact ⟨fun ⟨l, hl, h⟩ => ⟨l, hl, h.symm⟩, fun ⟨l, hl, h⟩ => ⟨l, hl, h.symm⟩⟩

/-- The generation of barrier 1 before each record of the K5 history. -/
theorem k5_at {i : Nat} {s : CtaBarrier.State} (hi : i < 4) (h : CtaBarrier.At 64 k5Hist i s) :
    (s.slots 1).generation = i / 2 := by
  have key : ∀ i < 4, Except.map (fun t : CtaBarrier.State => (t.slots 1).generation)
      (CtaBarrier.run 64 {} (k5Hist.take i)) = .ok (i / 2) := by
    intro i hi
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> rfl
  have := key i hi
  rw [show CtaBarrier.run 64 {} (k5Hist.take i) = .ok s from h] at this
  exact Except.ok.inj this


/-- Every reference of the record at position `i` of the K5 history is an arrival of warp `i % 2`
at its `bar.sync` number `i / 2`. -/
theorem k5_ref {i : Nat} {r : CtaBarrier.Record EvId} {y : EvId} (hr : k5Hist[i]? = some r)
    (hy : y ∈ r.refs) : i < 4 ∧ ∃ l < 32, y = (32 * (i % 2) + l, i / 2) := by
  obtain ⟨hi, rfl⟩ := k5Hist_get hr
  exact ⟨hi, k5Rec_refs.mp hy⟩

theorem k5_rec_of {g j : Nat} (hg : g < 64) (hj : j < 2) :
    k5Hist[2 * j + g / 32]? = some (k5Rec (g / 32) j) := by
  rcases (by omega : g / 32 = 0 ∨ g / 32 = 1) with h | h <;>
    rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl <;> simp [h, k5Hist]

theorem k5_mem_rec (g j : Nat) : (g, j) ∈ (k5Rec (g / 32) j).refs :=
  k5Rec_refs.mpr ⟨g % 32, Nat.mod_lt _ (by decide), by rw [Nat.div_add_mod]⟩

/-- The `bar.sync` number `j` of thread `g` belongs to generation `j` of barrier 1. -/
theorem k5_barK {g j : Nat} (hg : g < 64) (hj : j < 2) : CtaBarK L64 k5X (g, j) (1 + 16 * j) := by
  have hm : ∀ w, w < 2 → g / 32 = w → (g, (g, j)) ∈ (List.range 32).map
      (fun l => (32 * w + l, (32 * w + l, j))) := by
    intro w _ hw
    subst hw
    exact List.mem_map.mpr ⟨g % 32, List.mem_range.mpr (Nat.mod_lt _ (by decide)), by
      rw [Nat.div_add_mod]⟩
  refine ⟨by simp only [Launch.threads, L64]; omega, ⟨some 64, j, ?_⟩, ?_⟩
  · rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl <;> exact k5X_get_of hg (by decide)
  · rcases (by omega : g / 32 = 0 ∨ g / 32 = 1) with h | h <;>
      rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
    · exact ⟨0, _, 0, some 64, _, g, rfl, rfl, hm 0 (by decide) h, rfl, _, rfl⟩
    · exact ⟨2, _, 0, some 64, _, g, rfl, rfl, hm 0 (by decide) h, rfl, _, rfl⟩
    · exact ⟨1, _, 1, some 64, _, g, rfl, rfl, hm 1 (by decide) h, rfl, _, rfl⟩
    · exact ⟨3, _, 1, some 64, _, g, rfl, rfl, hm 1 (by decide) h, rfl, _, rfl⟩

/-- Both generations of barrier 1 complete, at the second warp's arrival. -/
theorem k5_done {j : Nat} (hj : j < 2) : CtaBarDone L64 k5X 0 (1 + 16 * j) := by
  rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
  · exact ⟨1, k5Rec 1 0, _, _, rfl, rfl, rfl, by decide⟩
  · exact ⟨3, k5Rec 1 1, _, _, rfl, rfl, rfl, by decide⟩

theorem k5_ready (e : EvId) : Ready L64 k5X e := by
  classical
  intro n hn
  cases he : k5X.get e with
  | none => simp [Needs, he] at hn
  | some ev =>
  obtain ⟨g, j⟩ := e
  obtain ⟨hg, hj, rfl⟩ := k5X_get he
  simp only at hg hj
  simp only [Needs, he, KindNeeds, ctaBarNeeds, List.mem_append, List.mem_cons] at hn
  rcases hn with hn | rfl | hn
  · simp only [ctaBarWarpNeeds, warpLanes, List.map_map, List.mem_map, List.mem_range,
      Function.comp] at hn
    obtain ⟨l, hl, rfl⟩ := hn
    have hws : warpSize L64 g = 32 := by simp only [warpSize, L64]; omega
    have hwl : warpLane L64 g l = 32 * (g / 32) + l := by
      simp only [warpLane, laneOf, L64]; omega
    rw [hws] at hl
    refine ⟨.thread (warpLane L64 g l, j), ⟨_, k5X_get_of (by omega) hj⟩, 2 * j + g / 32,
      k5Rec (g / 32) j, (warpLane L64 g l, j), k5_rec_of hg hj, k5_mem_rec g j, rfl, rfl,
      .inl (k5Rec_refs.mpr ⟨l, hl, by rw [hwl]⟩)⟩
  · exact ⟨1 + 16 * j, k5_barK hg hj, k5_done hj⟩
  · obtain ⟨y, hy, hn⟩ := List.mem_flatMap.mp hn
    obtain ⟨r, hr, hy⟩ := List.mem_flatMap.mp hy
    obtain ⟨i, hi⟩ := List.getElem?_of_mem hr
    obtain ⟨hi4, l, hl, rfl⟩ := k5_ref hi hy
    rw [needsIf] at hn
    split_ifs at hn
    · simp only [List.mem_singleton] at hn
      subst hn
      exact ⟨.thread _, ⟨_, k5X_get_of (by omega) (by omega)⟩, rfl⟩
    · simp at hn

/-- Every witness of a `bar.sync` of K5 is an arrival at the same `bar.sync` number. -/
theorem k5_witness {y e : EvId} (h : Witness L64 k5X (.thread y) e) : y.2 ≤ e.2 := by
  obtain ⟨pc, k, he, -⟩ := witness_kind h
  obtain ⟨-, -, hev⟩ := k5X_get he
  cases hev
  rcases barSync_witness he h with ⟨i, r, hr, he', hy | ⟨j', g', -, hx⟩⟩ | hc
  · obtain ⟨-, l, -, rfl⟩ := k5_ref hr hy
    obtain ⟨-, l', -, he''⟩ := k5_ref hr he'
    rw [he'']
  · obtain ⟨-, hx⟩ := k5Hist_get hx
    cases hx
  · obtain ⟨key, ic, ⟨-, -, i0, s0, w0, c0, lanes, g0, hr0, hs0, hl0, hgen0, -⟩, -, i, r, hr, hy, -,
      hgen⟩ := hc
    obtain ⟨hi0, l0, -, he0⟩ := k5_ref hr0 (List.mem_map_of_mem (f := Prod.snd) hl0)
    have h0 := k5_at hi0 hs0
    simp only at he0
    have hk : key % 16 = 1 := by
      obtain ⟨-, hrec⟩ := k5Hist_get hr0
      simp only [k5Rec, CtaBarrier.Record.arrival.injEq] at hrec
      exact hrec.1
    rw [hk] at hgen0
    obtain ⟨hi, l, -, rfl⟩ := k5_ref hr hy
    rcases hgen with ⟨w, count, lanes', s, hr', hs, hgen⟩ | ⟨g, hr'⟩
    · have := k5_at hi hs
      rw [hk] at hgen
      rw [he0]
      simp only
      omega
    · obtain ⟨-, hx⟩ := k5Hist_get hr
      rw [hr'] at hx
      cases hx

/-- The node rank of K5: each thread event at its position, the issue of warp 1 after the issue
of warp 0, and every return after both issues. -/
def k5Rank : AsyncCopy.Ref × Bool → Nat
  | (.thread e, false) => 4 * e.2 + min (e.1 / 32) 1
  | (.thread e, true) => 4 * e.2 + 2
  | (.async _ _, _) => 0

/-- K5 satisfies DEP-ORDER. -/
theorem k5_dependencyOk (K : Kernel) : DependencyOk L64 K k5X where
  ready e _ := k5_ready e
  acyclic := acyclic_nodes (noAsync_of rfl rfl rfl rfl rfl) k5Rank
    (fun e _ _ => by simp only [k5Rank]; omega)
    (fun x e hw => by have := k5_witness hw; simp only [k5Rank]; omega)
    (fun w f hr => by obtain ⟨⟨h1, h2, -⟩, -⟩ := hr; simp only [k5Rank]; omega)
    (fun o ho a c h => by
      cases o with
      | mbar m => obtain ⟨-, -, _, _, _, _, hr, -⟩ := h; simp [k5X] at hr
      | ctaBar cta id =>
        obtain ⟨a, b⟩ := a
        obtain ⟨c', b'⟩ := c
        obtain ⟨rfl, rfl, i, j, rfl, rfl, -, -, k, l, r, q, hr, hq, hkl, -, -, hi, hj⟩ := h
        obtain ⟨-, l1, hl1, rfl⟩ := k5_ref hr hi
        obtain ⟨hl, l2, hl2, rfl⟩ := k5_ref hq hj
        simp only [k5Rank]
        omega
      | cluster c => obtain ⟨-, -, -, -, -, -, k, -, x, -, hx, -⟩ := h; simp [k5X] at hx
      | tmem cta => exact ho.elim)


/-! ## Machinery: spins -/

section Spins
variable {L : Launch} {K : Kernel} {X : Execution}

/-- Every later event of the thread of the successful poll of a canonical spin depends on it. -/
theorem resumes_spin {w f : EvId} {pc ex q : Nat} {m : Loc} {acq : Bool} {sc : MbarScope}
    {ev : Event} (hw : X.get w = some ⟨pc, .wait m q true acq sc⟩) (hs : K.CanonicalSpin pc ex)
    (hf : X.get f = some ev) (h1 : w.1 = f.1) (h2 : w.2 < f.2) : Resumes K X w f :=
  ⟨traceBefore_of hf h1 h2, by
    simp only [hw, Option.map_some, Kind.resume]
    exact ⟨pc, ex, m, q, acq, sc, hw, hs, traceBefore_of hf h1 h2⟩⟩

/-- A witness of a successful poll is a record of the polled object. -/
theorem poll_witness_mem {e : EvId} {pc q : Nat} {m : Loc} {acq : Bool} {sc : MbarScope}
    {x : AsyncCopy.Ref} (he : X.get e = some ⟨pc, .wait m q true acq sc⟩)
    (h : Witness L X x e) : ∃ r ∈ X.objects m, r.id = x := by
  classical
  obtain ⟨fills, hn, -, hf⟩ := h
  simp only [Needs, he, KindNeeds, ite_true, pollNeeds, List.mem_flatMap, needsIf] at hn
  obtain ⟨r, hr, hn⟩ := hn
  split_ifs at hn
  · simp only [List.mem_singleton, Need.node.injEq] at hn
    subst hn
    exact ⟨r, hr, hf.symm⟩
  · simp at hn

/-- A failed poll has no witness. -/
theorem failed_poll_no_witness {e : EvId} {pc q : Nat} {m : Loc} {acq : Bool} {sc : MbarScope}
    {x : AsyncCopy.Ref} (he : X.get e = some ⟨pc, .wait m q false acq sc⟩) :
    ¬ Witness L X x e := by
  rintro ⟨fills, hn, -⟩
  simp [Needs, he, KindNeeds] at hn

end Spins

/-! ## K6: a spin with a failed and a successful poll -/

/-- K6 code: the consumer spins on `M` at positions 0–2 (shape B, then exit), the producer arrives
at positions 3–4, and a third thread initializes `M` at positions 5–6. Register 0 is the poll
predicate, register 1 the address of `M`. -/
def k6Code : Kernel where
  name := "k6"
  params := []
  code := [pollI 0 1 0, braIf 0 true 0, exitI, arriveI 1 0, exitI,
    { op := .mbarInit 1 0 (.imm 1) }, exitI]

theorem k6_spin : k6Code.CanonicalSpin 0 2 := ⟨rfl, 0, rfl, rfl⟩

/-- The history of `M` in K6: initialization, the failed poll, the arrival, the successful
poll. -/
def k6M : List (MBarrier.Record AsyncCopy.Ref) := [
  ⟨.thread (2, 0), .init 1, ⟨some st0, none, none⟩, none⟩,
  ⟨.thread (1, 0), .pollParity 0 false, ⟨some st0, some false, none⟩, none⟩,
  ⟨.thread (0, 0), .arrive 1 0, ⟨some st1, none, none⟩, none⟩,
  ⟨.thread (1, 1), .pollParity 0 true, ⟨some st2, some true, some 0⟩, none⟩]

theorem k6M_checked : MBarrier.CheckedLog k6M :=
  ⟨by decide, _,
    .cons ⟨rfl, rfl⟩ (.cons ⟨rfl, rfl⟩ (.cons ⟨rfl, rfl⟩ (.cons ⟨rfl, rfl⟩ (.nil _))))⟩

/-- K6: thread 0 arrives on `M`; thread 1 polls `M` once without success, once with success, and
exits; thread 2 initializes `M`. -/
def k6X : Execution where
  tr
    | 0 => [⟨3, .arrive M 0 1 false .cta⟩]
    | 1 => [⟨0, .wait M 0 false false .cta⟩, ⟨0, .wait M 0 true false .cta⟩, ⟨2, .exit⟩]
    | 2 => [⟨5, .mbInit M 1⟩]
    | _ => []
  rf _ _ := none
  objects m := if m = M then k6M else []

theorem k6X_get {e : EvId} {ev : Event} (h : k6X.get e = some ev) :
    (e = (0, 0) ∧ ev = ⟨3, .arrive M 0 1 false .cta⟩) ∨
    (e = (1, 0) ∧ ev = ⟨0, .wait M 0 false false .cta⟩) ∨
    (e = (1, 1) ∧ ev = ⟨0, .wait M 0 true false .cta⟩) ∨
    (e = (1, 2) ∧ ev = ⟨2, .exit⟩) ∨ (e = (2, 0) ∧ ev = ⟨5, .mbInit M 1⟩) := by
  obtain ⟨t, n⟩ := e
  rcases t with _ | _ | _ | t <;> rcases n with _ | _ | _ | n <;>
    simp [Execution.get, k6X] at h <;> simp [h]

/-- The thread ranks of K6: the initialization, the failed poll, the arrival, the successful poll,
the exit. -/
def k6Rk (e : EvId) : Nat :=
  if e.1 = 2 then e.2 else if e.1 = 0 then 2 + e.2 else if e.2 = 0 then 1 else e.2 + 2

/-- K6 satisfies DEP-ORDER: the successful poll has the arrival as its witness, the exit
depends on the successful poll, and the history of `M` follows the ranks. -/
theorem k6_dependencyOk (L : Launch) : DependencyOk L k6Code k6X where
  ready := ready_of fun e pc k h hk => by
    rcases k6X_get h with ⟨-, h'⟩ | ⟨-, h'⟩ | ⟨-, h'⟩ | ⟨-, h'⟩ | ⟨-, h'⟩ <;> cases h'
    · exact absurd rfl hk
    · intro n hn; simp [Needs, h, KindNeeds] at hn
    · exact ready_poll h
    · exact absurd rfl hk
    · exact absurd rfl hk
  acyclic := acyclic_pos (noAsync_of rfl rfl rfl rfl rfl) k6Rk
    (fun e f h1 h2 => by simp only [k6Rk, h1]; split_ifs <;> omega)
    (fun x e hw => by
      obtain ⟨pc, k, he, hk⟩ := witness_kind hw
      rcases k6X_get he with ⟨rfl, h'⟩ | ⟨rfl, h'⟩ | ⟨rfl, h'⟩ | ⟨rfl, h'⟩ | ⟨rfl, h'⟩ <;>
        cases h'
      · exact absurd rfl hk
      · exact absurd hw (failed_poll_no_witness he)
      · obtain ⟨r, hr, hx⟩ := poll_witness_mem he hw
        simp only [k6X, ite_true, k6M, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> cases hx <;> decide
      · exact absurd rfl hk
      · exact absurd rfl hk)
    (fun o ho a c h => by
      cases o with
      | mbar m =>
        obtain ⟨a, b⟩ := a
        obtain ⟨c', b'⟩ := c
        obtain ⟨rfl, rfl, i, j, r, s, hr, rfl, hs, rfl, hij⟩ := h
        by_cases hm : m = M
        · subst hm
          simp only [k6X, ite_true] at hr hs
          rcases i with _ | _ | _ | _ | i <;> rcases j with _ | _ | _ | _ | j <;>
            simp [k6M] at hr hs hij <;> subst hr hs <;> decide
        · simp [k6X, hm] at hr
      | ctaBar cta id => obtain ⟨-, -, -, -, -, -, -, -, k, -, x, -, hx, -⟩ := h; simp [k6X] at hx
      | cluster c => obtain ⟨-, -, -, -, -, -, k, -, x, -, hx, -⟩ := h; simp [k6X] at hx
      | tmem cta => exact ho.elim)

/-! ## K7: a single failed poll -/

/-- K7: thread 0 polls `M` once without success and then stores to `x`. -/
def k7X : Execution where
  tr
    | 0 => [⟨0, .wait M 0 false false .cta⟩, ⟨1, .wr { loc := xLoc, size := 1 } [one]⟩]
    | _ => []
  rf _ _ := none

/-- K7: no event depends on the failed poll, whatever the kernel. -/
theorem k7_no_resumes (K : Kernel) (f : EvId) : ¬ Resumes K k7X (0, 0) f := by
  rintro ⟨-, h⟩
  simp only [Execution.get, k7X, List.getElem?_cons_zero, Option.map_some, Kind.resume] at h
  obtain ⟨pc, ex, m, q, acq, sc, hw, -⟩ := h
  simp [Execution.get] at hw

/-! ## K10 and K11: the canonical spin shapes -/

/-- K10 code, shape A (CuTe inline assembly): `LAB_WAIT: mbarrier.try_wait.parity P1, [addr], 0;
@P1 bra.uni DONE; bra.uni LAB_WAIT; DONE: arrive B; exit` for the consumer (positions 0–4), an
arrive on `M` for the producer (positions 5–6), and the initialization of `M` (positions 7–8). -/
def k10Code : Kernel where
  name := "k10"
  params := []
  code := [pollI 0 1 0, braIf 0 false 3 true, braI 0 true, arriveI 1 8, exitI, arriveI 1 0, exitI,
    { op := .mbarInit 1 0 (.imm 1) }, exitI]

/-- K11 code, shape B (hand-written): `$L__WAIT0: mbarrier.try_wait.parity %p3, [%r3], 0;
@!%p3 bra $L__WAIT0; arrive B; exit` for the consumer (positions 0–3), the producer at positions
4–5, and the initialization at positions 6–7. -/
def k11Code : Kernel where
  name := "k11"
  params := []
  code := [pollI 0 1 0, braIf 0 true 0, arriveI 1 8, exitI, arriveI 1 0, exitI,
    { op := .mbarInit 1 0 (.imm 1) }, exitI]

theorem k10_spin : k10Code.CanonicalSpin 0 3 := ⟨rfl, 0, rfl, rfl⟩

theorem k11_spin : k11Code.CanonicalSpin 0 2 := ⟨rfl, 0, rfl, rfl⟩

/-- The history of `M` in K10 and K11: initialization, the producer's arrival, the consumer's
successful poll. -/
def spinM : List (MBarrier.Record AsyncCopy.Ref) := [
  ⟨.thread (2, 0), .init 1, ⟨some st0, none, none⟩, none⟩,
  ⟨.thread (1, 0), .arrive 1 0, ⟨some st1, none, none⟩, none⟩,
  ⟨.thread (0, 0), .pollParity 0 true, ⟨some st2, some true, some 0⟩, none⟩]

theorem spinM_checked : MBarrier.CheckedLog spinM :=
  ⟨by decide, _, .cons ⟨rfl, rfl⟩ (.cons ⟨rfl, rfl⟩ (.cons ⟨rfl, rfl⟩ (.nil _)))⟩

/-- K10 and K11: the consumer (thread 0) polls `M` successfully at position 0 and arrives on `B`
at position `after`; the producer (thread 1) arrives on `M` at position `prod`; thread 2
initializes `M`. -/
def spinX (after prod init : Nat) : Execution where
  tr
    | 0 => [⟨0, .wait M 0 true false .cta⟩, ⟨after, .arrive B 0 1 false .cta⟩]
    | 1 => [⟨prod, .arrive M 0 1 false .cta⟩]
    | 2 => [⟨init, .mbInit M 1⟩]
    | _ => []
  rf _ _ := none
  objects m := if m = M then spinM else []

/-- The producer's arrival is an update the consumer's successful poll observed. -/
theorem spin_observed (after prod init : Nat) :
    MbarObserved (spinX after prod init) (.thread (1, 0)) (.thread (0, 0)) := by
  refine ⟨⟨_, rfl⟩, (0, 0), M, false, .cta, rfl, ⟨⟨0, 0, rfl⟩, ?_⟩, ?_⟩
  · refine ⟨1, 2, _, _, 0, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by decide, rfl, rfl, ?_⟩
    intro k s h1 h2
    omega
  · intro r hr hid
    simp only [spinX, ite_true, spinM, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> cases hid
    trivial

/-- In K10 and K11, the dependency order leads from the producer's arrival to the consumer's
arrive after the spin: the arrival is a witness of the successful poll, and the event after the
spin depends on the poll's return. -/
theorem spin_path {K : Kernel} {after prod init ex : Nat} (L : Launch)
    (hs : K.CanonicalSpin 0 ex) :
    Relation.TransGen (DepStep L K (spinX after prod init)) (.thread (1, 0), false)
      (.thread (0, 1), false) :=
  .tail (.single (DepStep.of_witness L (poll_witness rfl (spin_observed after prod init))))
    (DepStep.of_resumes L (resumes_spin rfl hs rfl rfl (by decide)))

/-- K10: the shape A spin orders the producer's arrival before the consumer's arrive. -/
theorem k10_path (L : Launch) :
    Relation.TransGen (DepStep L k10Code (spinX 3 5 7)) (.thread (1, 0), false)
      (.thread (0, 1), false) :=
  spin_path L k10_spin

/-- K11: the shape B spin orders the producer's arrival before the consumer's arrive. -/
theorem k11_path (L : Launch) :
    Relation.TransGen (DepStep L k11Code (spinX 2 4 6)) (.thread (1, 0), false)
      (.thread (0, 1), false) :=
  spin_path L k11_spin


/-! ## K8: a `bar.sync` released by the exits of the other warp -/

/-- The arrival record of warp 0 of a 64-thread CTA at `bar.sync 1, 64`. -/
def k8Rec : CtaBarrier.Record EvId :=
  .arrival 1 0 (some 64) ((List.range 32).map fun l => (l, (l, 0)))

/-- The barrier history of K8: the exits of the 32 threads of warp 1, then the arrival of warp
0. -/
def k8Hist : List (CtaBarrier.Record EvId) :=
  (List.range 32).map (fun l => .exit (32 + l) (32 + l, 0)) ++ [k8Rec]

/-- K8: the threads of warp 1 exit; the threads of warp 0 run `bar.sync 1, 64`. -/
def k8X : Execution where
  tr g := if g < 32 then [⟨0, .bar 1 (some 64) .sync⟩] else if g < 64 then [⟨1, .exit⟩] else []
  rf _ _ := none
  barriers _ := k8Hist

theorem k8X_bar {g : Nat} (hg : g < 32) : k8X.get (g, 0) = some ⟨0, .bar 1 (some 64) .sync⟩ := by
  simp [Execution.get, k8X, hg]

theorem k8X_exit {g : Nat} (hg : 32 ≤ g) (hg' : g < 64) : k8X.get (g, 0) = some ⟨1, .exit⟩ := by
  simp [Execution.get, k8X, hg', show ¬ g < 32 by omega]

theorem k8Hist_32 : k8Hist[32]? = some k8Rec := rfl

theorem k8Rec_refs {y : EvId} : y ∈ k8Rec.refs ↔ ∃ l < 32, y = (l, 0) := by
  simp only [k8Rec, CtaBarrier.Record.refs, List.map_map, List.mem_map, List.mem_range,
    Function.comp]
  exact ⟨fun ⟨l, hl, h⟩ => ⟨l, hl, h.symm⟩, fun ⟨l, hl, h⟩ => ⟨l, hl, h.symm⟩⟩

/-- Every reference of the K8 history is a present event: an exit of warp 1 or an arrival of
warp 0. -/
theorem k8_present {y : EvId} (hy : y ∈ k8Hist.flatMap CtaBarrier.Record.refs) :
    k8X.RefPresent (.thread y) := by
  simp only [k8Hist, List.flatMap_append, List.mem_append, List.flatMap_map, List.mem_flatMap,
    List.mem_range, CtaBarrier.Record.refs, List.mem_singleton, List.flatMap_cons,
    List.flatMap_nil, List.append_nil] at hy
  rcases hy with ⟨l, hl, rfl⟩ | hy
  · exact ⟨_, k8X_exit (by omega) (by omega)⟩
  · obtain ⟨l, hl, rfl⟩ := k8Rec_refs.mp hy
    exact ⟨_, k8X_bar hl⟩

/-- The `bar.sync` of every thread of warp 0 belongs to generation 0 of barrier 1. -/
theorem k8_barK {g : Nat} (hg : g < 32) : CtaBarK L64 k8X (g, 0) 1 :=
  ⟨by simp only [Launch.threads, L64]; omega, ⟨some 64, 0, k8X_bar hg⟩, 32, _, 0, some 64, _, g,
    rfl, rfl, List.mem_map.mpr ⟨g, List.mem_range.mpr hg, rfl⟩, rfl, _, rfl⟩

/-- Generation 0 of barrier 1 completes at the arrival of warp 0, since warp 1 has exited. -/
theorem k8_completes : CtaBarrier.CompletesAt 64 k8Hist 32 1 0 :=
  ⟨k8Rec, _, _, rfl, rfl, rfl, by decide⟩

/-- K8: every `bar.sync` of warp 0 is ready. -/
theorem k8_ready {g : Nat} (hg : g < 32) : Ready L64 k8X (g, 0) := by
  classical
  intro n hn
  simp only [Needs, k8X_bar hg, KindNeeds, ctaBarNeeds, List.mem_append, List.mem_cons] at hn
  rcases hn with hn | rfl | hn
  · simp only [ctaBarWarpNeeds, warpLanes, List.map_map, List.mem_map, List.mem_range,
      Function.comp] at hn
    obtain ⟨l, hl, rfl⟩ := hn
    have hws : warpSize L64 g = 32 := by simp only [warpSize, L64]; omega
    have hwl : warpLane L64 g l = l := by simp only [warpLane, laneOf, L64]; omega
    rw [hws] at hl
    refine ⟨.thread (warpLane L64 g l, 0), ⟨_, k8X_bar (by omega)⟩, 32, k8Rec,
      (warpLane L64 g l, 0), k8Hist_32, k8Rec_refs.mpr ⟨g, hg, rfl⟩, rfl, rfl,
      .inl (k8Rec_refs.mpr ⟨l, hl, by rw [hwl]⟩)⟩
  · exact ⟨1, k8_barK hg, 32, k8_completes⟩
  · obtain ⟨y, hy, hn⟩ := List.mem_flatMap.mp hn
    rw [needsIf] at hn
    split_ifs at hn
    · simp only [List.mem_singleton] at hn
      subst hn
      exact ⟨.thread y, k8_present hy, rfl⟩
    · simp at hn

/-- K8: the exit of thread 32 (lane 0 of warp 1) is a witness of the `bar.sync` of thread 0: the
release of its generation counts the exit (§9.7.14.7). -/
theorem k8_exit_witness : Witness L64 k8X (.thread (32, 0)) (0, 0) :=
  witness_of (ctaBarCounted_witnessed L64 k8X _ _ (k8X_bar (by decide))
      (k8Hist.mem_flatMap.mpr ⟨_, List.mem_append_left _ (List.mem_map.mpr
        ⟨0, List.mem_range.mpr (by decide), rfl⟩), List.mem_singleton_self _⟩)
      ⟨1, 32, k8_barK (by decide), k8_completes, 0, _, rfl, List.mem_singleton_self _,
        by decide, .inr ⟨32, rfl⟩⟩)
    (k8X_exit (by decide) (by decide)) rfl


/-! ## K9: the relaxed-poll example -/

/-- The history of `M` in K9: initialization, thread 1's arrival, thread 0's successful poll. -/
def k9M : List (MBarrier.Record AsyncCopy.Ref) := [
  ⟨.thread (2, 0), .init 1, ⟨some st0, none, none⟩, none⟩,
  ⟨.thread (1, 1), .arrive 1 0, ⟨some st1, none, none⟩, none⟩,
  ⟨.thread (0, 0), .pollParity 0 true, ⟨some st2, some true, some 0⟩, none⟩]

theorem k9M_checked : MBarrier.CheckedLog k9M :=
  ⟨by decide, _, .cons ⟨rfl, rfl⟩ (.cons ⟨rfl, rfl⟩ (.cons ⟨rfl, rfl⟩ (.nil _)))⟩

/-- K9 (`sync = false`, the codex relaxed-poll example): thread 0 polls `M` once with a relaxed
`try_wait`, which returns true, and then runs `st.release.cta [x], 1`; thread 1 runs
`ld.acquire.cta r, [x]`, which reads 1, and then a relaxed arrive on `M`; thread 2 initializes
`M`. With `sync = true` the poll is `.acquire` and the arrival `.release`. -/
def k9X (sync : Bool) : Execution where
  tr
    | 0 => [⟨0, .wait M 0 true sync .cta⟩,
        ⟨1, .wr { loc := xLoc, size := 1, release := true } [one]⟩]
    | 1 => [⟨2, .rd { loc := xLoc, size := 1, acquire := true } [some one]⟩,
        ⟨3, .arrive M 0 1 sync .cta⟩]
    | 2 => [⟨4, .mbInit M 1⟩]
    | _ => []
  rf r _ := if r = .thread (1, 0) then some (.thread (0, 1)) else none
  objects m := if m = M then k9M else []

theorem k9X_get {sync : Bool} {e : EvId} {ev : Event} (h : (k9X sync).get e = some ev) :
    (e = (0, 0) ∧ ev = ⟨0, .wait M 0 true sync .cta⟩) ∨
    (e = (0, 1) ∧ ev = ⟨1, .wr { loc := xLoc, size := 1, release := true } [one]⟩) ∨
    (e = (1, 0) ∧ ev = ⟨2, .rd { loc := xLoc, size := 1, acquire := true } [some one]⟩) ∨
    (e = (1, 1) ∧ ev = ⟨3, .arrive M 0 1 sync .cta⟩) ∨ (e = (2, 0) ∧ ev = ⟨4, .mbInit M 1⟩) := by
  obtain ⟨t, n⟩ := e
  rcases t with _ | _ | _ | t <;> rcases n with _ | _ | n <;>
    simp [Execution.get, k9X] at h <;> simp [h]

theorem k9X_plain : Plain (k9X false) where
  async := noAsync_of rfl rfl rfl rfl rfl
  noAcq e pc m q ok acq sc h := by
    rcases k9X_get h with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ <;> cases h
    rfl
  noRel e m tx c s := by
    rintro ⟨pc, h⟩
    rcases k9X_get h with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ <;> cases h
  noWarpBar e m i := by
    rintro ⟨pc, h⟩
    rcases k9X_get h with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ <;> cases h
  noFence e sem s := by
    rintro ⟨pc, h⟩
    rcases k9X_get h with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ <;> cases h
  barriers _ := rfl
  clusters _ := rfl
  tmem _ := rfl
  ids m r hr := by
    simp only [k9X] at hr
    split_ifs at hr
    · simp only [k9M, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact ⟨_, rfl⟩
    · simp at hr

/-- K9 satisfies the observation axiom: the relaxed poll is no synchronizing observation. -/
theorem k9_observationCausal : ObservationCausal L32 (k9X false) :=
  k9X_plain.observationCausal

/-- The thread offsets of K9: the initialization, then thread 0, then thread 1. -/
def k9Off (g : Nat) : Nat := if g = 2 then 0 else if g = 0 then 1 else 3

/-- K9 satisfies per-object coherence: the arrival and the relaxed poll are not synchronizing
records, so the order of `M` enters only with its initialization, and causality runs from the
poll through the release store and the acquire load to the arrival. -/
theorem k9_objectCoherent : ObjectCoherent L32 (k9X false) := by
  refine k9X_plain.objectCoherent (fun e => 1 * e.2 + k9Off e.1)
    (fun e f h => rk_po 1 (by decide) k9Off h) (fun e f h => ?_) (fun m e f hb hs => ?_)
  · obtain ⟨a, b, bs, cs, hw, hr, -⟩ := h
    rcases hw with ⟨pc, hw⟩ | ⟨old, pc, hw⟩ <;>
      rcases k9X_get hw with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ <;> cases h
    rcases hr with ⟨pc, hr⟩ | ⟨new, pc, hr⟩ <;>
      rcases k9X_get hr with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ <;> cases h
    decide
  · obtain ⟨i, j, r, s, hr, hre, hs', hse, hij⟩ := hb
    by_cases hm : m = M
    · subst hm
      simp only [k9X, ite_true] at hr hs'
      rcases i with _ | _ | _ | i <;> rcases j with _ | _ | _ | j <;>
        simp [k9M] at hr hs' hij <;> subst hr hs' <;> cases hre <;> cases hse <;>
        simp [k9Off] at hs ⊢
      simp [MbarLifetimeRecord, Execution.MbInit, Execution.MbInval, Execution.get, k9X] at hs
    · simp [k9X, hm] at hr

theorem sameCta_L32 {g h : Nat} (hg : g < 32) (hh : h < 32) : SameCta L32 g h := by
  simp only [SameCta, Launch.threads, L32]; omega

/-- In the release/acquire variant, the poll precedes the arrival in base causality: program
order, the synchronization of the release store with the acquire load, program order. -/
theorem k9_baseCausality : baseCausality L32 (k9X true) (0, 0) (1, 1) := by
  have po0 : po (k9X true) (0, 0) (0, 1) := ⟨rfl, by decide, by decide, fun hs => by
    have := hs.2 1 (by decide)
    simp [Execution.get, k9X, Event.acc] at this⟩
  have po1 : po (k9X true) (1, 0) (1, 1) := ⟨rfl, by decide, by decide, fun hs => by
    simp [SameAccess, Execution.get, k9X, Event.acc] at hs⟩
  have ms : synchronizesWith L32 (k9X true) (0, 1) (1, 0) :=
    ⟨_, _, _, _, .inl ⟨1, rfl⟩, .inl ⟨2, rfl⟩, rfl, rfl, rfl, rfl, by decide,
      sameCta_L32 (by decide) (by decide), sameCta_L32 (by decide) (by decide),
      fun k _ => by simp [k9X]⟩
  exact .tail (.tail (.single (.inl po0)) (.inr (.inr (.inr (.inr (.inr (.inl ms)))))))
    (.inl po1)

/-- The release/acquire variant of K9 violates per-object coherence: the release arrival precedes
the acquire poll in the order of `M`, both are synchronizing records whose scopes include each
other's thread, and the poll precedes the arrival in causality. -/
theorem k9_sync_not_objectCoherent : ¬ ObjectCoherent L32 (k9X true) := by
  intro h
  let R := fun a c =>
    stageCausality L32 (k9X true) a c ∨ SyncObjectOrder L32 (k9X true) (.mbar M) a c
  have s1 : R (.thread (0, 0), true) (.thread (1, 1), false) :=
    .inl (.inr (.inl ⟨rfl, rfl, (0, 0), (1, 1), rfl, rfl, k9_baseCausality⟩))
  have s2 : R (.thread (1, 1), false) (.thread (1, 1), true) :=
    .inl (.inl (.inl ⟨rfl, rfl, rfl, _, rfl⟩))
  have s3 : R (.thread (1, 1), true) (.thread (0, 0), true) :=
    .inr ⟨⟨rfl, rfl, 1, 2, _, _, rfl, rfl, rfl, rfl, by decide⟩,
      .inl ⟨.cta, 1, .cta, 0, .inl ⟨.inl ⟨(1, 1), M, 0, 1, rfl, rfl, 3, rfl⟩,
        .inl ⟨(1, 1), 0, 1, rfl, 3, rfl⟩⟩, .inr ⟨(0, 0), 0, 0, rfl, rfl, rfl⟩,
        sameCta_L32 (by decide) (by decide), sameCta_L32 (by decide) (by decide)⟩⟩
  exact h (.mbar M) _ (.tail (.tail (.single s1) s2) s3)

/-- One thread whose acquire poll of `M` returned false. -/
def k9fX : Execution where
  tr
    | 0 => [⟨0, .wait M 0 false true .cta⟩]
    | _ => []
  rf _ _ := none

/-- An acquire poll that returned false is no synchronizing record of `M` (§9.7.15.16.19: only a
poll that returns True forms the acquire pattern), while the same poll returning true in the
release/acquire variant of K9 is one. -/
theorem k9_failed_poll_no_record :
    (∀ s g, ¬ MbarSyncRecord k9fX M (.thread (0, 0)) s g) ∧
      MbarSyncRecord (k9X true) M (.thread (0, 0)) .cta 0 := by
  refine ⟨?_, .inr ⟨(0, 0), 0, 0, rfl, rfl, rfl⟩⟩
  rintro s g (⟨-, ⟨j, tx, cnt, hj, pc, h⟩ | ⟨i, p, hx⟩⟩ | ⟨j, pc, q, hj, -, h⟩)
  · cases hj
    simp [Execution.get, k9fX] at h
  · cases hx
  · cases hj
    simp [Execution.get, k9fX] at h

/-! ## K9b: the asynchronous variant -/

/-- The 16-byte bulk copy of K9b, completed through `M`. -/
def k9bCopy : AsyncCopy.Spec where
  src := { loc := ⟨.global, 0, 128⟩, size := 16 }
  dst := { loc := ⟨.shared, 0, 64⟩, size := 16 }
  completion := .mbarrier M

/-- The history of `M` in K9b: initialization, an `arrive.expect_tx` of 16 bytes by thread 2, the
copy's complete-tx, which completes the phase, and thread 0's successful poll. -/
def k9bM : List (MBarrier.Record AsyncCopy.Ref) := [
  ⟨.thread (2, 0), .init 1, ⟨some st0, none, none⟩, none⟩,
  ⟨.thread (2, 1), .arrive 1 16, ⟨some ⟨0, 1, 0, 16, true⟩, none, none⟩, none⟩,
  ⟨.async (1, 1) (.notify .copy), .completeTx 16, ⟨some st1, none, none⟩, none⟩,
  ⟨.thread (0, 0), .pollParity 0 true, ⟨some st2, some true, some 0⟩, none⟩]

theorem k9bM_checked : MBarrier.CheckedLog k9bM :=
  ⟨by decide, _,
    .cons ⟨rfl, rfl⟩ (.cons ⟨rfl, rfl⟩ (.cons ⟨rfl, rfl⟩ (.cons ⟨rfl, rfl⟩ (.nil _))))⟩

/-- K9b: thread 0 polls `M` once with a relaxed `try_wait`, which returns true, then runs
`st.release.cta [x], 1` and exits; thread 1 runs `ld.acquire.cta r, [x]`, which reads 1, then the
16-byte `cp.async.bulk` whose complete-tx on `M` is the only update the phase waits for, and
exits; thread 2 initializes `M` and expects the 16 bytes. -/
def k9bX : Execution where
  tr
    | 0 => [⟨0, .wait M 0 true false .cta⟩,
        ⟨1, .wr { loc := xLoc, size := 1, release := true } [one]⟩, ⟨2, .exit⟩]
    | 1 => [⟨3, .rd { loc := xLoc, size := 1, acquire := true } [some one]⟩, ⟨4, .copy k9bCopy⟩,
        ⟨5, .exit⟩]
    | 2 => [⟨6, .mbInit M 1⟩, ⟨7, .arrive M 16 1 false .cta⟩]
    | _ => []
  rf r _ := if r = .thread (1, 0) then some (.thread (0, 1)) else none
  objects m := if m = M then k9bM else []

/-- K9b satisfies EXT-ASYNC-OBJECT: the only operation after the complete-tx in the order of `M`
is thread 0's poll, which is no earlier operation of thread 1, no lifetime record and no acquire
wait. -/
theorem k9b_asyncObjectOrdered : AsyncObjectOrdered L32 k9bX := by
  intro m i p y hb
  obtain ⟨a, b, r, s, hr, hre, hs, hse, hab⟩ := hb
  by_cases hm : m = M
  · subst hm
    simp only [k9bX, ite_true] at hr hs
    rcases a with _ | _ | _ | _ | a <;> simp [k9bM] at hr <;> subst hr <;> cases hre
    rcases b with _ | _ | _ | _ | b <;> simp [k9bM] at hs hab
    subst hs
    cases hse
    refine ⟨fun ⟨j, hj, h1, _⟩ => ?_, ?_⟩
    · cases hj
      simp at h1
    · rintro (⟨j, hj, ⟨c, pc, hc⟩ | ⟨pc, hc⟩⟩ | ⟨j, ws, hj, ⟨pc, par, hw⟩, -⟩) <;> cases hj
      · simp [Execution.get, k9bX] at hc
      · simp [Execution.get, k9bX] at hc
      · simp [Execution.get, k9bX] at hw
  · simp [k9bX, hm] at hr

end PTX.Tests.DependencyLitmus
