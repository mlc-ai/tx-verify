-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Step.TmemReady
public import Lemmas.Tmem.TmemRun
public import Lemmas.Protocol.CountNth
public import Lemmas.Order.WaitOrderEnables
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

/-! # A CTA pair's Tensor Memory allocation by one warp

A proof tool for a kernel whose Tensor Memory resource operations (`cta_group::2`) are made by
warp `w` of every CTA of a two-CTA cluster: each thread of that warp allocates all 512 columns,
relinquishes its permit and deallocates, in that order (`TmemShape`, by the count `tmemOps` of
the thread's earlier operations). The kernel supplies these facts (`TmemWarpOps`), and for the
safety conclusions that a deallocation frees its CTA's allocated column and that a lane of the
warp exits after its three operations (`TmemPairFacts`).

* Safety: a CTA's history records the operations of warp `w` in order (`record_info`,
  `history_ops`); it replays without a fault and records no allocation after a deallocation
  (`no_resource_unsafe`), and once every thread has exited and every operation is complete it
  leaves its allocator empty (`no_release_unsafe`).
* Progress: a record makes the `n`-th operation of the 32 lanes of warp `w` of its CTA
  (`record_shape`), a pairing pairs the `n`-th operations of the two CTAs (`pairing_shape`), so
  the `n`-th operations of a pair are covered together (`covered_all`); once every lane of the
  pair made its `n`-th operation, none covered, a step completing them is ready (`pair_ready`:
  `entry_ready`, `pairing_ready`). -/

namespace PTX.Tmem.Pair

noncomputable section

/-- A paired Tensor Memory operation. -/
def isTmemOp (e : Event) : Bool := match e.kind with | .tc (.resource ..) => true | _ => false

/-- A thread's paired Tensor Memory operations. -/
def tmemOps (es : List Event) : Nat := es.countP isTmemOp

/-- The `n`-th operation of a thread: the allocation of 512 columns, the relinquishment, the
deallocation of 512 columns. -/
def TmemShape : Nat → Tmem.Request → Prop
  | 0, a => a = .alloc 512
  | 1, a => a = .relinquish
  | 2, a => ∃ base, a = .dealloc base 512
  | _, _ => False

theorem lt_of_tmemShape {n : Nat} {a : Tmem.Request} (h : TmemShape n a) : n < 3 := by
  rcases n with _ | _ | _ | n <;> simp_all [TmemShape]

/-- The index of the kind of an operation. -/
def actIdx : Tmem.Request → Nat
  | .alloc .. => 0
  | .relinquish => 1
  | .dealloc .. => 2

theorem actIdx_of_shape {n : Nat} {a : Tmem.Request} (h : TmemShape n a) : actIdx a = n := by
  rcases n with _ | _ | _ | n
  · simp only [TmemShape] at h; subst h; rfl
  · simp only [TmemShape] at h; subst h; rfl
  · obtain ⟨b, rfl⟩ := h; rfl
  · exact h.elim

/-- Compatible requests are of one kind. -/
theorem actIdx_compat {a b : Tmem.Request} (h : compatible a b = true) : actIdx a = actIdx b := by
  cases a <;> cases b <;> simp_all [compatible, actIdx]

/-- An allocation is a thread's first operation. -/
theorem shape_alloc {m n : Nat} (h : TmemShape m (.alloc n)) : m = 0 ∧ n = 512 := by
  rcases m with _ | _ | _ | m
  · simp only [TmemShape, Tmem.Request.alloc.injEq] at h
    exact ⟨rfl, h⟩
  · simp [TmemShape] at h
  · simp [TmemShape] at h
  · exact h.elim

/-- **The resource operations of warp `w`.** Every Tensor Memory resource operation is made by
warp `w` of its CTA, in group two, and a thread's `n`-th has the shape `TmemShape n`; the
launch is one-dimensional, the cluster has two CTAs and the warp is in the block. -/
structure TmemWarpOps (L : Launch) (X : Execution) (w : Nat) : Prop where
  launch : L.oneDimLaunch
  cluster : L.clusterSize.val = 2
  warp_lt : (w + 1) * 32 ≤ L.block
  event : ∀ {g k pc : Nat} {grp : CtaGroup} {dst : Option Loc} {act : Tmem.Request},
    g < L.threads → X.get (g, k) = some ⟨pc, .tc (.resource grp dst act)⟩ →
    g % L.block / 32 = w ∧ grp = .two ∧ TmemShape (tmemOps ((X.tr g).take k)) act

/-- **The Tensor Memory pair facts of warp `w`**: its operations (`TmemWarpOps`); a deallocation
frees the column of its CTA's recorded allocation; a lane of warp `w` exits after its three
operations. -/
structure TmemPairFacts (L : Launch) (X : Execution) (w : Nat) : Prop
    extends TmemWarpOps L X w where
  dealloc : ∀ {g k pc : Nat} {grp : CtaGroup} {dst : Option Loc} {a n : Nat}, g < L.threads →
    X.get (g, k) = some ⟨pc, .tc (.resource grp dst (.dealloc a n))⟩ →
    ∀ r ∈ X.tmemHistory (g / L.block), ∀ col, r.action = .alloc 512 col → a = col % 2 ^ 32
  exit : ∀ {g k pc : Nat}, g < L.threads → g % L.block / 32 = w →
    X.get (g, k) = some ⟨pc, .exit⟩ → tmemOps ((X.tr g).take k) = 3

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution} {w : Nat}

/-! ## A thread's operations -/

/-- The paired operations of thread `g` before its `i`-th event. -/
abbrev opsAt (X : Execution) (g i : Nat) : Nat := tmemOps ((X.tr g).take i)

/-- A thread's paired operations before an operation are fewer than before any later event. -/
theorem tmemOps_lt {g i j : Nat} {e : Event} (he : X.get (g, i) = some e)
    (ht : isTmemOp e = true) (hij : i < j) :
    tmemOps ((X.tr g).take i) < tmemOps ((X.tr g).take j) := by
  have h1 : (X.tr g).take (i + 1) = (X.tr g).take i ++ [e] := by
    rw [List.take_add_one]
    congr
    simpa [Execution.get] using he
  have h2 : tmemOps ((X.tr g).take (i + 1)) ≤ tmemOps ((X.tr g).take j) :=
    (List.take_sublist_take_left (show i + 1 ≤ j by omega)).countP_le
  rw [h1] at h2
  simp only [tmemOps, List.countP_append, List.countP_singleton, ht, ↓reduceIte] at h2
  unfold tmemOps
  omega

/-- A paired operation is a resource event. -/
theorem tmemOp_resource {e : Event} (h : isTmemOp e = true) :
    ∃ pc grp dst act, e = ⟨pc, .tc (.resource grp dst act)⟩ := by
  obtain ⟨pc, kind⟩ := e
  unfold isTmemOp at h
  split at h
  · rename_i grp dst act hk
    exact ⟨pc, grp, dst, act, by simp only at hk; rw [hk]⟩
  · simp at h

/-- A list with `m` elements satisfying `p` among its first `k` has its `j`-th for each `j < m`. -/
theorem countP_take_occ {α : Type} (p : α → Bool) (l : List α) :
    ∀ k j, j < (l.take k).countP p →
      ∃ i < k, ∃ h : i < l.length, p l[i] = true ∧ (l.take i).countP p = j := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    intro j hj
    rw [List.take_add_one] at hj
    rcases hk : l[k]? with _ | a
    · simp only [hk, Option.toList_none, List.append_nil] at hj
      obtain ⟨i, hi, h⟩ := ih j hj
      exact ⟨i, by omega, h⟩
    · simp only [hk, Option.toList_some, List.countP_append, List.countP_singleton] at hj
      by_cases hlt : j < (l.take k).countP p
      · obtain ⟨i, hi, h⟩ := ih j hlt
        exact ⟨i, by omega, h⟩
      · obtain ⟨hkl, rfl⟩ := List.getElem?_eq_some_iff.mp hk
        by_cases hpa : p l[k] = true
        · exact ⟨k, by omega, hkl, hpa, by simp [hpa] at hj; omega⟩
        · simp [hpa] at hj
          omega

/-- Two positions of a block of size `B`: equal sums with offsets below `B` are equal. -/
theorem block_pos_inj {B c c' l l' : Nat} (hl : l < B) (hl' : l' < B)
    (h : c * B + l = c' * B + l') : c = c' ∧ l = l' := by
  have hB : 0 < B := by omega
  have e1 : (l + c * B) / B = c := by rw [Nat.add_mul_div_right _ _ hB, Nat.div_eq_of_lt hl]; simp
  have e2 : (l' + c' * B) / B = c' := by
    rw [Nat.add_mul_div_right _ _ hB, Nat.div_eq_of_lt hl']; simp
  have h' : l + c * B = l' + c' * B := by omega
  have hc : c = c' := by rw [← e1, ← e2, h']
  subst hc
  exact ⟨rfl, by omega⟩

/-! ## The records of a CTA's history -/

/-- The lane-0 event of a warp request of a recorded history: a paired operation of warp `w` of
its CTA, its thread's `n`-th. -/
theorem warp_info (ht : TmemWarpOps L X w) {q : WarpRequest} {grp : CtaGroup}
    (hv : q.Valid L X grp) :
    q.warp = w ∧ grp = .two ∧
      X.get (q.cta * L.block + w * 32, q.indices 0) =
        some ⟨q.pc, .tc (.resource grp q.dst q.request)⟩ ∧
      TmemShape (opsAt X (q.cta * L.block + w * 32) (q.indices 0)) q.request := by
  obtain ⟨-, h2, h3⟩ := WarpRequest.event_props hv 0
  have he := hv.2.2.1 0
  simp only [WarpRequest.event, Fin.val_zero, Nat.add_zero] at h2 h3 he
  obtain ⟨hw, hgrp, hshape⟩ := ht.event h3 he
  have hq : q.warp = w := h2.symm.trans hw
  rw [hq] at he hshape
  exact ⟨hq, hgrp, he, hshape⟩

/-- A record of CTA `cta`'s history: warp `w` of `cta`, a cta_group::2 request at its thread's
`n`-th operation, of its shape, performed by its action. -/
theorem record_info (hX : Consistent L K A mem0 X) (ht : TmemWarpOps L X w) {cta : Nat}
    {r : Requests} (hr : r ∈ X.tmemHistory cta) :
    r.own.cta = cta ∧ r.own.warp = w ∧ r.group = .two ∧ r.action.request = r.own.request ∧
      X.get (cta * L.block + w * 32, r.own.indices 0) =
        some ⟨r.own.pc, .tc (.resource .two r.own.dst r.own.request)⟩ ∧
      TmemShape (opsAt X (cta * L.block + w * 32) (r.own.indices 0)) r.own.request := by
  obtain ⟨hval, hown, -⟩ := hX.tmemPair.1 cta
  have hcta := hown r hr
  obtain ⟨-, hreq, hv⟩ := hval r hr
  obtain ⟨hw, hgrp, hle, hls⟩ := warp_info ht hv
  rw [hcta, hgrp] at hle
  rw [hcta] at hls
  exact ⟨hcta, hw, hgrp, hreq, hle, hls⟩

/-- The lane-0 thread of a record's warp is a launched thread. -/
theorem record_thread (hX : Consistent L K A mem0 X) (ht : TmemWarpOps L X w) {cta : Nat}
    {r : Requests} (hr : r ∈ X.tmemHistory cta) : cta * L.block + w * 32 < L.threads := by
  have h3 := (WarpRequest.event_props ((hX.tmemPair.1 cta).1 r hr).2.2 0).2.2
  obtain ⟨hc, hw, -⟩ := record_info hX ht hr
  simpa [WarpRequest.event, hc, hw] using h3

/-- A CTA's history is in warp `w`'s program order. -/
theorem history_before (hX : Consistent L K A mem0 X) (ht : TmemWarpOps L X w) {cta : Nat}
    {a b : Requests} (ha : a ∈ X.tmemHistory cta) (hb : b ∈ X.tmemHistory cta)
    (hab : a.own.Ordered b.own) : a.own.Before b.own := by
  obtain ⟨hca, hwa, -⟩ := record_info hX ht ha
  obtain ⟨hcb, hwb, -⟩ := record_info hX ht hb
  exact hab (hca.trans hcb.symm) (hwa.trans hwb.symm)

/-- An event of lane 0 of warp `w` of a CTA covered by a completed operation is a record of that
CTA's history: the operations are cta_group::2, completed by pairings of recorded requests. -/
theorem covered_record (hX : Consistent L K A mem0 X) (ht : TmemWarpOps L X w) {cta i : Nat}
    (hc : Covered L X (cta * L.block + w * 32, i)) :
    ∃ r ∈ X.tmemHistory cta, r.own.indices 0 = i := by
  obtain ⟨ws, hws, q, hq, lane, hl⟩ := hc
  obtain ⟨r, hr, hrw⟩ : ∃ r ∈ X.tmemHistory q.cta, r.own = q := by
    rcases hws with ⟨k, x, hx, hg, rfl⟩ | ⟨p, hp, rfl⟩
    · rw [List.mem_singleton.mp hq]
      obtain ⟨-, -, hg2, -⟩ := record_info hX ht hx
      rw [hg] at hg2
      cases hg2
    · obtain ⟨-, ⟨a, ha, ha1, -⟩, b, hb, hb1, -⟩ := hX.tmemPair.2.1 p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · exact ⟨a, ha, ha1⟩
      · exact ⟨b, hb, hb1⟩
  subst hrw
  obtain ⟨hcta, hw0, -⟩ := record_info hX ht hr
  have hwb := ht.warp_lt
  simp only [WarpRequest.event, hw0, Prod.mk.injEq] at hl
  obtain ⟨hl1, hl2⟩ := hl
  have hlane := lane.isLt
  obtain ⟨hk, hl0⟩ := block_pos_inj (B := L.block) (c := r.own.cta) (c' := cta)
    (l := w * 32 + lane) (l' := w * 32 + 0) (by omega) (by omega) (by omega)
  have hl0 : lane = 0 := by ext; simp only [Fin.val_zero]; omega
  subst hl0
  rw [hk] at hr
  exact ⟨r, hr, hl2⟩

/-- A record of a thread's first operation is its history's first. -/
theorem history_first (hX : Consistent L K A mem0 X) (ht : TmemWarpOps L X w) {cta : Nat}
    {r : Requests} (hr : r ∈ X.tmemHistory cta)
    (h0 : opsAt X (cta * L.block + w * 32) (r.own.indices 0) = 0) :
    ∃ rest, X.tmemHistory cta = r :: rest := by
  obtain ⟨s, t, hst⟩ := List.append_of_mem hr
  cases s with
  | nil => exact ⟨t, hst⟩
  | cons x s =>
    exfalso
    have hord := hX.object.tmemOrdered hX.tmemPair cta
    rw [hst] at hord
    have hx : x ∈ X.tmemHistory cta := by rw [hst]; simp
    have hxr := (List.pairwise_cons.mp hord).1 r (by simp)
    obtain ⟨-, -, hlt⟩ := history_before hX ht hx hr hxr
    obtain ⟨-, -, -, -, hle, -⟩ := record_info hX ht hx
    have := tmemOps_lt hle rfl (hlt 0)
    simp only [opsAt] at h0
    omega

/-- **A recorded allocation is of all 512 columns at column 0**: it is its history's first
record, and an empty allocator performs such an allocation only at column 0. -/
theorem alloc_zero (hX : Consistent L K A mem0 X) (ht : TmemWarpOps L X w) {cta : Nat}
    {r : Requests} (hr : r ∈ X.tmemHistory cta) :
    ∀ n col, r.action = .alloc n col → n = 512 ∧ col = 0 := by
  intro n col hl
  obtain ⟨-, -, -, hreq, -, hls⟩ := record_info hX ht hr
  rw [← hreq, hl] at hls
  obtain ⟨h0, rfl⟩ := shape_alloc hls
  obtain ⟨rest, hh⟩ := history_first hX ht hr h0
  have hrun := (hX.tmemPair.1 cta).2.2
  rw [hh] at hrun
  refine ⟨rfl, ?_⟩
  by_contra hc
  apply hrun
  simp [runRequests, hl, perform_alloc, hc]

/-- A covered event of lane 0 of warp `w` of CTA `cta` is recorded in its CTA's history, and an
allocation it records is at column 0. -/
theorem alloc_recorded (hX : Consistent L K A mem0 X) (ht : TmemWarpOps L X w) {cta i : Nat}
    (hc : Covered L X (cta * L.block + w * 32, i)) :
    ∃ r ∈ X.tmemHistory cta, r.own.event L 0 = (cta * L.block + w * 32, i) ∧
      ∀ n col, r.action = .alloc n col → col = 0 := by
  obtain ⟨r, hr, hi⟩ := covered_record hX ht hc
  obtain ⟨hcta, hw, -⟩ := record_info hX ht hr
  refine ⟨r, hr, ?_, fun n col h => (alloc_zero hX ht hr n col h).2⟩
  simp [WarpRequest.event, hw, hcta, hi]

/-- A thread of warp `w` that has made an operation before an event of its trace has its first
operation recorded in its CTA's history: the operation is complete, since the thread went on. -/
theorem first_recorded (hX : Consistent L K A mem0 X) (ht : TmemWarpOps L X w) {cta j : Nat}
    (hj : j < (X.tr (cta * L.block + w * 32)).length)
    (h0 : 0 < opsAt X (cta * L.block + w * 32) j) :
    ∃ r ∈ X.tmemHistory cta, opsAt X (cta * L.block + w * 32) (r.own.indices 0) = 0 := by
  obtain ⟨i, hij, hil, hpi, hci⟩ := countP_take_occ _ _ _ _ h0
  have hget : X.get (cta * L.block + w * 32, i) = some (X.tr (cta * L.block + w * 32))[i] :=
    List.getElem?_eq_getElem hil
  obtain ⟨pce, grp, dst, act, he⟩ := tmemOp_resource hpi
  rw [he] at hget
  have hT : cta * L.block + w * 32 < L.threads := by
    by_contra hn
    rw [hX.outside _ (by omega)] at hj
    simp at hj
  have hsh := (ht.event hT hget).2.2
  unfold tmemOps at hsh
  rw [hci] at hsh
  simp only [TmemShape] at hsh
  subst hsh
  obtain ⟨r, hr, hri⟩ := covered_record hX ht (hX.tmemPairBlocking.covered
    ⟨pce, _, _, _, hget, trivial⟩ (show i + 1 < (X.tr (cta * L.block + w * 32)).length by omega))
  exact ⟨r, hr, by rw [hri]; exact hci⟩

/-! ## Safety: the replay of a CTA's history -/

/-- A record's action is its operation's, at column 0. -/
theorem record_act (hX : Consistent L K A mem0 X) (ht : TmemPairFacts L X w) {cta : Nat}
    {r : Requests} (hr : r ∈ X.tmemHistory cta) :
    r.action = opAct 0 (opsAt X (cta * L.block + w * 32) (r.own.indices 0)) := by
  have hto := ht.toTmemWarpOps
  obtain ⟨-, -, -, hreq, hle, hls⟩ := record_info hX hto hr
  have hn := lt_of_tmemShape hls
  generalize hgn : opsAt X (cta * L.block + w * 32) (r.own.indices 0) = n at hn hls
  rw [← hreq] at hls
  interval_cases n <;> simp only [TmemShape] at hls
  · obtain ⟨c1, ha⟩ := Tmem.Action.request_eq_alloc hls
    obtain ⟨-, rfl⟩ := alloc_zero hX hto hr _ _ ha
    exact ha
  · exact Tmem.Action.request_eq_relinquish hls
  · obtain ⟨b1, hb1⟩ := hls
    have ha := Tmem.Action.request_eq_dealloc hb1
    rw [← hreq, ha] at hle
    have hT := record_thread hX hto hr
    have hwb := ht.warp_lt
    have hdiv : (cta * L.block + w * 32) / L.block = cta := by
      rw [Nat.mul_comm, Nat.mul_add_div (by omega), Nat.div_eq_of_lt (by omega)]
      simp
    obtain ⟨r0, hr0, h00⟩ := first_recorded hX hto (len_of_get hle) (by
      rw [hgn]; decide)
    obtain ⟨-, -, -, hreq0, -, hls0⟩ := record_info hX hto hr0
    rw [h00] at hls0
    simp only [TmemShape] at hls0
    rw [← hreq0] at hls0
    obtain ⟨c0, ha0⟩ := Tmem.Action.request_eq_alloc hls0
    have hc0 := (alloc_zero hX hto hr0 _ _ ha0).2
    have h1 := ht.dealloc hT hle r0 (by rw [hdiv]; exact hr0) c0 ha0
    rw [ha, h1, hc0]
    rfl

/-- Increasing operation counts, with a deallocation only after its allocation. -/
theorem ops_pattern {ns : List Nat} (hp : ns.Pairwise (· < ·)) (hb : ∀ n ∈ ns, n ≤ 2)
    (h2 : 2 ∈ ns → 0 ∈ ns) :
    ns = [] ∨ ns = [0] ∨ ns = [1] ∨ ns = [0, 1] ∨ ns = [0, 2] ∨ ns = [0, 1, 2] := by
  rcases ns with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, rest⟩⟩⟩⟩
  · simp
  · have := hb a (by simp)
    interval_cases a <;> simp_all
  · have := hb a (by simp)
    have := hb b (by simp)
    simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil] at hp
    interval_cases a <;> interval_cases b <;> simp_all
  · have := hb a (by simp)
    have := hb b (by simp)
    have := hb c (by simp)
    simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil] at hp
    interval_cases a <;> interval_cases b <;> interval_cases c <;> simp_all
  · have := hb d (by simp)
    simp only [List.pairwise_cons, List.mem_cons] at hp
    have h1 := hp.1 b (by simp)
    have h2 := hp.2.1 c (by simp)
    have h3 := hp.2.2.1 d (by simp)
    omega

/-- A CTA's history: its records' operation counts, increasing, and their actions at
column 0. -/
theorem history_ops (hX : Consistent L K A mem0 X) (ht : TmemPairFacts L X w) (cta : Nat) :
    (X.tmemHistory cta).map (·.action) =
        ((X.tmemHistory cta).map fun r => opsAt X (cta * L.block + w * 32) (r.own.indices 0)).map
          (opAct 0) ∧
      ((X.tmemHistory cta).map fun r => opsAt X (cta * L.block + w * 32) (r.own.indices 0)).Pairwise
        (· < ·) ∧
      ∀ n ∈ (X.tmemHistory cta).map fun r => opsAt X (cta * L.block + w * 32) (r.own.indices 0),
        n ≤ 2 := by
  have hto := ht.toTmemWarpOps
  refine ⟨?_, ?_, ?_⟩
  · rw [List.map_map]
    exact List.map_congr_left fun r hr => record_act hX ht hr
  · rw [List.pairwise_map]
    refine (hX.object.tmemOrdered hX.tmemPair cta).imp_of_mem fun {a b} ha hb hab => ?_
    obtain ⟨-, -, -, -, hle, -⟩ := record_info hX hto ha
    obtain ⟨-, -, hlt⟩ := history_before hX hto ha hb hab
    exact tmemOps_lt hle rfl (hlt 0)
  · simp only [List.mem_map]
    rintro n ⟨r, hr, rfl⟩
    obtain ⟨-, -, -, -, -, hls⟩ := record_info hX hto hr
    have := lt_of_tmemShape hls
    omega

/-- **No CTA's resource history faults, and no allocation follows a deallocation.** -/
theorem no_resource_unsafe (hX : Consistent L K A mem0 X) (ht : TmemPairFacts L X w) :
    ¬ ResourceUnsafe L X := by
  have hto := ht.toTmemWarpOps
  refine not_resourceUnsafe (fun cta reason hf => ?_) (fun cta => ?_)
  swap
  · have hp := (history_ops hX ht cta).2.1
    rw [List.pairwise_map] at hp
    refine hp.imp_of_mem fun {d a} _ ha hlt _ n base han => ?_
    rw [record_act hX ht ha] at han
    generalize opsAt X (cta * L.block + w * 32) (a.own.indices 0) = m at han hlt
    rcases m with _ | _ | m
    · omega
    · cases han
    · cases han
  obtain ⟨hacts, hp, hb⟩ := history_ops hX ht cta
  refine run_alloc_ok hacts (ops_pattern hp hb ?_) reason hf
  simp only [List.mem_map]
  rintro ⟨r, hr, hn⟩
  obtain ⟨-, -, -, -, hle, -⟩ := record_info hX hto hr
  obtain ⟨r0, hr0, h0⟩ := first_recorded hX hto (len_of_get hle) (by rw [hn]; decide)
  exact ⟨r0, hr0, h0⟩

/-- **Once every thread has exited and every operation is complete, no allocation is live.** -/
theorem no_release_unsafe (hX : Consistent L K A mem0 X) (ht : TmemPairFacts L X w) :
    ¬ ReleaseUnsafe L X := by
  have hto := ht.toTmemWarpOps
  rintro ⟨hexit, hdrain, hrel⟩
  apply hrel
  intro cta s hd
  rcases hH : X.tmemHistory cta with _ | ⟨r, rest⟩
  · rw [hH] at hd
    simp only [runRequests, Tmem.Outcome.done.injEq] at hd
    subst hd
    rfl
  have hr : r ∈ X.tmemHistory cta := by simp [hH]
  obtain ⟨-, -, -, -, hle, -⟩ := record_info hX hto hr
  have hT := record_thread hX hto hr
  have hwb := ht.warp_lt
  obtain ⟨hacts, hp, hb⟩ := history_ops hX ht cta
  rcases hexit _ hT with ⟨hnil, -⟩ | ⟨pc, hlast⟩
  · simp [Execution.get, hnil] at hle
  rw [List.getLast?_eq_getElem?] at hlast
  replace hlast : X.get (cta * L.block + w * 32,
      (X.tr (cta * L.block + w * 32)).length - 1) = some ⟨pc, .exit⟩ := hlast
  have hwarp : (cta * L.block + w * 32) % L.block / 32 = w := by
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
    omega
  have h3 := ht.exit hT hwarp hlast
  have hocc : ∀ j < 3,
      j ∈ (X.tmemHistory cta).map fun r => opsAt X (cta * L.block + w * 32) (r.own.indices 0) := by
    intro j hj
    rw [← h3] at hj
    obtain ⟨i, -, hil, hpi, hci⟩ := countP_take_occ _ _ _ _ hj
    have hget : X.get (cta * L.block + w * 32, i) = some (X.tr (cta * L.block + w * 32))[i] :=
      List.getElem?_eq_getElem hil
    obtain ⟨pce, grp, dst, act, he⟩ := tmemOp_resource hpi
    rw [he] at hget
    obtain ⟨r', hr', hi'⟩ := covered_record hX hto (hdrain _ _ _ _ _ hget)
    exact List.mem_map.mpr ⟨r', hr', by rw [hi']; exact hci⟩
  have hns := ops_pattern hp hb (fun _ => hocc 0 (by decide))
  have h1 := hocc 1 (by decide)
  have h2 := hocc 2 (by decide)
  rcases hns with h | h | h | h | h | h <;> rw [h] at h1 h2 hacts <;> simp at h1 h2
  exact run_alloc_released hacts hd

/-! ## Progress: the lanes of a pair -/

/-- Event `j` of thread `h` is its `n`-th paired Tensor Memory operation. -/
def TmemOp (X : Execution) (h n j : Nat) : Prop :=
  (∃ pc grp dst act, X.get (h, j) = some ⟨pc, .tc (.resource grp dst act)⟩) ∧
    tmemOps ((X.tr h).take j) = n

/-- An operation is counted by every later prefix. -/
theorem tmemOps_lt_of_lt {h j j' n : Nat} (hop : TmemOp X h n j) (hjj : j < j') :
    n < tmemOps ((X.tr h).take j') := by
  obtain ⟨⟨pc, grp, dst, act, he⟩, rfl⟩ := hop
  exact tmemOps_lt he rfl hjj

/-- A thread's `n`-th operation is one event. -/
theorem tmemOp_unique {h n j j' : Nat} (hop : TmemOp X h n j) (hop' : TmemOp X h n j') :
    j = j' := by
  rcases Nat.lt_trichotomy j j' with hl | he | hl
  · have := tmemOps_lt_of_lt hop hl
    rw [hop'.2] at this
    omega
  · exact he
  · have := tmemOps_lt_of_lt hop' hl
    rw [hop.2] at this
    omega

/-- Earlier operations are earlier events. -/
theorem tmemOp_lt {h m n j j' : Nat} (hop : TmemOp X h m j) (hop' : TmemOp X h n j') (hmn : m < n) :
    j < j' := by
  rcases Nat.lt_or_ge j j' with hl | hl
  · exact hl
  · rcases Nat.eq_or_lt_of_le hl with he | hl
    · subst he
      have := hop.2.symm.trans hop'.2
      omega
    · have := tmemOps_lt_of_lt hop' hl
      rw [hop.2] at this
      omega

/-- A thread that has made more than `n` operations has made its `n`-th. -/
theorem tmemOp_exists {h n : Nat} (hn : n < tmemOps (X.tr h)) : ∃ j, TmemOp X h n j := by
  obtain ⟨j, x, hx, hp, hc⟩ := MbarRing.Slot.exists_nth_countP isTmemOp (xs := X.tr h) (c := n) hn
  obtain ⟨pc, grp, dst, act, rfl⟩ := tmemOp_resource hp
  exact ⟨j, ⟨_, _, _, _, hx⟩, hc⟩

/-- The shape of a thread's `n`-th operation. -/
theorem tmemOp_shape (ht : TmemWarpOps L X w) {h n j : Nat} (hh : h < L.threads)
    (hop : TmemOp X h n j) : h % L.block / 32 = w ∧
      ∃ pc dst act, X.get (h, j) = some ⟨pc, .tc (.resource .two dst act)⟩ ∧ TmemShape n act := by
  obtain ⟨⟨pc, grp, dst, act, he⟩, rfl⟩ := hop
  obtain ⟨h0, rfl, hs⟩ := ht.event hh he
  exact ⟨h0, pc, dst, act, he, hs⟩

/-- Lane `ℓ` of warp `w` of the CTA `key + s`. -/
def pairLane (L : Launch) (w key s ℓ : Nat) : Nat := (key + s) * L.block + w * 32 + ℓ

theorem pairLane_div_mod (ht : TmemWarpOps L X w) {key s ℓ : Nat} (hℓ : ℓ < 32) :
    pairLane L w key s ℓ / L.block = key + s ∧ pairLane L w key s ℓ % L.block = w * 32 + ℓ := by
  have hwb := ht.warp_lt
  have hlt : w * 32 + ℓ < L.block := by omega
  have e : pairLane L w key s ℓ = L.block * (key + s) + (w * 32 + ℓ) := by
    simp only [pairLane]; ring
  rw [e, Nat.mul_add_div (by omega), Nat.mul_add_mod, Nat.div_eq_of_lt hlt, Nat.mod_eq_of_lt hlt]
  simp

theorem pairLane_lt (ht : TmemWarpOps L X w) {key s ℓ : Nat} (hk : key + 1 < L.grid)
    (hs : s < 2) (hℓ : ℓ < 32) : pairLane L w key s ℓ < L.threads := by
  have hwb := ht.warp_lt
  simp only [pairLane, Launch.threads]
  have : key + s + 1 ≤ L.grid := by omega
  nlinarith

theorem pairLane_inj (ht : TmemWarpOps L X w) {a b s s' ℓ ℓ' : Nat} (hℓ : ℓ < 32)
    (hℓ' : ℓ' < 32) (h : pairLane L w a s ℓ = pairLane L w b s' ℓ') : a + s = b + s' ∧ ℓ = ℓ' := by
  have h1 := pairLane_div_mod ht (key := a) (s := s) hℓ
  have h2 := pairLane_div_mod ht (key := b) (s := s') hℓ'
  rw [h] at h1
  exact ⟨h1.1.symm.trans h2.1, by omega⟩

/-- A thread of warp `w` of a CTA of the pair is one of its lanes. -/
theorem pairLane_of {h key : Nat} (hk : key % 2 = 0)
    (hc : h / L.block / 2 = key / 2) (hw : h % L.block / 32 = w) :
    ∃ s ℓ, s < 2 ∧ ℓ < 32 ∧ h = pairLane L w key s ℓ := by
  refine ⟨h / L.block % 2, h % L.block % 32, by omega, by omega, ?_⟩
  simp only [pairLane]
  have e1 := Nat.div_add_mod h L.block
  have e2 := Nat.div_add_mod (h % L.block) 32
  have h2 : key + h / L.block % 2 = h / L.block := by omega
  rw [h2, Nat.mul_comm, ← hw]
  omega

/-- The lanes of one side are one warp. -/
theorem pairLane_sameWarp (ht : TmemWarpOps L X w) {key s ℓ ℓ' : Nat} (hk : key + 1 < L.grid)
    (hs : s < 2) (hℓ : ℓ < 32) (hℓ' : ℓ' < 32) :
    SameWarp L (pairLane L w key s ℓ) (pairLane L w key s ℓ') := by
  have h1 := pairLane_div_mod ht (key := key) (s := s) hℓ
  have h2 := pairLane_div_mod ht (key := key) (s := s) hℓ'
  refine ⟨⟨pairLane_lt ht hk hs hℓ, pairLane_lt ht hk hs hℓ', by rw [h1.1, h2.1]⟩, ?_⟩
  rw [h1.2, h2.2]
  omega

/-- The lane events of a warp request of warp `w`. -/
theorem event_pairLane {q : WarpRequest} {key s : Nat} (hc : q.cta = key + s) (hw : q.warp = w)
    (ℓ : Fin 32) : q.event L ℓ = (pairLane L w key s ℓ, q.indices ℓ) := by
  simp [WarpRequest.event, pairLane, hc, hw]

/-- The grid of a two-CTA cluster launch is even. -/
theorem grid_even (ht : TmemWarpOps L X w) : L.grid % 2 = 0 := by
  have h := ht.launch.2
  rw [ht.cluster] at h
  exact h

/-- **A valid warp request makes the `n`-th operation of the 32 lanes of warp `w` of its CTA**,
for one `n`, of its shape. -/
theorem warp_shape (ht : TmemWarpOps L X w) {q : WarpRequest}
    {grp : CtaGroup} (hv : q.Valid L X grp) :
    ∃ key s n, key % 2 = 0 ∧ s < 2 ∧ key + 1 < L.grid ∧ q.cta = key + s ∧ q.warp = w ∧
      grp = .two ∧ n < 3 ∧ TmemShape n q.request ∧
      ∀ ℓ : Fin 32, TmemOp X (pairLane L w key s ℓ) n (q.indices ℓ) := by
  have hgr := grid_even ht
  have hlev := hv.2.2.1
  obtain ⟨-, hl1, hl2⟩ := WarpRequest.event_props hv 0
  obtain ⟨h0, hgrp, hs0⟩ := ht.event hl2 (hlev 0)
  have hwl : q.warp = w := by rw [← hl1]; exact h0
  have hcta := hv.1
  have hord : ∀ ℓ, tmemOps ((X.tr (q.event L ℓ).1).take (q.event L ℓ).2) = actIdx q.request := by
    intro ℓ
    obtain ⟨-, -, hl2'⟩ := WarpRequest.event_props hv ℓ
    exact (actIdx_of_shape (ht.event hl2' (hlev ℓ)).2.2).symm
  have hn0 : tmemOps ((X.tr (q.event L 0).1).take (q.event L 0).2) = actIdx q.request := hord 0
  refine ⟨q.cta - q.cta % 2, q.cta % 2, actIdx q.request, by omega, by omega, by omega, by omega,
    hwl, hgrp, by rw [← hn0]; exact lt_of_tmemShape hs0, by rw [← hn0]; exact hs0, fun ℓ => ?_⟩
  have el := event_pairLane (L := L) (key := q.cta - q.cta % 2) (s := q.cta % 2) (by omega) hwl ℓ
  refine ⟨?_, ?_⟩
  · rw [← el]; exact ⟨_, _, _, _, hlev ℓ⟩
  · have := hord ℓ; rw [el] at this; exact this

/-- **A record of a CTA's history makes the `n`-th operation of warp `w` of that CTA**, for one
`n`. -/
theorem record_shape (hX : Consistent L K A mem0 X) (ht : TmemWarpOps L X w) {c : Nat}
    {x : Requests} (hx : x ∈ X.tmemHistory c) :
    ∃ key s n, key % 2 = 0 ∧ s < 2 ∧ key + 1 < L.grid ∧ c = key + s ∧ x.own.cta = c ∧
      x.own.warp = w ∧ x.group = .two ∧ n < 3 ∧ TmemShape n x.own.request ∧
      ∀ ℓ : Fin 32, TmemOp X (pairLane L w key s ℓ) n (x.own.indices ℓ) := by
  obtain ⟨hval, hk, -⟩ := hX.tmemPair.1 c
  have hc := hk x hx
  obtain ⟨key, s, n, hk2, hs, hk1, hxc, hw, hg, hn, hsh, hall⟩ :=
    warp_shape ht (hval x hx).2.2
  exact ⟨key, s, n, hk2, hs, hk1, hc ▸ hxc, hc, hw, hg, hn, hsh, hall⟩

/-- **A pairing pairs the `n`-th operations of warp `w` of the two CTAs of a pair**, for one
`n`. -/
theorem pairing_shape (hX : Consistent L K A mem0 X) (ht : TmemWarpOps L X w)
    {q : WarpRequest × WarpRequest} (hq : q ∈ X.tmemPairing) :
    ∃ key n, key % 2 = 0 ∧ key + 1 < L.grid ∧ q.1.cta = key ∧ q.2.cta = key + 1 ∧
      q.1.warp = w ∧ q.2.warp = w ∧ n < 3 ∧
      ∀ ℓ : Fin 32, TmemOp X (pairLane L w key 0 ℓ) n (q.1.indices ℓ) ∧
        TmemOp X (pairLane L w key 1 ℓ) n (q.2.indices ℓ) := by
  have hcl := ht.cluster
  obtain ⟨-, hv1, hv2, ⟨⟨-, -, hclu⟩, -⟩, hne, hrank, hcomp⟩ := (hX.tmemPair.2.1 q hq).1
  obtain ⟨k1, s1, n1, hk1, hs1, hg1, hc1, hw1, -, hn1, hsh1, hall1⟩ := warp_shape ht hv1
  obtain ⟨k2, s2, n2, hk2, hs2, hg2, hc2, hw2, -, -, hsh2, hall2⟩ := warp_shape ht hv2
  simp only [Launch.oneDim_clusterOfCta ht.launch.1, Launch.oneDim_rankOfCta ht.launch.1, hcl]
    at hclu hrank
  have hs1' : s1 = 0 := by omega
  have hk : k2 = k1 := by omega
  have hs2' : s2 = 1 := by omega
  subst hs1' hk hs2'
  have hn : n2 = n1 := by
    rw [← actIdx_of_shape hsh1, ← actIdx_of_shape hsh2]
    exact (actIdx_compat hcomp).symm
  subst hn
  exact ⟨k2, n2, hk1, hg1, by simpa using hc1, hc2, hw1, hw2, hn1, fun ℓ => ⟨hall1 ℓ, hall2 ℓ⟩⟩

/-- A covered event is a participant of a pairing: the operations are all of cta_group::2. -/
theorem covered_pairing (hX : Consistent L K A mem0 X) (ht : TmemWarpOps L X w) {i : EvId}
    (hc : Covered L X i) :
    ∃ q ∈ X.tmemPairing, Participates L q.1 i ∨ Participates L q.2 i := by
  obtain ⟨ws, ⟨c, x, hx, hg, rfl⟩ | ⟨q, hq, rfl⟩, v, hv, hp⟩ := hc
  · obtain ⟨-, -, -, -, -, -, -, -, -, hg2, -⟩ := record_shape hX ht hx
    rw [hg] at hg2
    cases hg2
  · refine ⟨q, hq, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · exact .inl hp
    · exact .inr hp

/-- **The `n`-th operations of a pair are covered together.** -/
theorem covered_all (hX : Consistent L K A mem0 X) (ht : TmemWarpOps L X w)
    {key s ℓ s' ℓ' n j j' : Nat} (hkey : key % 2 = 0) (hs : s < 2) (hℓ : ℓ < 32) (hs' : s' < 2)
    (hℓ' : ℓ' < 32) (hop : TmemOp X (pairLane L w key s ℓ) n j)
    (hcov : Covered L X (pairLane L w key s ℓ, j))
    (hop' : TmemOp X (pairLane L w key s' ℓ') n j') :
    Covered L X (pairLane L w key s' ℓ', j') := by
  obtain ⟨q, hq, hp⟩ := covered_pairing hX ht hcov
  obtain ⟨k, m, hk2, -, hc1, hc2, hw1, hw2, -, hall⟩ := pairing_shape hX ht hq
  have hkm : k = key ∧ m = n := by
    rcases hp with ⟨l0, he⟩ | ⟨l0, he⟩
    · rw [event_pairLane (L := L) (key := k) (s := 0) (by simp [hc1]) hw1 l0] at he
      simp only [Prod.mk.injEq] at he
      obtain ⟨h1, h2⟩ := pairLane_inj ht l0.isLt hℓ he.1
      have hmn : m = n := by
        have := (hall l0).1.2
        rw [he.1, he.2] at this
        exact this.symm.trans hop.2
      exact ⟨by omega, hmn⟩
    · rw [event_pairLane (L := L) (key := k) (s := 1) hc2 hw2 l0] at he
      simp only [Prod.mk.injEq] at he
      obtain ⟨h1, h2⟩ := pairLane_inj ht l0.isLt hℓ he.1
      have hmn : m = n := by
        have := (hall l0).2.2
        rw [he.1, he.2] at this
        exact this.symm.trans hop.2
      exact ⟨by omega, hmn⟩
  obtain ⟨hk, hm⟩ := hkm
  subst hk hm
  refine ⟨[q.1, q.2], .inr ⟨q, hq, rfl⟩, ?_⟩
  rcases (by omega : s' = 0 ∨ s' = 1) with rfl | rfl
  · have hj := tmemOp_unique (hall ⟨ℓ', hℓ'⟩).1 hop'
    exact ⟨q.1, by simp, ⟨ℓ', hℓ'⟩,
      by rw [event_pairLane (L := L) (key := k) (s := 0) (by simp [hc1]) hw1, hj]⟩
  · have hj := tmemOp_unique (hall ⟨ℓ', hℓ'⟩).2 hop'
    exact ⟨q.2, by simp, ⟨ℓ', hℓ'⟩,
      by rw [event_pairLane (L := L) (key := k) (s := 1) hc2 hw2, hj]⟩

/-! ## The lanes of one warp make one collective instance -/

/-- The warp-collective count of event `j` of thread `h`. -/
abbrev tcCount (X : Execution) (h j : Nat) : Nat := ((X.tr h).take j).countP isTcColl

theorem tcK_of_op {h n j : Nat} (hop : TmemOp X h n j) : X.TcK (h, j) (tcCount X h j) := by
  obtain ⟨⟨pc, grp, dst, act, he⟩, -⟩ := hop
  exact ⟨⟨_, he, rfl⟩, rfl⟩

/-- An event of a lane at the collective count of another lane's `n`-th operation is its own
`n`-th operation: the collective instance names one request, whose kind fixes `n`. -/
theorem tcK_lane (ht : TmemWarpOps L X w) (htc : ¬ AlignedMismatch L K X) {h1 h2 n j1 j2 j' : Nat}
    (hw : SameWarp L h1 h2) (hop1 : TmemOp X h1 n j1) (hop2 : TmemOp X h2 n j2)
    (hk : X.TcK (h2, j') (tcCount X h1 j1)) : j' = j2 := by
  obtain ⟨⟨ev, hget, hcoll⟩, hcnt⟩ := hk
  obtain ⟨pc', kf⟩ := ev
  cases kf <;> simp only [isTcColl, Bool.false_eq_true] at hcoll
  rename_i kf
  obtain ⟨-, pc, dst, act, hget1, hs1⟩ := tmemOp_shape ht hw.1.1 hop1
  have hst : tcStatic (.resource .two dst act) = tcStatic kf := by
    by_contra hne
    apply htc
    refine ⟨.tc, .inl ((AlignedClass.divergent_tc_iff L).mpr ⟨(h1, j1), (h2, j'), _, _, _, _, _, hw,
      tcK_of_op hop1, ⟨⟨_, hget, ?_⟩, hcnt⟩, hget1, hget, .inr hne⟩)⟩
    cases kf <;> simp_all [isTcColl]
  obtain ⟨grp', dst', act', rfl⟩ : ∃ grp' dst' act', kf = .resource grp' dst' act' := by
    cases kf <;> simp_all [tcStatic]
  simp only [tcStatic, TcKind.resource.injEq] at hst
  obtain ⟨-, -, rfl⟩ := hst
  have hs' := (ht.event hw.1.2.1 hget).2.2
  have hord := (actIdx_of_shape hs1).symm.trans (actIdx_of_shape hs')
  exact tmemOp_unique ⟨⟨_, _, _, _, hget⟩, hord.symm⟩ hop2

/-- **The lanes of a warp make their `n`-th operation as one collective instance.** -/
theorem tcCount_eq (ht : TmemWarpOps L X w) (htc : ¬ AlignedMismatch L K X) {h1 h2 n j1 j2 : Nat}
    (hw : SameWarp L h1 h2) (hop1 : TmemOp X h1 n j1) (hop2 : TmemOp X h2 n j2) :
    tcCount X h1 j1 = tcCount X h2 j2 := by
  have key : ∀ {a b ja jb : Nat}, SameWarp L a b → TmemOp X a n ja → TmemOp X b n jb →
      ¬ tcCount X a ja < tcCount X b jb := by
    intro a b ja jb hab hopa hopb hlt
    have hle : tcCount X b jb ≤ (X.tr b).countP isTcColl := (List.take_sublist _ _).countP_le
    obtain ⟨j', ev, hev, hp, hc⟩ := MbarRing.Slot.exists_nth_countP isTcColl (xs := X.tr b)
      (c := tcCount X a ja) (by omega)
    have hj := tcK_lane ht htc hab hopa hopb ⟨⟨ev, hev, hp⟩, hc⟩
    subst hj
    simp only [tcCount] at hc hlt
    omega
  have h21 : SameWarp L h2 h1 := ⟨⟨hw.1.2.1, hw.1.1, hw.1.2.2.symm⟩, hw.2.symm⟩
  have := key hw hop1 hop2
  have := key h21 hop2 hop1
  omega

/-- **The lanes of a warp make their `n`-th operation with one event.** -/
theorem lanes_same_event (ht : TmemWarpOps L X w) (htc : ¬ AlignedMismatch L K X)
    {h1 h2 n j1 j2 : Nat}
    (hw : SameWarp L h1 h2) (hop1 : TmemOp X h1 n j1) (hop2 : TmemOp X h2 n j2) :
    X.get (h1, j1) = X.get (h2, j2) := by
  have hk := tcCount_eq ht htc hw hop1 hop2
  obtain ⟨-, pc, dst, act, hget1, -⟩ := tmemOp_shape ht hw.1.1 hop1
  obtain ⟨-, pc', dst', act', hget2, -⟩ := tmemOp_shape ht hw.1.2.1 hop2
  have hst :
      pc = pc' ∧ tcStatic (.resource .two dst act) = tcStatic (.resource .two dst' act') := by
    by_contra hne
    apply htc
    refine ⟨.tc, .inl ((AlignedClass.divergent_tc_iff L).mpr ⟨(h1, j1), (h2, j2), _, _, _, _, _, hw,
      tcK_of_op hop1, by rw [hk]; exact tcK_of_op hop2, hget1, hget2, ?_⟩)⟩
    by_cases hp : pc = pc'
    · exact .inr fun h => hne ⟨hp, h⟩
    · exact .inl hp
  obtain ⟨rfl, hst⟩ := hst
  simp only [tcStatic] at hst
  rw [hget1, hget2, hst]

/-! ## A ready step of a pair -/

/-- The action performing a request: an allocation at column 0. -/
def actOf : Tmem.Request → Tmem.Action
  | .alloc n => .alloc n 0
  | .dealloc b n => .dealloc b n
  | .relinquish => .relinquish

theorem actOf_request (a : Tmem.Request) : (actOf a).request = a := by cases a <;> rfl

/-- The warp request of side `s` of a pair whose lanes all made their `n`-th operation. -/
theorem side_request (ht : TmemWarpOps L X w) (htc : ¬ AlignedMismatch L K X) {key s n : Nat}
    (hk : key + 1 < L.grid) (hs : s < 2)
    (hall : ∀ ℓ : Fin 32, ∃ j, TmemOp X (pairLane L w key s ℓ) n j) :
    ∃ q : WarpRequest, q.cta = key + s ∧ q.warp = w ∧ TmemShape n q.request ∧
      q.Valid L X .two ∧ ∀ ℓ : Fin 32, TmemOp X (pairLane L w key s ℓ) n (q.indices ℓ) := by
  choose idx hidx using hall
  have hl0 := pairLane_lt ht hk hs (ℓ := 0) (by decide)
  obtain ⟨-, pc, dst, act, hget0, hs0⟩ := tmemOp_shape ht hl0 (hidx 0)
  have hwb := ht.warp_lt
  refine ⟨⟨key + s, w, idx, pc, dst, act⟩, rfl, rfl, hs0,
    ⟨by dsimp only; omega, hwb, ?_, ?_⟩, hidx⟩
  · intro ℓ
    rw [event_pairLane (L := L) (key := key) (s := s) rfl rfl ℓ]
    rw [lanes_same_event ht htc (pairLane_sameWarp ht hk hs ℓ.isLt (by decide)) (hidx ℓ)
      (hidx 0)]
    exact hget0
  · refine ⟨tcCount X (pairLane L w key s 0) (idx 0), fun ℓ => ?_⟩
    rw [event_pairLane (L := L) (key := key) (s := s) rfl rfl ℓ]
    have := tcCount_eq ht htc (pairLane_sameWarp ht hk hs (by decide) ℓ.isLt) (hidx 0) (hidx ℓ)
    have h2 := tcK_of_op (hidx ℓ)
    rw [← this] at h2
    exact h2

/-- Every operation of a valid request of the pair is a lane's operation. -/
theorem valid_lane_op {q : WarpRequest} {group : CtaGroup} (hv : q.Valid L X group) {key s : Nat}
    (hc : q.cta = key + s) (hw : q.warp = w) (ℓ : Fin 32) :
    TmemOp X (pairLane L w key s ℓ)
      (tmemOps ((X.tr (pairLane L w key s ℓ)).take (q.indices ℓ))) (q.indices ℓ) := by
  have he := hv.2.2.1 ℓ
  rw [event_pairLane hc hw ℓ] at he
  exact ⟨⟨_, _, _, _, he⟩, rfl⟩

/-- A record of a CTA of a pair is of a side of the pair. -/
theorem record_side (hX : Consistent L K A mem0 X) (ht : TmemWarpOps L X w) {key s : Nat}
    (hkey : key % 2 = 0) (hs : s < 2) {x : Requests} (hx : x ∈ X.tmemHistory (key + s)) :
    ∃ m, x.own.cta = key + s ∧ x.own.warp = w ∧ x.group = .two ∧ TmemShape m x.own.request ∧
      ∀ ℓ : Fin 32, TmemOp X (pairLane L w key s ℓ) m (x.own.indices ℓ) := by
  obtain ⟨k', s', m, hk2, hs', -, hc, hxc, hxw, hg, -, hsh, hall⟩ := record_shape hX ht hx
  have hk : k' = key := by omega
  have hss : s' = s := by omega
  subst hk hss
  exact ⟨m, hxc, hxw, hg, hsh, hall⟩

/-- **A ready record of a side.** When every lane of side `s` of the pair made its `n`-th
operation and the side's request is not recorded, its CTA's allocator can perform it. -/
theorem entry_ready (hX : Consistent L K A mem0 X) (ht : TmemWarpOps L X w) {key s n : Nat}
    (hkey : key % 2 = 0) (hs : s < 2) {q : WarpRequest} (hwc : q.cta = key + s)
    (hww : q.warp = w) (hwsh : TmemShape n q.request) (hwv : q.Valid L X .two)
    (hwi : ∀ ℓ : Fin 32, TmemOp X (pairLane L w key s ℓ) n (q.indices ℓ))
    (hnew : ∀ x ∈ X.tmemHistory (key + s), x.own ≠ q) :
    Step.EntryReady L X (key + s) ⟨q, .two, actOf q.request⟩ := by
  have hbefore : ∀ x ∈ X.tmemHistory (key + s), x.own.Before q := by
    intro x hx
    obtain ⟨m, hxc, hxw, -, -, hxall⟩ := record_side hX ht hkey hs hx
    rcases Nat.lt_trichotomy m n with h | h | h
    · exact ⟨hxc.trans hwc.symm, hxw.trans hww.symm, fun ℓ => tmemOp_lt (hxall ℓ) (hwi ℓ) h⟩
    · subst h
      exfalso
      have hxv := ((hX.tmemPair.1 _).1 x hx).2.2
      have he : x.own.event L 0 = q.event L 0 := by
        rw [event_pairLane hxc hxw 0, event_pairLane hwc hww 0, tmemOp_unique (hxall 0) (hwi 0)]
      exact hnew x hx (hxv.ext hwv he)
    · exfalso
      have hb : q.Before x.own :=
        ⟨hwc.trans hxc.symm, hww.trans hxw.symm, fun ℓ => tmemOp_lt (hwi ℓ) (hxall ℓ) h⟩
      obtain ⟨x', hx', hx'w⟩ := Tmem.Pair.recorded_of_before hX.tmemPair hX.tmemPairBlocking hwv
        ((hX.tmemPair.1 _).1 x hx).2.2 hb
      rw [hwc] at hx'
      exact hnew x' hx' hx'w
  refine ⟨⟨Launch.oneDimLaunch_clusterGridValid ht.launch, actOf_request _, hwv⟩,
    (fun h => by cases h), hnew, hwc, ?_⟩
  -- the replay is not blocked
  apply Tmem.Pair.run_append_ne_blocked (hX.tmemPair.1 _).2.2
  intro st hst
  show Tmem.perform st (actOf q.request) ≠ .blocked
  rcases n with _ | n
  · -- an allocation has no earlier operation, so the allocator is empty
    have hnil : X.tmemHistory (key + s) = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro x hx
      obtain ⟨m, hxc, hxw, -, -, hxall⟩ := record_side hX ht hkey hs hx
      have hlt := tmemOps_lt_of_lt (hxall 0) ((hbefore x hx).2.2 0)
      rw [(hwi 0).2] at hlt
      omega
    rw [hnil] at hst
    simp only [runRequests, Tmem.Outcome.done.injEq] at hst
    subst hst
    simp only [TmemShape] at hwsh
    rw [hwsh]
    exact Tmem.Pair.perform_empty_alloc 512
  · apply Tmem.Pair.perform_ne_blocked
    intro a c h
    rcases n with _ | _ | n
    · simp only [TmemShape] at hwsh; rw [hwsh] at h; cases h
    · obtain ⟨b, hb'⟩ := hwsh; rw [hb'] at h; cases h
    · exact hwsh.elim

/-- **A ready pairing.** When both CTAs' allocators performed the `n`-th requests of the pair,
none covered, and every earlier operation of the pair is covered, the requests can be paired. -/
theorem pairing_ready (hX : Consistent L K A mem0 X) (ht : TmemWarpOps L X w) {key n : Nat}
    (hkey : key % 2 = 0) (hk : key + 1 < L.grid)
    {w0 w1 : WarpRequest} (h0c : w0.cta = key + 0) (h0w : w0.warp = w)
    (h0sh : TmemShape n w0.request) (h0v : w0.Valid L X .two)
    (h0i : ∀ ℓ : Fin 32, TmemOp X (pairLane L w key 0 ℓ) n (w0.indices ℓ))
    (h1c : w1.cta = key + 1) (h1w : w1.warp = w)
    (h1sh : TmemShape n w1.request) (h1v : w1.Valid L X .two)
    (h1i : ∀ ℓ : Fin 32, TmemOp X (pairLane L w key 1 ℓ) n (w1.indices ℓ))
    (hunc : ∀ s, s < 2 → ∀ ℓ : Fin 32, ∀ j, TmemOp X (pairLane L w key s ℓ) n j →
      ¬ Covered L X (pairLane L w key s ℓ, j))
    (hdone : ∀ m, m < n → ∀ s, s < 2 → ∀ ℓ : Fin 32, ∀ j, TmemOp X (pairLane L w key s ℓ) m j →
      Covered L X (pairLane L w key s ℓ, j))
    (hr0 : ∃ x ∈ X.tmemHistory (key + 0), x.own = w0)
    (hr1 : ∃ x ∈ X.tmemHistory (key + 1), x.own = w1) :
    Step.PairingReady L X (w0, w1) := by
  have hcl := ht.cluster
  have hw0c : w0.cta = key := by simpa using h0c
  -- the participants of the pairing are uncovered
  have hpart : ∀ j, (Participates L w0 j ∨ Participates L w1 j) → ¬ Covered L X j := by
    rintro j (⟨ℓ, rfl⟩ | ⟨ℓ, rfl⟩)
    · rw [event_pairLane (L := L) (key := key) (s := 0) h0c h0w ℓ]
      exact hunc 0 (by decide) ℓ _ (h0i ℓ)
    · rw [event_pairLane (L := L) (key := key) (s := 1) h1c h1w ℓ]
      exact hunc 1 (by decide) ℓ _ (h1i ℓ)
  have hone := ht.launch.1
  refine ⟨⟨Launch.oneDimLaunch_clusterGridValid ht.launch, h0v, h1v,
    ⟨⟨by dsimp only; omega, by dsimp only; omega, ?_⟩, ?_⟩, by dsimp only; omega, ?_, ?_⟩,
    ?_, ?_, ?_, ?_, fun j hj _ => hpart j hj, ?_⟩
  · simp only [Launch.oneDim_clusterOfCta hone, hcl, hw0c, h1c]
    omega
  · simp only [Launch.ctaGroupRanks, Launch.oneDim_rankOfCta hone, hcl, hw0c, h1c, CtaGroup.size]
    simp only [List.mem_map, List.mem_range]
    exact ⟨1, by decide, by omega⟩
  · simp only [Launch.oneDim_rankOfCta hone, hcl, hw0c]
    omega
  · rcases n with _ | _ | _ | n
    · simp only [TmemShape] at h0sh h1sh
      simp [h0sh, h1sh, compatible]
    · simp only [TmemShape] at h0sh h1sh
      simp [h0sh, h1sh, compatible]
    · obtain ⟨b, hb⟩ := h0sh
      obtain ⟨b', hb'⟩ := h1sh
      simp [hb, hb', compatible]
    · exact h0sh.elim
  · obtain ⟨x, hx, hxo⟩ := hr0
    obtain ⟨-, -, -, hg, -⟩ := record_side hX ht hkey (by decide) hx
    exact ⟨x, by rw [hw0c]; simpa using hx, hxo, hg⟩
  · obtain ⟨x, hx, hxo⟩ := hr1
    obtain ⟨-, -, -, hg, -⟩ := record_side hX ht hkey (by decide) hx
    exact ⟨x, by rw [h1c]; exact hx, hxo, hg⟩
  · intro q' hq'
    refine ⟨fun he => hpart _ (.inl ⟨0, rfl⟩) ?_, fun he => hpart _ (.inr ⟨0, rfl⟩) ?_⟩
    · exact ⟨_, .inr ⟨q', hq', rfl⟩, q'.1, by simp, 0, he⟩
    · exact ⟨_, .inr ⟨q', hq', rfl⟩, q'.2, by simp, 0, he⟩
  · -- every earlier request of the two warps is covered
    intro v hv u g hu hb i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    obtain ⟨s, hs, hvc, hvw, hvi⟩ : ∃ s, s < 2 ∧ v.cta = key + s ∧ v.warp = w ∧
        ∀ ℓ : Fin 32, TmemOp X (pairLane L w key s ℓ) n (v.indices ℓ) := by
      rcases hv with rfl | rfl
      · exact ⟨0, by decide, h0c, h0w, h0i⟩
      · exact ⟨1, by decide, h1c, h1w, h1i⟩
    have huc : u.cta = key + s := hb.1.trans hvc
    have huw : u.warp = w := hb.2.1.trans hvw
    obtain ⟨ℓ, rfl⟩ := hi
    have hop := valid_lane_op hu huc huw ℓ
    have hlt := tmemOps_lt_of_lt hop (hb.2.2 ℓ)
    rw [(hvi ℓ).2] at hlt
    rw [event_pairLane huc huw ℓ]
    exact hdone _ hlt s hs ℓ _ hop
  · -- a waiting participant is its thread's last event, so no later record orders it
    intro j hj hm cta' j' hp
    have hlast := Step.pending_is_last hX hm (hpart j hj)
    obtain ⟨k, l, x, y, hx, hy, hkl, ⟨ℓ, rfl⟩, -⟩ := hp
    have hord := hX.object.tmemOrdered hX.tmemPair cta'
    obtain ⟨hk', hxk⟩ := List.getElem?_eq_some_iff.mp hx
    obtain ⟨hl', hyl⟩ := List.getElem?_eq_some_iff.mp hy
    have ho := List.pairwise_iff_getElem.mp hord k l hk' hl' hkl
    rw [hxk, hyl] at ho
    have hxm := List.mem_of_getElem? hx
    have hym := List.mem_of_getElem? hy
    obtain ⟨-, -, -, -, -, -, -, hxc, hxw, -⟩ := record_shape hX ht hxm
    obtain ⟨-, -, -, -, -, -, -, hyc, hyw, -⟩ := record_shape hX ht hym
    have hb := ho (hxc.trans hyc.symm) (hxw.trans hyw.symm)
    have hlt := hb.2.2 ℓ
    have hyv := ((hX.tmemPair.1 cta').1 y hym).2.2
    have hget := len_of_get (hyv.2.2.1 ℓ)
    have hth : (y.own.event L ℓ).1 = (x.own.event L ℓ).1 := by
      simp [WarpRequest.event, hb.1, hb.2.1]
    rw [hth] at hget
    simp only [WarpRequest.event] at hlast hget hlt
    omega

/-- **A ready step of a pair.** When every lane of the pair made its `n`-th operation, none
covered, and every earlier operation of the pair is covered, a CTA's allocator can perform its
warp's request, or both performed them and the requests can be paired. -/
theorem pair_ready (hX : Consistent L K A mem0 X) (ht : TmemWarpOps L X w)
    (htc : ¬ AlignedMismatch L K X) {key n : Nat} (hkey : key % 2 = 0) (hk : key + 1 < L.grid)
    (hall : ∀ s, s < 2 → ∀ ℓ : Fin 32, ∃ j, TmemOp X (pairLane L w key s ℓ) n j ∧
      ¬ Covered L X (pairLane L w key s ℓ, j))
    (hdone : ∀ m, m < n → ∀ s, s < 2 → ∀ ℓ : Fin 32, ∀ j, TmemOp X (pairLane L w key s ℓ) m j →
      Covered L X (pairLane L w key s ℓ, j)) :
    (∃ c r, Step.EntryReady L X c r) ∨ ∃ q, Step.PairingReady L X q := by
  obtain ⟨w0, h0c, h0w, h0sh, h0v, h0i⟩ := side_request ht htc hk (by decide : 0 < 2)
    (fun ℓ => (hall 0 (by decide) ℓ).imp fun _ h => h.1)
  obtain ⟨w1, h1c, h1w, h1sh, h1v, h1i⟩ := side_request ht htc hk (by decide : 1 < 2)
    (fun ℓ => (hall 1 (by decide) ℓ).imp fun _ h => h.1)
  have hunc : ∀ s, s < 2 → ∀ ℓ : Fin 32, ∀ j, TmemOp X (pairLane L w key s ℓ) n j →
      ¬ Covered L X (pairLane L w key s ℓ, j) := by
    intro s hs ℓ j hop hc
    obtain ⟨j', hop', hn'⟩ := hall s hs ℓ
    rw [tmemOp_unique hop hop'] at hc
    exact hn' hc
  by_cases hr0 : ∃ x ∈ X.tmemHistory (key + 0), x.own = w0
  · by_cases hr1 : ∃ x ∈ X.tmemHistory (key + 1), x.own = w1
    · exact .inr ⟨_, pairing_ready hX ht hkey hk h0c h0w h0sh h0v h0i h1c h1w h1sh h1v h1i hunc
        hdone hr0 hr1⟩
    · refine .inl ⟨_, _, entry_ready hX ht hkey (by decide) h1c h1w h1sh h1v h1i
        fun x hx hxo => hr1 ⟨x, hx, hxo⟩⟩
  · refine .inl ⟨_, _, entry_ready hX ht hkey (by decide) h0c h0w h0sh h0v h0i
      fun x hx hxo => hr0 ⟨x, hx, hxo⟩⟩

end
end PTX.Tmem.Pair
