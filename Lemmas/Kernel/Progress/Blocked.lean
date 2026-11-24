-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.Unreleased
public import Lemmas.Step.ClusterReady
public import Lemmas.Step.CtaBarNamed
public import Lemmas.Protocol.NamedBarArrive
public import Lemmas.Tmem.TmemResourceReady
public import Lemmas.Tcgen05.TcCollectiveOrdinaryWaiting

@[expose] public section

/-! # The blocking part of a thread's last event

A pending thread whose last event blocks and is not ready (`Descent.unreleased_cases`, DEP-ORDER)
has one blocking part (`thread_cases`), by the kind of that event: a cluster-barrier operation
that no record holds (`ClusterWait`), a `setmaxnreg` whose warp's lanes have not all requested
(`RegWait`), a paired Tensor Memory operation (`TmemWait`), a `bar.sync` whose generation is not
done (`BarWait`), a warp-collective `tcgen05` load, store or wait some lane of its warp has not
reached (`TcWait`), a `bar.arrive` without its record (`ArriveWait`) or a bulk-group wait
(`BulkWait`). A `cp.async.wait_group` is excluded by a premise. Each class steps by its own
argument. A paired Tensor Memory operation that cannot return either cannot return yet
(`TmemOpen`) or is an allocation that waits only for its warp's address store (`PublishWait`,
`tmemWait_cases`). -/

namespace PTX.Sched

open PTX

noncomputable section

/-- The last event of thread `g` is not ready. -/
def LastNotReady (L : Launch) (X : Execution) (g : Nat) : Prop :=
  ¬ Ready L X (g, (X.tr g).length - 1)

/-- The last event of thread `g`: a cluster-barrier operation that no record holds. -/
def ClusterWait (L : Launch) (X : Execution) (g : Nat) : Prop :=
  ∃ pc op, X.get (g, (X.tr g).length - 1) = some ⟨pc, .cluster op⟩ ∧
    ¬ ClusterRecorded L X (g, (X.tr g).length - 1)

/-- The last event of thread `g`: a register request whose warp's lanes have not all requested. -/
def RegWait (L : Launch) (X : Execution) (g : Nat) : Prop :=
  ∃ pc inc n inst, SetMaxNReg.Request X (g, (X.tr g).length - 1) pc inc n inst ∧
    LastNotReady L X g

/-- The last event of thread `g`: a paired Tensor Memory operation that cannot yet return. -/
def TmemWait (L : Launch) (X : Execution) (g : Nat) : Prop :=
  ∃ pc grp dst act, X.get (g, (X.tr g).length - 1) = some ⟨pc, .tc (.resource grp dst act)⟩ ∧
    LastNotReady L X g

/-- The last event of thread `g`: a named barrier whose generation is not done. -/
def BarWait (L : Launch) (X : Execution) (g : Nat) : Prop :=
  ∃ id cnt pc, 0 < (X.tr g).length ∧ X.IsBarrier (g, (X.tr g).length - 1) id cnt pc ∧
    ¬ ∃ key, CtaBarK L X (g, (X.tr g).length - 1) key ∧ CtaBarDone L X (g / L.block) key

/-- The last event of thread `g`: its `k`-th warp-collective `tcgen05` load, store or wait, which
some lane of its warp has not reached. -/
def TcWait (L : Launch) (X : Execution) (g : Nat) : Prop :=
  ∃ k, 0 < (X.tr g).length ∧ X.TcK (g, (X.tr g).length - 1) k ∧
    ¬ ∀ h, h < L.threads → SameWarp L g h → ∃ j, X.TcK (h, j) k

/-- The last event of thread `g`: a `bar.arrive` that no record holds. -/
def ArriveWait (L : Launch) (X : Execution) (g : Nat) : Prop :=
  ∃ pc id cnt, X.get (g, (X.tr g).length - 1) = some ⟨pc, .bar id cnt .arrive⟩ ∧
    (g, (X.tr g).length - 1) ∉ (X.barriers (g / L.block)).flatMap CtaBarrier.Record.refs

/-- The last event of thread `g`: a bulk-group wait that is not ready. -/
def BulkWait (L : Launch) (X : Execution) (g : Nat) : Prop :=
  ∃ pc mode n, X.get (g, (X.tr g).length - 1) = some ⟨pc, .bulkWait mode n⟩ ∧
    LastNotReady L X g

/-- A lane of the warp of a thread is a thread. -/
theorem warpLane_lt {L : Launch} {g l : Nat} (hg : g < L.threads) (hl : l < warpSize L g) :
    warpLane L g l < L.threads := by
  have hb : 0 < L.block := by
    rcases Nat.eq_zero_or_pos L.block with h | h
    · simp [Launch.threads, h] at hg
    · exact h
  have hc : g / L.block < L.grid := (Nat.div_lt_iff_lt_mul hb).mpr hg
  have hm : (g / L.block + 1) * L.block ≤ L.grid * L.block := Nat.mul_le_mul_right _ hc
  have e1 := Nat.div_add_mod' g L.block
  have e2 := Nat.div_add_mod (g % L.block) 32
  unfold warpSize at hl
  rw [lt_min_iff] at hl
  unfold warpLane laneOf
  unfold Launch.threads at hg ⊢
  rw [Nat.add_mul, Nat.one_mul] at hm
  omega

/-- A warp-collective `tcgen05` event that every lane of its warp has reached is ready, unless
it is a paired Tensor Memory operation, whose needs include the allocator's. -/
theorem tc_ready_of_done {L : Launch} {X : Execution} {e : EvId} {k pc : Nat} {t : TcKind}
    (hlt : e.1 < L.threads) (he : X.get e = some ⟨pc, .tc t⟩)
    (ht : ∀ grp dst act, t ≠ .resource grp dst act) (hk : X.TcK e k)
    (hd : ∀ h, h < L.threads → SameWarp L e.1 h → ∃ j, X.TcK (h, j) k) : Ready L X e := by
  have hn : Needs L X e = tcNeeds L X e := by
    obtain ⟨ev, hev, hc⟩ := hk.1
    rw [he] at hev
    cases hev
    unfold Needs
    rw [he]
    cases t <;> first | exact (ht _ _ _ rfl).elim | rfl | simp [isTcColl] at hc
  intro n hm
  rw [hn] at hm
  obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hm
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hh
  have hlt' := warpLane_lt hlt (List.mem_range.mp hl)
  have hsw := sameWarp_of_mem_warpLanes hh hlt' hlt
  obtain ⟨j, hj⟩ := hd _ hlt' (sameWarp_symm hsw)
  obtain ⟨ev, hev, -⟩ := hj.1
  exact ⟨.thread (warpLane L e.1 l, j), ⟨_, hev⟩, j, rfl, hk.2 ▸ hj⟩

variable {K : Kernel} {A : List Assumption} {mem0 : Mem0} {L : Launch} in
/-- **The blocking part of a thread's last event**, for a thread whose last event is not a
`cp.async.wait_group` (`hna`). -/
theorem thread_cases {X : Execution} (hX : Consistent L K A mem0 X) {g : Nat} (hg : g < L.threads)
    (hna : ∀ pc n, X.get (g, (X.tr g).length - 1) ≠ some ⟨pc, .asyncWait n⟩)
    (h : ¬ Step.Released L X g) :
    ClusterWait L X g ∨ RegWait L X g ∨ TmemWait L X g ∨ BarWait L X g ∨ TcWait L X g ∨
      ArriveWait L X g ∨ BulkWait L X g := by
  obtain ⟨pc, k, hq, hk, hr⟩ := Descent.unreleased_cases h
  have hlen : 0 < (X.tr g).length := by
    have := len_of_get hq
    simp only at this
    omega
  cases k with
  | cluster op =>
    exact .inl ⟨pc, op, hq, fun hrec => hr (Step.ready_of_recorded hX.cluster hq hrec)⟩
  | setMaxReg inc n inst => exact .inr (.inl ⟨pc, inc, n, inst, hq, hr⟩)
  | bar id cnt mode =>
    cases mode with
    | sync =>
      exact .inr (.inr (.inr (.inl ⟨id, cnt, pc, hlen, hq, fun ⟨key, hkey, hd⟩ =>
        hr (NamedBar.ready_of_released hX.ctaBar hq hkey hd)⟩)))
    | arrive =>
      refine .inr (.inr (.inr (.inr (.inr (.inl ⟨pc, id, cnt, hq, fun hrec => ?_⟩)))))
      obtain ⟨gen, hkey⟩ := NamedBar.recorded_arrivalK hX hq hg hrec
      exact hr (NamedBar.ready_of_arrivalK hX.ctaBar hq hkey)
  | bulkWait mode n =>
    exact .inr (.inr (.inr (.inr (.inr (.inr ⟨pc, mode, n, hq, hr⟩)))))
  | asyncWait n => exact (hna pc n hq).elim
  | tc t =>
    cases t with
    | resource grp dst act =>
      exact .inr (.inr (.inl ⟨pc, grp, dst, act, hq, hr⟩))
    | _ =>
      first
        | simp [Kind.resume, TcKind.resume] at hk; done
        | have htk : X.TcK (g, (X.tr g).length - 1) _ := ⟨⟨_, hq, rfl⟩, rfl⟩
          exact .inr (.inr (.inr (.inr (.inl ⟨_, hlen, htk, fun hd =>
            hr (tc_ready_of_done hg hq (fun _ _ _ he => by cases he) htk hd)⟩))))
  | _ => simp [Kind.resume] at hk

/-! ### Paired Tensor Memory operations -/

/-- The last event of thread `g`: a paired Tensor Memory operation whose return is not ready
(`Tmem.Pair.ReturnReady`). -/
def TmemOpen (L : Launch) (X : Execution) (g : Nat) : Prop :=
  ∃ pc grp dst act, X.get (g, (X.tr g).length - 1) = some ⟨pc, .tc (.resource grp dst act)⟩ ∧
    ¬ Tmem.Pair.ReturnReady L X (g, (X.tr g).length - 1)

/-- The last event of thread `g`: an allocation whose return waits only for its warp's result:
the operation can return (`Tmem.Pair.ReturnReady`), but the local leader has not stored the
allocated address (EXT-TMEM-ALLOC-RESULT-ORDER, `Tmem.Pair.allocResultNeeds`). -/
def PublishWait (L : Launch) (X : Execution) (g : Nat) : Prop :=
  ∃ pc grp dst n, X.get (g, (X.tr g).length - 1) = some ⟨pc, .tc (.resource grp dst (.alloc n))⟩ ∧
    Tmem.Pair.ReturnReady L X (g, (X.tr g).length - 1) ∧
    ¬ ∃ store out, Tmem.Pair.AllocResult L X store (g, (X.tr g).length - 1) out

variable {K : Kernel} {A : List Assumption} {mem0 : Mem0} {L : Launch} in
/-- **A paired Tensor Memory operation that cannot return** cannot return yet (`TmemOpen`), or is
an allocation whose return waits only for its warp's address store (`PublishWait`): an operation
that can return and is not an allocation is ready. -/
theorem tmemWait_cases {X : Execution} (hX : Consistent L K A mem0 X) {g : Nat}
    (h : TmemWait L X g) : TmemOpen L X g ∨ PublishWait L X g := by
  obtain ⟨pc, grp, dst, act, hq, hr⟩ := h
  by_cases hrr : Tmem.Pair.ReturnReady L X (g, (X.tr g).length - 1)
  · cases act with
    | alloc n =>
      exact .inr ⟨pc, grp, dst, n, hq, hrr, fun hres =>
        hr (Tmem.Pair.ReturnReady.ready hX.tmemPair hq hrr fun _ _ _ => hres)⟩
    | _ =>
      exact (hr (Tmem.Pair.ReturnReady.ready hX.tmemPair hq hrr fun _ h _ => by cases h)).elim
  · exact .inl ⟨pc, grp, dst, act, hq, hrr⟩

end

end PTX.Sched
