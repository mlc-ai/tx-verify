-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Tmem.AllocResult
public import Lemmas.Tmem.TmemPairHistory

@[expose] public section

namespace PTX.Tmem.Pair

variable {L : Launch} {X Y : Execution}

/-- An actual allocating warp and its result store provide a handoff witness
for every participating lane of the local CTA. -/
theorem AllocResult.of_warpRequest {w : WarpRequest} {group : CtaGroup}
    {dst : Loc} {n : Nat} {bytes : List Byte} (hw : w.Valid L X group)
    (hn : w.request = .alloc n) (hd : w.dst = some dst)
    (hs : dst.space = .shared) (hc : dst.cta = w.cta)
    (hstore : X.get ((w.event L 0).1, (w.event L 0).2 + 1) =
      some ⟨w.pc, .wr { loc := dst, size := 4 } bytes⟩) (lane : Fin 32) :
    AllocResult L X ((w.event L 0).1, (w.event L 0).2 + 1) (w.event L lane) dst := by
  have hleader : laneOf L (w.event L 0).1 = 0 := by
    have hlt : w.warp * 32 < L.block := by have := hw.2.1; omega
    simp only [laneOf, WarpRequest.event, Fin.val_zero, Nat.add_zero]
    rw [Nat.mul_comm w.cta, Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]
    simp
  obtain ⟨k, hk⟩ := hw.2.2.2
  have he : ∀ l, X.get (w.event L l) =
      some ⟨w.pc, .tc (.resource group (some dst) (.alloc n))⟩ := by
    simpa only [hn, hd] using hw.2.2.1
  exact ⟨WarpRequest.event_sameWarp hw 0 lane, hleader, hs,
    hc.trans (WarpRequest.event_props hw lane).1.symm, (w.event L 0).2,
    w.pc, group, n, k, bytes, rfl, he 0, he lane, hk 0, hk lane, hstore⟩

theorem AllocResult.mono_trace {store i : EvId} {dst : Loc}
    (h : AllocResult L X store i dst) (htr : ∀ g, X.tr g <+: Y.tr g) :
    AllocResult L Y store i dst := by
  have get_old {e : EvId} {ev : Event} (he : X.get e = some ev) : Y.get e = some ev := by
    obtain ⟨suffix, hs⟩ := htr e.1
    unfold Execution.get at he ⊢
    rw [← hs, List.getElem?_append_left (PTX.len_of_get he)]
    exact he
  have tc_old {e : EvId} {k : Nat} (hk : X.TcK e k) : Y.TcK e k := by
    obtain ⟨⟨ev, he, hc⟩, hn⟩ := hk
    refine ⟨⟨ev, get_old he, hc⟩, ?_⟩
    obtain ⟨suffix, hs⟩ := htr e.1
    rwa [← hs, List.take_append_of_le_length (PTX.len_of_get he).le]
  obtain ⟨hw, hl, hs, hc, j, site, group, n, k, bytes, hj, ha, hi, hk, hki, hb⟩ := h
  exact ⟨hw, hl, hs, hc, j, site, group, n, k, bytes, hj, get_old ha, get_old hi,
    tc_old hk, tc_old hki, get_old hb⟩

theorem AllocResult.mono {store i : EvId} {dst : Loc}
    (h : AllocResult L X store i dst) (hle : X.le Y) : AllocResult L Y store i dst :=
  h.mono_trace hle.1

private theorem get_of_prefix (htr : ∀ g, X.tr g <+: Y.tr g) {e : EvId} {ev : Event}
    (hi : e.2 < (X.tr e.1).length) (he : Y.get e = some ev) : X.get e = some ev := by
  obtain ⟨suffix, hs⟩ := htr e.1
  unfold Execution.get at he
  rw [← hs, List.getElem?_append_left hi] at he
  exact he

private theorem tcK_of_prefix (htr : ∀ g, X.tr g <+: Y.tr g) {e : EvId} {k : Nat}
    (hi : e.2 < (X.tr e.1).length) (hk : Y.TcK e k) : X.TcK e k := by
  obtain ⟨⟨ev, he, hc⟩, hn⟩ := hk
  refine ⟨⟨ev, get_of_prefix htr hi he, hc⟩, ?_⟩
  obtain ⟨suffix, hs⟩ := htr e.1
  rw [← hs, List.take_append_of_le_length hi.le] at hn
  exact hn

/-- The result link is determined by the two endpoint traces through those events. -/
theorem AllocResult.of_tracePrefix {store i : EvId} {dst : Loc}
    (h : AllocResult L Y store i dst) (htr : ∀ g, X.tr g <+: Y.tr g)
    (hstore : store.2 < (X.tr store.1).length) (hi : i.2 < (X.tr i.1).length) :
    AllocResult L X store i dst := by
  obtain ⟨hw, hl, hs, hc, j, site, group, n, k, bytes, hj, ha, he, hk, hki, hb⟩ := h
  have hleader : j < (X.tr store.1).length := by omega
  exact ⟨hw, hl, hs, hc, j, site, group, n, k, bytes, hj, get_of_prefix htr hleader ha,
    get_of_prefix htr hi he, tcK_of_prefix htr hleader hk, tcK_of_prefix htr hi hki,
    get_of_prefix htr hstore hb⟩

theorem AllocResult.of_prefix {store i : EvId} {dst : Loc}
    (h : AllocResult L Y store i dst) (hle : X.le Y)
    (hstore : store.2 < (X.tr store.1).length) (hi : i.2 < (X.tr i.1).length) :
    AllocResult L X store i dst :=
  h.of_tracePrefix hle.1 hstore hi

theorem AllocResultBefore.mono {l : Loc} {store load : EvId}
    (h : AllocResultBefore L X l store load) (hle : X.le Y) :
    AllocResultBefore L Y l store load := by
  obtain ⟨j, dst, a, bytes, hr, hj, hb, ⟨site, he⟩, hc⟩ := h
  exact ⟨j, dst, a, bytes, hr.mono hle, hj, hb, ⟨site, Execution.le_get hle he⟩, hc⟩

/-- An extension cannot introduce an allocation handoff between two existing endpoints. -/
theorem AllocResultBefore.of_prefix {l : Loc} {store load : EvId}
    (h : AllocResultBefore L Y l store load) (hle : X.le Y)
    (hstore : store.2 < (X.tr store.1).length) (hload : load.2 < (X.tr load.1).length) :
    AllocResultBefore L X l store load := by
  obtain ⟨j, dst, a, bytes, hr, hj, hb, ⟨site, he⟩, hc⟩ := h
  exact ⟨j, dst, a, bytes, hr.of_prefix hle hstore (hj.trans hload),
    hj, hb, ⟨site, get_of_prefix hle.1 hload he⟩, hc⟩

/-- The allocation-result handoff depends only on the thread traces. -/
theorem AllocResultBefore.iff_of_tr (htr : Y.tr = X.tr) {l : Loc} {store load : EvId} :
    AllocResultBefore L Y l store load ↔ AllocResultBefore L X l store load := by
  simp only [AllocResultBefore, AllocResult, Execution.TcK, Execution.Reads, Execution.get, htr]

theorem AllocResultBefore.shared {l : Loc} {store load : EvId}
    (h : AllocResultBefore L X l store load) :
    l.space = .shared ∧ l.cta = load.1 / L.block := by
  obtain ⟨_, _, _, _, ⟨_, _, hshared, hcta, _⟩, _, hb, _, _⟩ := h
  exact ⟨hb.1.trans hshared, hb.2.1.trans hcta⟩

/-- The result relation identifies the actual write and its four-byte footprint. -/
theorem AllocResult.writes {store i : EvId} {dst : Loc} (h : AllocResult L X store i dst) :
    ∃ bytes, X.Writes store { loc := dst, size := 4 } bytes := by
  obtain ⟨_, _, _, _, _, site, _, _, _, bytes, _, _, _, _, _, he⟩ := h
  exact ⟨bytes, site, he⟩

/-- A lane has at most one result store for its allocation event. -/
theorem AllocResult.unique {store store' i : EvId} {dst dst' : Loc}
    (h : AllocResult L X store i dst) (h' : AllocResult L X store' i dst') :
    store = store' := by
  obtain ⟨⟨⟨_, _, hcta⟩, hwarp⟩, hlane, _, _, j, _, _, _, k, _, hj, _, _, hk, hi, _⟩ := h
  obtain ⟨⟨⟨_, _, hcta'⟩, hwarp'⟩, hlane', _, _, j', _, _, _, k', _, hj', _, _, hk', hi', _⟩ := h'
  have hrank : store.1 % L.block = store'.1 % L.block := by
    have hdiv := Nat.div_add_mod (store.1 % L.block) 32
    have hdiv' := Nat.div_add_mod (store'.1 % L.block) 32
    unfold laneOf at hlane hlane'
    rw [hlane, hwarp, ← hwarp', ← hlane', hdiv'] at hdiv
    exact hdiv.symm
  have ht : store.1 = store'.1 := by
    have hdiv := Nat.div_add_mod store.1 L.block
    have hdiv' := Nat.div_add_mod store'.1 L.block
    rw [hcta, ← hcta', hrank, hdiv'] at hdiv
    exact hdiv.symm
  have hord : k = k' := hi.2.symm.trans hi'.2
  rw [hord, ht] at hk
  have hindex := hk.unique hk'
  exact Prod.ext ht (hj.trans (congrArg (· + 1) hindex) |>.trans hj'.symm)

end PTX.Tmem.Pair
