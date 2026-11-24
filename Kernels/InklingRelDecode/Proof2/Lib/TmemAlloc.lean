-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Tmem.PairProtocol
public import Lemmas.Tmem.TmemRun
public import Lemmas.Kernel.Frame

@[expose] public section

/-!
# The Tensor Memory allocation of a CTA (`cta_group::1`)

The kernel's Tensor Memory resource operations are `cta_group::1` and made by one warp of each CTA
(warp 0: `@%p3` is `tid < 32`): each of its 32 lanes allocates all 512 columns, relinquishes the
permit and deallocates, in that order. The library's pair protocol
(`Lemmas/Tmem/PairProtocol.lean`, `Tmem.Pair.no_resource_unsafe`, `no_release_unsafe`) is for the
two-CTA `cta_group::2` case: its `TmemWarpOps` asks for group two and a two-CTA cluster. This file
is the single-CTA version of its safety half, with the same arguments: the records of a CTA's
history are the operations of warp `w`, in program order (`record_info`, `history_before`,
`history_ops`); the allocation is the history's first record, so at column 0 (`alloc_zero`); the
history replays without a fault (`Tmem.Pair.run_alloc_ok`); once every thread has exited and every
operation is complete, the allocator is empty (`Tmem.Pair.run_alloc_released`).

`Tmem1Facts` is what the thread layer supplies (the development notes, "Protocol `Tmem`"): every
resource event is warp `w`'s, in group one, and the `n`-th of its thread has the shape `n` (the
allocation of 512 columns, the relinquishment, the deallocation); a deallocation frees column 0
(the base word's read returns the zero word, `SO.BaseWordZero`); a lane of the warp exits after its
three operations.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Tmem1
open PTX PTX.Proof Tmem.Pair

noncomputable section

/-- **The resource operations of warp `w`, `cta_group::1`.** Every Tensor Memory resource
operation is made by warp `w` of its CTA, in group one, and a thread's `n`-th has the shape `n`
(`TmemShape`). -/
structure Tmem1Ops (L : Launch) (X : Execution) (w : Nat) : Prop where
  warp_lt : (w + 1) * 32 ≤ L.block
  event : ∀ {g k pc : Nat} {grp : CtaGroup} {dst : Option Loc} {act : Tmem.Request},
    g < L.threads → X.get (g, k) = some ⟨pc, .tc (.resource grp dst act)⟩ →
    g % L.block / 32 = w ∧ grp = .one ∧ TmemShape (tmemOps ((X.tr g).take k)) act

/-- **The Tensor Memory facts of warp `w`**: its operations; a deallocation frees column 0, the
column of the allocation (`alloc_zero`); a lane of warp `w` exits after its three operations. -/
structure Tmem1Facts (L : Launch) (X : Execution) (w : Nat) : Prop extends Tmem1Ops L X w where
  dealloc : ∀ {g k pc : Nat} {grp : CtaGroup} {dst : Option Loc} {a n : Nat}, g < L.threads →
    X.get (g, k) = some ⟨pc, .tc (.resource grp dst (.dealloc a n))⟩ → a = 0
  exit : ∀ {g k pc : Nat}, g < L.threads → g % L.block / 32 = w →
    X.get (g, k) = some ⟨pc, .exit⟩ → tmemOps ((X.tr g).take k) = 3

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution} {w : Nat}

/-! ## The records of a CTA's history -/

/-- The lane-0 event of a warp request of a recorded history: a paired operation of warp `w` of
its CTA, its thread's `n`-th. -/
theorem warp_info (ht : Tmem1Ops L X w) {q : WarpRequest} {grp : CtaGroup}
    (hv : q.Valid L X grp) :
    q.warp = w ∧ grp = .one ∧
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

/-- A record of CTA `cta`'s history: warp `w` of `cta`, a cta_group::1 request at its thread's
`n`-th operation, of its shape, performed by its action. -/
theorem record_info (hX : Consistent L K A mem0 X) (ht : Tmem1Ops L X w) {cta : Nat}
    {r : Requests} (hr : r ∈ X.tmemHistory cta) :
    r.own.cta = cta ∧ r.own.warp = w ∧ r.group = .one ∧ r.action.request = r.own.request ∧
      X.get (cta * L.block + w * 32, r.own.indices 0) =
        some ⟨r.own.pc, .tc (.resource .one r.own.dst r.own.request)⟩ ∧
      TmemShape (opsAt X (cta * L.block + w * 32) (r.own.indices 0)) r.own.request := by
  obtain ⟨hval, hown, -⟩ := hX.tmemPair.1 cta
  have hcta := hown r hr
  obtain ⟨-, hreq, hv⟩ := hval r hr
  obtain ⟨hw, hgrp, hle, hls⟩ := warp_info ht hv
  rw [hcta, hgrp] at hle
  rw [hcta] at hls
  exact ⟨hcta, hw, hgrp, hreq, hle, hls⟩

/-- The lane-0 thread of a record's warp is a launched thread. -/
theorem record_thread (hX : Consistent L K A mem0 X) (ht : Tmem1Ops L X w) {cta : Nat}
    {r : Requests} (hr : r ∈ X.tmemHistory cta) : cta * L.block + w * 32 < L.threads := by
  have h3 := (WarpRequest.event_props ((hX.tmemPair.1 cta).1 r hr).2.2 0).2.2
  obtain ⟨hc, hw, -⟩ := record_info hX ht hr
  simpa [WarpRequest.event, hc, hw] using h3

/-- A CTA's history is in warp `w`'s program order. -/
theorem history_before (hX : Consistent L K A mem0 X) (ht : Tmem1Ops L X w) {cta : Nat}
    {a b : Requests} (ha : a ∈ X.tmemHistory cta) (hb : b ∈ X.tmemHistory cta)
    (hab : a.own.Ordered b.own) : a.own.Before b.own := by
  obtain ⟨hca, hwa, -⟩ := record_info hX ht ha
  obtain ⟨hcb, hwb, -⟩ := record_info hX ht hb
  exact hab (hca.trans hcb.symm) (hwa.trans hwb.symm)

/-- An event of lane 0 of warp `w` of a CTA covered by a completed operation is a record of that
CTA's history: the operations are cta_group::1, so no pairing completes one. -/
theorem covered_record (hX : Consistent L K A mem0 X) (ht : Tmem1Ops L X w) {cta i : Nat}
    (hc : Covered L X (cta * L.block + w * 32, i)) :
    ∃ r ∈ X.tmemHistory cta, r.own.indices 0 = i := by
  obtain ⟨ws, hws, q, hq, lane, hl⟩ := hc
  obtain ⟨r, hr, hrw⟩ : ∃ r ∈ X.tmemHistory q.cta, r.own = q := by
    rcases hws with ⟨cta', x, hx, hg, rfl⟩ | ⟨p, hp, rfl⟩
    · rw [List.mem_singleton.mp hq]
      obtain ⟨hc', -⟩ := record_info hX ht hx
      exact ⟨x, by rw [hc']; exact hx, rfl⟩
    · exfalso
      obtain ⟨-, ⟨a, ha, -, ha2⟩, -⟩ := hX.tmemPair.2.1 p hp
      obtain ⟨-, -, hg2, -⟩ := record_info hX ht ha
      rw [hg2] at ha2
      cases ha2
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
theorem history_first (hX : Consistent L K A mem0 X) (ht : Tmem1Ops L X w) {cta : Nat}
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
theorem alloc_zero (hX : Consistent L K A mem0 X) (ht : Tmem1Ops L X w) {cta : Nat}
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

/-- A thread of warp `w` that has made an operation before an event of its trace has its first
operation recorded in its CTA's history: the operation is complete, since the thread went on. -/
theorem first_recorded (hX : Consistent L K A mem0 X) (ht : Tmem1Ops L X w) {cta j : Nat}
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
theorem record_act (hX : Consistent L K A mem0 X) (ht : Tmem1Facts L X w) {cta : Nat}
    {r : Requests} (hr : r ∈ X.tmemHistory cta) :
    r.action = opAct 0 (opsAt X (cta * L.block + w * 32) (r.own.indices 0)) := by
  have hto := ht.toTmem1Ops
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
    have h1 := ht.dealloc hT hle
    rw [ha, h1]
    rfl

/-- A CTA's history: its records' operation counts, increasing, and their actions at
column 0. -/
theorem history_ops (hX : Consistent L K A mem0 X) (ht : Tmem1Facts L X w) (cta : Nat) :
    (X.tmemHistory cta).map (·.action) =
        ((X.tmemHistory cta).map fun r => opsAt X (cta * L.block + w * 32) (r.own.indices 0)).map
          (opAct 0) ∧
      ((X.tmemHistory cta).map fun r => opsAt X (cta * L.block + w * 32) (r.own.indices 0)).Pairwise
        (· < ·) ∧
      ∀ n ∈ (X.tmemHistory cta).map fun r => opsAt X (cta * L.block + w * 32) (r.own.indices 0),
        n ≤ 2 := by
  have hto := ht.toTmem1Ops
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

/-- **No CTA's resource history faults, and no allocation follows a deallocation**
(`Safety.Protocol.tmemResource`). -/
theorem no_resource_unsafe (hX : Consistent L K A mem0 X) (ht : Tmem1Facts L X w) :
    ¬ ResourceUnsafe L X := by
  have hto := ht.toTmem1Ops
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

/-- **Once every thread has exited and every operation is complete, no allocation is live**
(`Safety.Protocol.tmemRelease`). -/
theorem no_release_unsafe (hX : Consistent L K A mem0 X) (ht : Tmem1Facts L X w) :
    ¬ ReleaseUnsafe L X := by
  have hto := ht.toTmem1Ops
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

end
end PTX.Kernels.InklingRelDecode.Proof.Tmem1
