-- SPDX-License-Identifier: Apache-2.0
module

import Lemmas.Kernel.FrameU

public import Kernels.TmlFa4Fwd.Proof.Common.Roles
public import Kernels.TmlFa4Fwd.Proof.SmWarp.Export.Follow
public import Kernels.TmlFa4Fwd.Proof.Mma.Export.TmemTrace
public import Lemmas.Tmem.Tmem1Protocol
import Kernels.TmlFa4Fwd.Flow.Code
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Kernels.TmlFa4Fwd.Proof.Mma.Export.SafePre
import Kernels.TmlFa4Fwd.Proof.Mma.Warp
import Kernels.TmlFa4Fwd.Proof.Top.JRStub
import Kernels.TmlFa4Fwd.Proof.Protocol.KV.Obj
import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.Init
import Kernels.TmlFa4Fwd.Proof.Mma.Export.TmemCount
import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.Ops
import Kernels.TmlFa4Fwd.Proof.Protocol.Shared.WFrame
import Lemmas.Flow.AllocTmpl
import Lemmas.Flow.LoadShared
import Lemmas.Kernel.Safety.TmemAlloc
import Lemmas.Kernel.Source.ProtectedRead
import Std.Tactic.BVDecide.Normalize.Prop

import Kernels.TmlFa4Fwd.Proof.Common.SharedSites
import Lemmas.Kernel.Source.ProtectedReadU

@[expose] public section

/-! # The allocation word is 0

A lane of the MMA warp reads the allocation word back at `sb + 312` (`ldAlloc`) and keeps it for
its deallocation. The read returns the bytes of the allocation's store (a protected read,
`RoleTable.protected_read_of_followed`):

* the writer is lane 0's address store after its allocation (for lane 0 itself, its own next
  event; for another lane, the store its allocation waited for, `allocResult_witnessed`), and it
  is before the read at every byte by Core's allocation-result order (`AllocResultBefore`);
* no other write covers the word (`wr_low`: the only write below `sb + 316` in shared memory is an
  address store, one per CTA: lane 0 of warp 12 allocates once, `res_unique`);
* the store writes column 0 (`alloc_store_zero`: the allocation is its CTA's first record, at
  column 0 by `Tmem.One.alloc_zero`, and Core's `ResultOk` puts that column in the store).

So every state of the role past the read holds the word `0` (`ta_zero`), the deallocation frees
column 0, and with `tmem1Ops` and `tmem1_exit` the facts `Tmem.One.Tmem1Facts` hold
(`tmem1Facts`): ERR-TMEM-RESOURCE and ERR-TMEM-NOT-RELEASED are excluded (`noTmemResource`,
`noTmemRelease`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow PTX.Frame Tmem.Pair

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- Two resource events of a thread with as many resource events before them are one event. -/
theorem res_unique {h i j : Nat} {e e' : Event} (hi : X.get (h, i) = some e)
    (hj : X.get (h, j) = some e') (hti : isTmemOp e = true) (htj : isTmemOp e' = true)
    (h0 : opsAt X h i = opsAt X h j) : i = j := by
  rcases lt_trichotomy i j with hl | hl | hl
  · have := tmemOps_lt hi hti hl
    simp only [opsAt] at h0
    omega
  · exact hl
  · have := tmemOps_lt hj htj hl
    simp only [opsAt] at h0
    omega

/-- An allocation event of a lane of warp 12 has no resource event before it. -/
theorem alloc_ops0 (ht : Tmem.One.Tmem1Ops L X 12) {h i pc : Nat} {grp : CtaGroup}
    {dst : Option Loc} {nn : Nat} (hh : h < L.threads)
    (he : X.get (h, i) = some ⟨pc, .tc (.resource grp dst (.alloc nn))⟩) :
    opsAt X h i = 0 ∧ nn = 512 :=
  shape_alloc (ht.event hh he).2.2

/-- **Lane 0's address store writes column 0.** -/
theorem alloc_store_zero (hX : Consistent L kernel Assumptions.all m X)
    (ht : Tmem.One.Tmem1Ops L X 12) {g0 j0 pc pc' : Nat} {grp : CtaGroup} {dst : Option Loc}
    {nn : Nat} {a : Acc} {bs : List Byte} (hg0 : g0 < L.threads)
    (hl : g0 % L.block = 384)
    (h1 : X.get (g0, j0) = some ⟨pc, .tc (.resource grp dst (.alloc nn))⟩)
    (h2 : X.get (g0, j0 + 1) = some ⟨pc', .wr a bs⟩) :
    bs = (Value.bits 32 (BitVec.ofNat 64 0)).toBytes := by
  obtain ⟨h0, rfl⟩ := alloc_ops0 ht hg0 h1
  have hg : g0 = g0 / L.block * L.block + 12 * 32 := by
    have := Nat.div_add_mod g0 L.block
    rw [hl] at this
    rw [Nat.mul_comm]
    omega
  have hlen : j0 + 1 < (X.tr g0).length :=
    (List.getElem?_eq_some_iff.mp (show (X.tr g0)[j0 + 1]? = _ from h2)).1
  have hpos : 0 < opsAt X g0 (j0 + 1) := by
    have := tmemOps_lt h1 rfl (show j0 < j0 + 1 by omega)
    simp only [opsAt] at h0 ⊢
    omega
  rw [hg] at hlen hpos
  obtain ⟨r, hr, hr0⟩ := Tmem.One.first_recorded hX ht hlen hpos
  obtain ⟨hcta, hw, -, hreq, hle, hls⟩ := Tmem.One.record_info hX ht hr
  rw [← hg] at hle hls hr0
  rw [hr0] at hls
  have hidx : r.own.indices 0 = j0 := res_unique hle h1 rfl rfl (by rw [hr0, h0])
  simp only [TmemShape] at hls
  rw [← hreq] at hls
  obtain ⟨col, ha⟩ := Tmem.Action.request_eq_alloc hls
  obtain ⟨-, rfl⟩ := Tmem.One.alloc_zero hX ht hr _ _ ha
  have hev : r.own.event L 0 = (g0, j0) := by
    simp only [WarpRequest.event, hcta, hw, Fin.val_zero, Nat.add_zero, hidx]
    rw [← hg]
  exact hX.tmemPairResult (g0, j0) pc grp dst 512 h1 (g0 / L.block) r 0 hr hev ha pc' a bs h2

/-- The allocation word's footprint as the role reads it. -/
abbrev wordAcc (L : Launch) (g : Nat) : Acc :=
  { loc := (⟨.shared, g / L.block, L.sharedBase + 312⟩ : Loc).at 0, size := 4, elem := 0 }

set_option maxHeartbeats 4000000 in
/-- **The read at `ldAlloc` reads the allocation word**: the four bytes at `sb + 312`. -/
theorem Mma.ld_acc (hp : Pre p L m) {v : Mma.V} {t : TState} {ins : Instr} {e : Event}
    {o : Option TState} (h : (Mma.code p L g (Mma.ent p L)).AtD ⟨.ldAlloc, v⟩ t)
    (hc : kernel.code[(Mma.code p L g (Mma.ent p L)).pc ⟨.ldAlloc, v⟩]? = some ins)
    (hf : Fires ((Mma.code p L g (Mma.ent p L)).pc ⟨.ldAlloc, v⟩)
      (eventTmpl Assumptions.all L g t ins.op) e o)
    {a : Acc} {bs : List (Option Byte)} (hk : e.kind = .rd a bs) : a = wordAcc L g := by
  have hs0 : t.sub = 0 := h.2.1
  replace h : At t (Mma.Site.ldAlloc).pc (Mma.facts p L g (Mma.ent p L) ⟨.ldAlloc, v⟩) := h
  replace hc : kernel.code[(Mma.Site.ldAlloc).pc]? = some ins := hc
  have hsh := hp.shared
  obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
  change Fires _ (loadTmpl Assumptions.all L g t .shared false 32 [1179] 2535 312) e o at hf
  have hr : t.regs 2535 = some (b32 L.sharedBase) :=
    (Mma.reg_of (d := ⟨.ldAlloc, v⟩) h (by lit_mem)).trans rfl
  have hea := effAddr_b32_off (L := L) (g := g) (off := 312) hr (by omega)
  refine shape_ld (P := fun e => ∀ a bs, e.kind = .rd a bs → a = wordAcc L g) hf hea hs0
    (fun bs _ a' bs' hk' => by cases hk'; rfl) (fun f a' bs' hk' => by cases hk') a bs hk

/-- **The writer of the allocation word**: lane 0's address store after the allocation of a lane
of warp 12, before that lane's later events in Core's allocation-result order. -/
theorem alloc_writer (hX : Consistent L kernel Assumptions.all m X) (hg : g < L.threads)
    {k' j : Nat} (hall : AllocAt L X g k') (hst : StoreAt L X g k') (hkj : k' < j)
    (hj : j < (X.tr g).length) :
    ∃ w dst, AllocResult L X w (g, k') dst := by
  by_cases hl : laneOf L g = 0
  · obtain ⟨bs, hb⟩ := hst hl
    exact ⟨(g, k' + 1), _, ⟨⟨hg, hg, rfl⟩, rfl⟩, hl, rfl, rfl, k', 1909, .one, 512, 0, bs, rfl,
      hall.1, hall.1, ⟨⟨_, hall.1, rfl⟩, hall.2⟩, ⟨⟨_, hall.1, rfl⟩, hall.2⟩, hb⟩
  · have hret : Returned X (g, k') := by
      simp only [Returned, hall.1]
      show k' + 1 < (X.tr g).length
      omega
    have hready := hX.dependency.ready _ hret _ (allocResult_witnessed L X (g, k') hall.1 hl)
    obtain ⟨x, -, hx⟩ := hready
    cases x with
    | thread store =>
      obtain ⟨dst, hAR⟩ := hx
      exact ⟨store, dst, hAR⟩
    | async => exact hx.elim

theorem lane0_384 (hb : L.block = 512) {h : Nat} (hw : h % L.block / 32 = 12)
    (hl : laneOf L h = 0) :
    h % L.block = 384 := by
  simp only [laneOf] at hl
  rw [hb] at hw hl ⊢
  omega

set_option maxHeartbeats 16000000 in
/-- **The read of the allocation word returns column 0.** -/
theorem ld_word (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X)
    (hg : g < L.threads) (h12 : Prologue.warpIndex L g = 12) {j : Nat} {v : Mma.V}
    {n : Cls → Nat} (hσ : Frame.stateAt (thread p L) X g j =
      some (some (Mma.minj p L g ⟨.ldAlloc, v⟩ n)))
    {pc : Nat} {a : Acc} {bs : List (Option Byte)} (he : X.get (g, j) = some ⟨pc, .rd a bs⟩) :
    bs = (Value.bits 32 (BitVec.ofNat 64 0)).toBytes.map some := by
  have ht := tmem1Ops hp hX hFw
  have hT := table_shape_of hp hFw
  have hF := table_followed hp hX hFw
  have hsb := hp.shared.2.1
  have hblk := hp.block
  have hjl : j < (X.tr g).length :=
    (List.getElem?_eq_some_iff.mp (show (X.tr g)[j]? = _ from he)).1
  -- the read's footprint
  obtain ⟨t, ins, o, hat, -, hc, hf⟩ := Frame.fired_siteU (fun g hg => thread_sound hp hg) hX he hσ
    (fun _ => nofun)
  have ha : a = wordAcc L g := Mma.ld_acc hp hat hc hf rfl
  subst ha
  -- the writer
  obtain ⟨⟨k', hk', hall, hst⟩, -⟩ := mma_trace hp hX hg h12 j hjl.le _ hσ
  obtain ⟨w, dst, hAR⟩ := alloc_writer hX hg hall hst hk' hjl
  have hAR' := hAR
  obtain ⟨⟨⟨hw1, -, hcw⟩, hww⟩, hl0, -, -, j0, site, grp, nn, kk, bytes, hw2, hget0, hgetr, -, -,
    hgetw⟩ := hAR'
  rw [hall.1] at hgetr
  simp only [Option.some.injEq, Event.mk.injEq, Kind.tc.injEq, TcKind.resource.injEq,
    Tmem.Request.alloc.injEq] at hgetr
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hgetr
  have h12g : g % L.block / 32 = 12 := h12
  have hw384 : w.1 % L.block = 384 := lane0_384 hblk (by rw [hww]; exact h12g) hl0
  obtain ⟨w1, w2⟩ := w
  simp only at hw2 hw1 hcw hww hl0 hw384 hget0
  subst hw2
  have hbytes := alloc_store_zero hX ht hw1 hw384 hget0 hgetw
  subst hbytes
  -- the protected read
  refine RoleTable.protected_read_of_followedU (T := table p L) (S := fun g => g < L.threads)
    (fun g hg => thread_sound hp hg) hX hT hF (r := (g, j)) (w := (w1, j0 + 1))
    (dst := { loc := ⟨.shared, g / L.block, L.sharedBase + 312⟩, size := 4 })
    (.inl ⟨pc, he⟩) (.inl ⟨_, hgetw⟩) (by simp [Loc.at]) rfl rfl ?_ ?_ ?_
  · intro k hk
    have hk4 : k < 4 := hk
    refine modelCausality.of_allocResultBefore L ⟨k', _, wordAcc L g, _, hAR, hk', ?_, ⟨pc, he⟩, ?_⟩
    · simp only [Loc.InRange, Loc.at]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> first | rfl | trivial | omega
    · simp only [Acc.Covers, Loc.InRange, Loc.at]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> first | rfl | trivial | omega
  · intro g' j' d' e' hg' hσ' hJ' hi' hev' he' dst' hwo ⟨l, hcov, k, hk, hlk⟩
    subst hlk
    have hk4 : k < 4 := hk
    simp only [Acc.Covers, Loc.InRange, Loc.at] at hcov
    obtain ⟨hsp, hct, hlo, hhi⟩ := hcov
    have hsh : dst'.loc.space = .shared := hsp.symm
    rcases writeOf_kind hwo with hwk | ⟨ai, s, x, y, kk, hk', hwl⟩ |
      ⟨ai, s, x, y, kk, hk', hwl⟩ | ⟨s, tg, hk'⟩
    · rcases wr_low hp hX he' hσ' hJ' hev' hwk hwo hsh with ⟨n', rfl⟩ | hge
      · obtain ⟨t', ins', o', hat', hi'', hc', hf'⟩ :=
          strict_fired_site hp hX he' hσ' rfl
        obtain ⟨col, hki⟩ := (Mma.pre_kind (g := g') (s := .wr) hp hat' hc' hf').2.2 rfl
        have h12' := jr_mma hJ'
        have hj'l : j' < (X.tr g').length :=
          (List.getElem?_eq_some_iff.mp (show (X.tr g')[j']? = _ from he')).1
        obtain ⟨hl', k'', rfl, hall'⟩ := mma_trace hp hX hg' h12' j' hj'l.le _ hσ'
        have hdst : dst' = { loc := ⟨.shared, g' / L.block, L.sharedBase + 312⟩, size := 4 } := by
          obtain ⟨pce, kind⟩ := e'
          simp only at hki
          subst hki
          exact hwo
        subst hdst
        simp only at hct
        refine ⟨by obtain ⟨pce, kind⟩ := e'; simp only at hki; subst hki; trivial, .inl ?_⟩
        have hg'w : g' = w1 := sameWarp_leader_eq ⟨⟨hg', hw1, by omega⟩,
          by rw [hww]; exact h12'.trans h12g.symm⟩ hl' hl0
        subst hg'w
        have h0 := (alloc_ops0 ht hg' hall'.1).1
        have h0' := (alloc_ops0 ht hg' hget0).1
        have := res_unique hall'.1 hget0 rfl rfl (by rw [h0, h0'])
        rw [this]
      · omega
    · have := tload_low hp hX hFw (show X.get (g', j') = some ⟨e'.pc, .tensorIssue ai s⟩ by
        rw [he', ← hk']) hwl
      omega
    · have := tstore_global hwl
      rw [this] at hsh
      cases hsh
    · exact (no_clc hp hX hFw g' j' e'.pc _ _ (by rw [he', ← hk'])).elim
  · intro ref dst' bytes hm hn
    obtain ⟨e', he', -⟩ := memWrites_writeOf hm
    exact absurd (Frame.lt_of_get hX he') hn

theorem rebuild_zero :
    rebuild 3 ((Value.bits 32 (BitVec.ofNat 64 0)).toBytes.map some) =
      .ok (.bits 32 (BitVec.ofNat 64 0)) :=
  rebuild_b32 0

/-- **Every state of the MMA warp's role past the read holds the allocation word 0.** -/
theorem ta_zero (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X)
    (hg : g < L.threads) (h12 : Prologue.warpIndex L g = 12) {k : Nat} {d : Mma.D}
    {n : Cls → Nat} (hk : k ≤ (X.tr g).length)
    (hσ : Frame.stateAt (thread p L) X g k = some (some (Mma.minj p L g d n)))
    (hpast : Mma.past d.site = true) : d.v.ta = .bits 32 (BitVec.ofNat 64 0) := by
  obtain ⟨-, hrd⟩ := mma_trace hp hX hg h12 k hk _ hσ
  obtain ⟨j, -, ⟨v, n', hσj⟩, pc, a, bs, he, hb⟩ := hrd hpast
  rw [ld_word hp hX hFw hg h12 hσj he, rebuild_zero] at hb
  exact (Except.ok.inj hb).symm

set_option maxHeartbeats 4000000 in
/-- **The deallocation frees column 0** when the allocation word is 0. -/
theorem Mma.dealloc_col (hp : Pre p L m) {l : Bool} {v : Mma.V} {t : TState} {ins : Instr}
    {e : Event} {o : Option TState}
    (h : (Mma.code p L g (Mma.ent p L)).AtD ⟨.dealloc l, v⟩ t)
    (hc : kernel.code[(Mma.code p L g (Mma.ent p L)).pc ⟨.dealloc l, v⟩]? = some ins)
    (hf : Fires ((Mma.code p L g (Mma.ent p L)).pc ⟨.dealloc l, v⟩)
      (eventTmpl Assumptions.all L g t ins.op) e o)
    (hta : v.ta = .bits 32 (BitVec.ofNat 64 0)) {grp : CtaGroup} {dst : Option Loc} {a n : Nat}
    (hk : e.kind = .tc (.resource grp dst (.dealloc a n))) : a = 0 := by
  have hb : L.block % 32 = 0 := by rw [hp.block]
  replace h : At t (Mma.Site.dealloc l).pc (Mma.facts p L g (Mma.ent p L) ⟨.dealloc l, v⟩) := h
  replace hc : kernel.code[(Mma.Site.dealloc l).pc]? = some ins := hc
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2766)
  have h2 : t.regs 2682 = some (b32 512) :=
    Mma.reg_bits h (by show 2682 ∈ Flow.live 2766; lit_mem) rfl
  have h1 : t.regs 1179 = some (b32 0) :=
    Mma.reg_bits h (by show 1179 ∈ Flow.live 2766; lit_mem)
      (by simp [Mma.valueOf, Mma.values, Mma.valuesRole, hta, List.lookup])
  have hn := readBits_b32 (L := L) (g := g) h2 (by decide)
  have hz := readBits_b32 (L := L) (g := g) h1 (by decide)
  simp [eventTmpl, tcTmpl, ofExec, hb, hz, hn, bind, Except.bind, pure, Except.pure,
    Tmem.validColumns, Fires] at hf
  rw [hf.1] at hk
  simp only [Kind.tc.injEq, TcKind.resource.injEq, Tmem.Request.dealloc.injEq] at hk
  omega

set_option maxHeartbeats 4000000 in
/-- **The deallocation is no undefined behaviour** when the allocation word is 0: it frees the 512
columns at column 0. -/
theorem Mma.dealloc_safe (hp : Pre p L m) {l : Bool} {v : Mma.V} {t : TState} {ins : Instr}
    {e : Event} {o : Option TState}
    (h : (Mma.code p L g (Mma.ent p L)).AtD ⟨.dealloc l, v⟩ t)
    (hc : kernel.code[(Mma.code p L g (Mma.ent p L)).pc ⟨.dealloc l, v⟩]? = some ins)
    (hf : Fires ((Mma.code p L g (Mma.ent p L)).pc ⟨.dealloc l, v⟩)
      (eventTmpl Assumptions.all L g t ins.op) e o)
    (hta : v.ta = .bits 32 (BitVec.ofNat 64 0)) (f : Fault) : e.kind ≠ .ub f := by
  have hb : L.block % 32 = 0 := by rw [hp.block]
  replace h : At t (Mma.Site.dealloc l).pc (Mma.facts p L g (Mma.ent p L) ⟨.dealloc l, v⟩) := h
  replace hc : kernel.code[(Mma.Site.dealloc l).pc]? = some ins := hc
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2766)
  have h2 : t.regs 2682 = some (b32 512) :=
    Mma.reg_bits h (by show 2682 ∈ Flow.live 2766; lit_mem) rfl
  have h1 : t.regs 1179 = some (b32 0) :=
    Mma.reg_bits h (by show 1179 ∈ Flow.live 2766; lit_mem)
      (by simp [Mma.valueOf, Mma.values, Mma.valuesRole, hta, List.lookup])
  have hn := readBits_b32 (L := L) (g := g) h2 (by decide)
  have hz := readBits_b32 (L := L) (g := g) h1 (by decide)
  simp [eventTmpl, tcTmpl, ofExec, hb, hz, hn, bind, Except.bind, pure, Except.pure,
    Tmem.validColumns, Fires] at hf
  rw [hf.1]
  simp

set_option maxHeartbeats 8000000 in
/-- **The Tensor Memory facts of the MMA warp** (`Tmem.One.Tmem1Facts`): its operations, the
deallocation of column 0, and its three operations before a return. -/
theorem tmem1Facts (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) :
    Tmem.One.Tmem1Facts L X 12 := by
  have hT := table_shape_of hp hFw
  have hF := table_followed hp hX hFw
  refine ⟨tmem1Ops hp hX hFw, fun {g k pc grp dst a n} hg he => ?_,
    fun hg h12 he => tmem1_exit hp hX hFw hg h12 he⟩
  obtain ⟨σ, hσ, hJ, hi, hev⟩ := ev_at hp hX hT hF he (by intro f hf; cases hf)
  obtain ⟨d, n', rfl⟩ := tev_res hJ hi hev rfl
  have h12 := jr_mma hJ
  have hk : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp
    (show (X.tr g)[k]? = _ from he)).1
  obtain ⟨t, ins, o, hat, hinv, hcd, hf⟩ :=
    Frame.fired_siteU (fun g hg => thread_sound hp hg) hX he hσ
    (fun _ => nofun)
  rcases d with s0 | ⟨⟨⟩, d⟩
  · exfalso
    have hk3 := Mma.pre_kind hp hat hcd hf
    cases s0 with
    | set => obtain ⟨_, h⟩ := hk3.1 rfl; cases h
    | alloc => cases hk3.2.1 rfl
    | wr => obtain ⟨_, h⟩ := hk3.2.2 rfl; cases h
    | enter => exact absurd hinv.2 (by simp [Mma.Start.exit])
  · have hrd := Mma.ev_res (Mma.mfired hp hX he hσ).1 rfl
    have hkd := Mma.rd_kind hp hat hcd hf (by intro f hf; cases hf)
    obtain ⟨site, v⟩ := d
    cases site <;> simp only [Mma.isRD, reduceCtorEq] at hrd
    · exact absurd (hkd.1 ⟨_, rfl⟩) (by simp)
    · exact Mma.dealloc_col hp hat hcd hf
        (ta_zero hp hX hFw hg h12 hk.le hσ rfl) rfl

/-- **ERR-TMEM-RESOURCE**: the MMA warp's allocator history replays without a fault. -/
theorem noTmemResource (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) :
    ¬ Tmem.Pair.ResourceUnsafe L X :=
  (Frame.tmem1_safe hX (tmem1Facts hp hX hFw)).1

/-- **ERR-TMEM-NOT-RELEASED**: the MMA warp releases its columns before it returns. -/
theorem noTmemRelease (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) :
    ¬ Tmem.Pair.ReleaseUnsafe L X :=
  (Frame.tmem1_safe hX (tmem1Facts hp hX hFw)).2

end
end PTX.Kernels.TmlFa4Fwd.Proof
