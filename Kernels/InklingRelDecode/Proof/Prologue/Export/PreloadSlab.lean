-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Lib.KvSlab
import Kernels.InklingRelDecode.Proof.Common.ValueSound
import Kernels.InklingRelDecode.Proof.Prologue.ValueEvent
import Kernels.InklingRelDecode.Proof.Common.ValueFollow
import Kernels.InklingRelDecode.Proof.Common.Where
import Kernels.InklingRelDecode.Proof.Common.FollowControl
import Kernels.InklingRelDecode.Proof.Common.StartupEvents
import Kernels.InklingRelDecode.Proof.Prologue.Data.Step
import Kernels.InklingRelDecode.Proof.Prologue.Data.PayRow
import Kernels.InklingRelDecode.Proof.Prologue.Export.BlockAddress
import Kernels.InklingRelDecode.Proof.Prologue.CopyFoot
import Kernels.InklingRelDecode.Proof.Lib.GlobalLoad
import Kernels.InklingRelDecode.Proof.Lib.Coordinates
import Lemmas.Kernel.StateMap
import Lemmas.Kernel.FrameU
import Lemmas.Kernel.CountClosed
import Lemmas.Flow.TensorLoadFacts

/-! # A prologue preload is the copy of a box of an existing slab

The value thread machine `threadD` is the control thread machine with the prologue's value
machine in its slot, and a value state is followed whenever its control state is
(`threadD_stepMap`). At the tensor load `ptc b j` its value state holds the two coordinate
registers as data facts: the column of half `j % 2` of the block (the broadcast bit, the head's
column offset) and the row of the page word the load `lb b (j / 2)` returned (`proD_pay`: that
event is earlier in the thread's trace; `block_page`: it read the page of an existing slab). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Export
open PTX PTX.Flow PTX.Proof Control Data

variable {Q : Params} {L : Launch} {g : Nat}

private theorem lb_load : ∀ (b : Fin 3) (h : Fin 2),
    Lib.globalLoad (Prologue.Site.lb b h).pc (2071 + 2 * b.val + h.val) 32 = true := by
  decide +kernel

private theorem proD_pay {m : Mem0} {X : Execution} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) {k : Nat}
    {w : Value} {d : Prologue.Data.D} {n : Cls → Nat}
    (hk : k ≤ (X.tr g).length)
    (hs : Frame.stateAt (threadD Q L) X g k = some (some (proDState w d n)))
    (nub : Frame.NoUbBefore X g k) (b : Fin 3) (h : Fin 2) (hr : Tag.row b h ∈ tags d.c.site) :
    ∃ k' < k, ∃ a bs, X.get (g, k') = some ⟨(Prologue.Site.lb b h).pc, .rd a bs⟩ ∧
      d.v.pay b h = loadVal bs := by
  have key := proD_induct (Q := Q) (L := L) (X := X)
    (fun k d => ∀ b h, Tag.row b h ∈ tags d.c.site → ∃ k' < k, ∃ a bs,
      X.get (g, k') = some ⟨(Prologue.Site.lb b h).pc, .rd a bs⟩ ∧ d.v.pay b h = loadVal bs)
    (fun k b' h' hr' =>
      ((by decide : ∀ b h, Tag.row b h ∉ tags Prologue.Site.sMax) b' h' hr').elim)
    (by
      intro k e w' old cnt d' he' hu hs IH hv b' h' hr'
      rcases pay_succ hv hr' with ⟨hrow, heq⟩ | ⟨hsite, hrec⟩
      · obtain ⟨k', hk', a, bs, get, pay⟩ := IH b' h' hrow
        exact ⟨k', by omega, a, bs, get, by rw [heq]; exact pay⟩
      · obtain ⟨t, ins, o, ht, -, hc, fire⟩ :=
          Frame.fired_siteU (fun g h => threadD_sound hp h) hX he' hs hu
        have pc := Frame.event_pcU (fun g h => threadD_sound hp h) hX he' hs hu
        change kernel.code[old.c.site.pc]? = some ins at hc
        change Fires old.c.site.pc (eventTmpl Assumptions.all L g t ins.op) e o at fire
        change e.pc = old.c.site.pc at pc
        rw [hsite] at hc fire pc
        rcases Lib.global_load_kind hc (lb_load b' h') fire with ⟨a, bs, hk⟩ | ⟨f, hf⟩
        · obtain ⟨epc, ekind⟩ := e
          have hk' := hrec a bs hk
          change ekind = _ at hk
          subst hk
          change epc = _ at pc
          rw [pc] at he'
          exact ⟨k, by omega, a, bs, he', hk'⟩
        · exact absurd hf (hu f)) hk hs nub
  exact key b h hr

/-- The two coordinate registers of a tensor load of the prologue's copies. -/
private def copyRegs : Option Instr → Option (Nat × Nat)
  | some ⟨_, .cpTensor false false _ 0 (.reg 1949) [.reg c, .reg r] _ 0 none .tile none⟩ =>
    some (c, r)
  | _ => none

private theorem of_copyRegs {ins : Option Instr} {c r : Nat} (h : copyRegs ins = some (c, r)) :
    ∃ guard dst mb, ins = some ⟨guard,
      .cpTensor false false dst 0 (.reg 1949) [.reg c, .reg r] mb 0 none .tile none⟩ := by
  unfold copyRegs at h
  split at h <;> simp_all

private def half (j : Fin 4) : Fin 2 := ⟨j.val % 2, by omega⟩

private def pair (j : Fin 4) : Fin 2 := ⟨j.val / 2, by omega⟩

private theorem copy_regs : ∀ (b : Fin 3) (j : Fin 4),
    copyRegs kernel.code[(Site.ptc b j).pc]? = some ((Tag.col b (half j)).reg,
      (Tag.row b (pair j)).reg) ∧
    Tag.col b (half j) ∈ tags (.ptc b j) ∧ Tag.row b (pair j) ∈ tags (.ptc b j) ∧
    (∀ h, (Site.lb b h).pc = 197 ∨ (Site.lb b h).pc = 220 ∨ (Site.lb b h).pc = 241 ∨
      (Site.lb b h).pc = 262 ∨ (Site.lb b h).pc = 283 ∨ (Site.lb b h).pc = 304) ∧
    Iface.preloadOff (Site.ptc b j).pc % 1024 = 0 := by
  decide +kernel

private theorem ptc_site (s : Site) :
    s.pc ∈ [211, 217, 226, 231, 253, 259, 268, 273, 295, 301, 310, 315] → ∃ b j, s = .ptc b j := by
  cases s <;> first | exact fun _ => ⟨_, _, rfl⟩ |
    (repeat' first | decide +kernel | (rename_i j; revert j))

private theorem word_b32 (n : Nat) : (Lib.word (b32 n)).toNat = n % 2 ^ 32 := by
  unfold Lib.word b32 truncBits Value.regBits
  have := Nat.mod_lt n (show 0 < 2 ^ 32 by norm_num)
  simp
  omega

/-- **A prologue preload is the copy of a box of an existing slab** into the issuer's CTA. -/
public theorem preload_slab_at {Q L m X g k pc addr sp} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (he : X.get (g, k) = some ⟨pc, .tensorIssue addr sp⟩)
    (site : pc ∈ [211, 217, 226, 231, 253, 259, 268, 273, 295, 301, 310, 315]) :
    ∃ (b : Fin 3) (isV h hh : Nat), isV ≤ 1 ∧ h ≤ 1 ∧ hh ≤ 1 ∧
      2 * ((L.ctaidOf (g / L.block)).get .x + b.val * Q.splits) + h <
        2 * Q.blocks ((L.ctaidOf (g / L.block)).get .z) ∧
      sp = Lib.kvCopySpec Q (g / L.block)
        ((L.ctaidOf (g / L.block)).get .y * Q.headCols + 128 * isV + 64 * hh)
        (Q.page ((L.ctaidOf (g / L.block)).get .z)
          (2 * ((L.ctaidOf (g / L.block)).get .x + b.val * Q.splits) + h) * Q.pageRows +
          (L.ctaidOf (g / L.block)).get .y * Q.headRows)
        (L.sharedBase + 32768 * b.val + 16384 * hh + 98304 * isV + 8192 * h) sp.mbar := by
  have hg := Frame.lt_of_get hX he
  have range : 27 < pc ∧ pc < 574 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at site
    omega
  obtain ⟨w, d, n, t, ins, u, hs, ht, pce, hc, fire⟩ :=
    proD_event hp hX he (by simp) range.1 range.2
  obtain ⟨b, j, hsite⟩ := ptc_site d.c.site (pce ▸ site)
  obtain ⟨hregs, hcol, hrow, hlb, hoff⟩ := copy_regs b j
  rw [hsite] at hc
  rw [hc] at hregs
  obtain ⟨guard, dst, mb, hins⟩ := of_copyRegs hregs
  obtain rfl := Option.some.inj hins
  obtain ⟨hpc, sub, acc, flt, regs⟩ := ht
  obtain ⟨regsC, regsD⟩ := (holds_append _ _ _).mp regs
  obtain ⟨desc, -, -, -, base⟩ := preload_footprint hp ⟨hpc, sub, acc, flt, regsC⟩ b j hsite
    (by rw [hsite]; exact hc) fire rfl
  have load := fires_cpTensor_copy fire rfl
  have r0 := holds_mem regsD (List.mem_map.mpr ⟨_, hsite ▸ hcol, rfl⟩)
  have r1 := holds_mem regsD (List.mem_map.mpr ⟨_, hsite ▸ hrow, rfl⟩)
  obtain ⟨k', -, a', bs', get', pay⟩ := proD_pay hp hX (List.getElem?_eq_some_iff.mp he).1.le hs
    (Frame.noUbBefore_of_get hX he) b (pair j) (hsite ▸ hrow)
  obtain ⟨sl, hsl, rb, slEq⟩ := block_page hp hX hf get' (hlb (pair j))
  have page : d.v.pay b (pair j) = b32 (Q.page ((L.ctaidOf (g / L.block)).get .z) sl) := by
    rw [pay]
    unfold loadVal
    rw [rb]
    rfl
  change t.regs _ = some (colVal Q L g d.c.broadcast (half j)) at r0
  change t.regs _ = some (rowVal Q L g (d.v.pay b (pair j))) at r1
  rw [page] at r1
  obtain ⟨-, c0, c1⟩ := Lib.kv_coord_lt hp hg hsl (isV := (half j).val)
    (hh := (Lib.word d.c.broadcast).toNat % 2) (Nat.lt_succ_iff.mp (half j).isLt) (by omega)
  have hpr := Nat.le_mul_of_pos_right (Q.page ((L.ctaidOf (g / L.block)).get .z) sl) hp.pageRowsPos
  have align := hp.sharedAlignment
  rw [hsite] at base
  have off : ∀ b j, Iface.preloadOff (Site.ptc b j).pc = 32768 * b.val + 98304 * (half j).val +
      8192 * (pair j).val := by decide +kernel
  have lbEq : ∀ (b : Fin 3) (h : Fin 2), (Site.lb b h).pc = lbPcAt b.val h.val := by
    decide +kernel
  have sl' := slEq b (pair j) (lbEq b (pair j))
  refine ⟨b, (half j).val, (pair j).val, (Lib.word d.c.broadcast).toNat % 2,
    Nat.lt_succ_iff.mp (half j).isLt, Nat.lt_succ_iff.mp (pair j).isLt, by omega,
    sl' ▸ hsl, ?_⟩
  rw [← sl']
  have := Lib.kvCopy_of_load (isV := (half j).val) (hh := (Lib.word d.c.broadcast).toNat % 2) hp hg
    load desc hsl (Nat.lt_succ_iff.mp (half j).isLt) (by omega) r0 r1 ?_ ?_ base
  · have hD : L.sharedBase + 16384 * ((Lib.word d.c.broadcast).toNat % 2) +
        Iface.preloadOff (Site.ptc b j).pc = L.sharedBase + 32768 * b.val +
        16384 * ((Lib.word d.c.broadcast).toNat % 2) + 98304 * (half j).val +
        8192 * (pair j).val := by
      rw [off]
      omega
    rw [hD] at this
    exact this
  · rw [Nat.mul_comm Q.headCols, Nat.mod_eq_of_lt (by omega)]
    omega
  · have hP : Q.page ((L.ctaidOf (g / L.block)).get .z) sl % 2 ^ 32 =
        Q.page ((L.ctaidOf (g / L.block)).get .z) sl := Nat.mod_eq_of_lt (by omega)
    rw [word_b32, hP, Nat.mul_comm Q.headRows]
    exact Nat.mod_eq_of_lt (by omega)

/-- **A prologue preload is the copy of a box of an existing slab** into the issuer's CTA. -/
public theorem preload_slab {Q L m X g k pc addr sp} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (he : X.get (g, k) = some ⟨pc, .tensorIssue addr sp⟩)
    (site : pc ∈ [211, 217, 226, 231, 253, 259, 268, 273, 295, 301, 310, 315]) :
    Lib.KvSlab Q (g / L.block) sp := by
  obtain ⟨b, isV, h, hh, hV, hH, hh2, hl, hsp⟩ := preload_slab_at hp hX hf he site
  have al := hp.sharedAlignment
  obtain ⟨-, hy, hz⟩ := Lib.coordinate_bounds hp (Frame.lt_of_get hX he)
  exact ⟨_, _, _, _, _, isV, hh, hz, hl, hy, hV, hh2, by omega, hsp⟩

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Export
