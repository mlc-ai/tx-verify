-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.KV.CopyOrder
public import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.InputBytes
public import Kernels.TmlFa4Fwd.Proof.Protocol.Values.Block
import Kernels.TmlFa4Fwd.Proof.Protocol.Staging.Final
import Kernels.TmlFa4Fwd.Proof.LdWarp.Export.ArrCopies
import Kernels.TmlFa4Fwd.Proof.Lib.GlobalWrites
import Kernels.TmlFa4Fwd.Proof.Protocol.KV.Handoff
import Kernels.TmlFa4Fwd.Proof.Protocol.Shared.CopySource
import Kernels.TmlFa4Fwd.Proof.Protocol.Shared.Lifetime
import Kernels.TmlFa4Fwd.Proof.Protocol.Values.Block
import Lemmas.Async.ReadReuse
import Lemmas.Async.ReadSources
import Lemmas.Async.AsyncExecution
import Lemmas.Flow.NthEv
import Lemmas.Tcgen05.MmaOperandObservations
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The sources of the K/V operand bytes

The MMAs of ring use `t` read the block that the loader lanes copied as packet `t`: element
`(row, d)` is of the copy of row `row / 8` and half `d / 64` of the lane `kvLane`, which was made
before the read (`kv_copy_exists`). Every other write of the byte is a copy of another packet of the
slot, which is before that copy or after the read (`kv_write_order`), so the operand byte is the
byte the copy wrote (`kv_operand`), a byte of its source or a zero (`kv_operand_src`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Values
open PTX PTX.Proof PTX.Flow TcMma Tm AsyncCopy PTX.MbarRing

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g k : Nat}

/-- The loader lane of CTA `c` that copies element `(row, d)` of a block. -/
def kvLane (L : Launch) (c row d : Nat) : Nat := c * L.block + 448 + blockLane row d

/-- **The copy of element `(row, d)` of packet `t`.** -/
structure KvCp (L : Launch) (X : Execution) (c t row d jc : Nat) (sp : AsyncCopy.Spec) :
    Prop where
  get : ∃ pc, X.get (kvLane L c row d, jc) = some ⟨pc, .copy sp⟩
  ld : LdCp L X (kvLane L c row d) jc sp
  cnt : ((X.tr (kvLane L c row d)).take jc).countP cpCopy = 32 * t + (2 * (row / 8) + d / 64)
  dst : sp.dst = { loc := ⟨.shared, c, kvBase L (t % 3) + 16384 * (d / 64) + 1024 * (row / 8) +
    16 * Loader.rowCol (blockLane row d)⟩, size := 16 }

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
include hp hX hFw

omit hX hFw in
theorem kvLane_spec {c row d : Nat} : kvLane L c row d / L.block = c ∧
    (Prologue.warpIndex L (kvLane L c row d) = 14 ∨
      Prologue.warpIndex L (kvLane L c row d) = 15) ∧
    kvLane L c row d % L.block % 64 = blockLane row d := by
  have hb := hp.block
  have hl := blockLane_lt row d
  unfold kvLane Prologue.warpIndex
  rw [hb]
  refine ⟨by omega, by omega, by omega⟩

/-- **The copies of a packet before a read of its use.** -/
theorem kv_copy_exists {t row d : Nat} (hR : KvRead L X g k t) (hrow : row < 128) (hd : d < 128) :
    ∃ jc sp, KvCp L X (g / L.block) t row d jc sp ∧
      (X.async.copies (kvLane L (g / L.block) row d, jc)).writeBytes.isSome := by
  obtain ⟨hin, hpoll, -⟩ := hR.slot hp hX hFw
  obtain ⟨-, -, dd, s, acc, mask, hi⟩ := hR.use
  obtain ⟨c, hc, -, hcm, hfull, -⟩ := kvHandoff hp hX hFw g hin.1 ⟨t % 3, Nat.mod_lt _ (by decide)⟩
  obtain rfl := hcm hi hin
  obtain ⟨j, pcj, par, acq, sc, hjk, hje, hjn⟩ := nth_poll hpoll
  obtain ⟨i, pci, hie, hcnt, harr, -⟩ := hfull hje hjn ⟨blockLane row d, blockLane_lt row d⟩
  change X.get (kvLane L (g / L.block) row d, i) = _ at hie
  change ((X.tr (kvLane L (g / L.block) row d)).take i).countP _ = _ at hcnt
  change X.async.arrived (kvLane L (g / L.block) row d, i) = true at harr
  obtain ⟨hyc, hyw, hyl⟩ := kvLane_spec (L := L) hp (c := g / L.block) (row := row) (d := d)
  set y := kvLane L (g / L.block) row d with hy
  have hie' : X.get (y, i) = some ⟨pci, .asyncArrive (obj L y (32 + 8 * (t % 3))) true⟩ := by
    rw [obj_cta hyc]; exact hie
  have hcnt' : ((X.tr y).take i).countP (arriveOnTo (obj L y (32 + 8 * (t % 3)))) = t / 3 := by
    rw [obj_cta hyc]; exact hcnt
  have hcp := ld_arr_copies hp hX hFw hyw ⟨t % 3, Nat.mod_lt _ (by decide)⟩ hie' hcnt'
  simp only at hcp
  have htt : 3 * (t / 3) + t % 3 = t := Nat.div_add_mod t 3
  rw [htt] at hcp
  have hn : 2 * (row / 8) + d / 64 < 32 := by omega
  obtain ⟨jc, ⟨pcc, kd⟩, hjc, hge, hpe, hce⟩ := exists_nthEv (X := X) (g := y) (k := i)
    (p := cpCopy) (n := 32 * t + (2 * (row / 8) + d / 64)) (by omega)
  cases kd <;> simp [cpCopy] at hpe
  rename_i sp
  obtain ⟨-, hC⟩ := copy_row hp hX hFw (i := (y, jc)) ⟨_, hge⟩
  simp only at hC
  have hpk : pkt X y jc = t := by unfold pkt; omega
  refine ⟨jc, sp, ⟨⟨pcc, hge⟩, hC, hce, ?_⟩, ?_⟩
  · obtain ⟨i', j', hij, hdst⟩ := hC.dst
    rw [hce] at hij
    have h1 := i'.isLt
    have h2 := j'.isLt
    have e1 : i'.val = row / 8 := by omega
    have e2 : j'.val = d / 64 := by omega
    rw [hdst, hpk, hyc]
    simp only [Loader.cpAddr, e1, e2, hyl, kvBase]
  · obtain ⟨-, -, -, harrOk⟩ := hX.tma
    have ht : TracksCpAsync X (y, jc) (y, i) := ⟨rfl, hjc, ⟨sp, ⟨_, hge⟩, hC.grp⟩, _, true, ⟨_,
        hie⟩⟩
    exact (harrOk (y, i) harr).2 _ ht

/-- The copies of one byte of one packet are one. -/
theorem kv_copy_unique {y jc pc y' jc' pc' : Nat} {sp sp' : AsyncCopy.Spec} {l : Loc}
    (hcp : X.get (y, jc) = some ⟨pc, .copy sp⟩) (hcp' : X.get (y', jc') = some ⟨pc', .copy sp'⟩)
    (hc : sp.dst.Covers l) (hc' : sp'.dst.Covers l) (hpk : pkt X y jc = pkt X y' jc') :
    (y, jc) = (y', jc') := by
  obtain ⟨hy, hC⟩ := copy_row hp hX hFw (i := (y, jc)) ⟨_, hcp⟩
  obtain ⟨hy', hC'⟩ := copy_row hp hX hFw (i := (y', jc')) ⟨_, hcp'⟩
  simp only at hy hC hy' hC'
  have hb := hp.block
  obtain ⟨i, j, hij, hd⟩ := hC.dst
  obtain ⟨i', j', hij', hd'⟩ := hC'.dst
  have hcl := Loader.rowCol_lt _ (Nat.mod_lt (y % L.block) (show 0 < 64 by decide))
  have hcl' := Loader.rowCol_lt _ (Nat.mod_lt (y' % L.block) (show 0 < 64 by decide))
  have hi := i.isLt
  have hi' := i'.isLt
  have hj := j.isLt
  have hj' := j'.isLt
  obtain ⟨-, c2, c3, c4⟩ := hc
  obtain ⟨-, d2, d3, d4⟩ := hc'
  rw [hd] at c2 c3 c4
  rw [hd'] at d2 d3 d4
  simp only [Loader.cpAddr] at c2 c3 c4 d2 d3 d4
  rw [← hpk] at d3 d4
  have hcta : y / L.block = y' / L.block := c2.symm.trans d2
  have hcol : Loader.rowCol (y % L.block % 64) = Loader.rowCol (y' % L.block % 64) := by omega
  have hlane := Loader.rowCol_inj _ (Nat.mod_lt _ (by decide)) _ (Nat.mod_lt _ (by decide)) hcol
  have hyy : y = y' := by
    simp only [Prologue.warpIndex, hb] at hy hy' hlane hcta
    omega
  subst hyy
  have hcnt : ((X.tr y).take jc).countP cpCopy = ((X.tr y).take jc').countP cpCopy := by
    unfold pkt at hpk
    omega
  rw [nthEv_unique (p := cpCopy) hcp rfl hcp' rfl hcnt]

omit hX hFw in
/-- **A copy covers the bytes of its element.** -/
theorem KvCp.covers {c t row d jc z : Nat} {sp : AsyncCopy.Spec} (h : KvCp L X c t row d jc sp)
    (hz : z < 2) : sp.dst.Covers (blockLoc c (kvBase L (t % 3)) row d z) ∧
      (blockLoc c (kvBase L (t % 3)) row d z).addr = sp.dst.loc.addr + (2 * (d % 64) + z) % 16 := by
  have hs := hp.shared.1
  have ha := blockAddr_eq (base := kvBase L (t % 3)) (row := row) (d := d) (z := z)
    (by unfold kvBase; omega) hz
  rw [h.dst]
  refine ⟨⟨rfl, rfl, ?_, ?_⟩, ha⟩ <;> simp only [ha] <;> omega

/-- **The write that a K/V operand byte reads, and the order of every other write of the byte**:
before that write, or after the read. -/
theorem kv_write_order {t row d z idx : Nat} (hR : KvRead L X g k t) (hrow : row < 128)
    (hd : d < 128) (hz : z < 2)
    (hcov : AsyncCovers X (g, k) (.mmaRead true idx)
      (blockLoc (g / L.block) (kvBase L (t % 3)) row d z))
    {jc : Nat} {sp : AsyncCopy.Spec} (hC : KvCp L X (g / L.block) t row d jc sp) :
    modelCausality L X (blockLoc (g / L.block) (kvBase L (t % 3)) row d z)
        (.async (kvLane L (g / L.block) row d, jc) (.write .copy))
        (.async (g, k) (.mmaRead true idx)) ∧
      ∀ w a bs, X.MemWrites w a bs →
        a.Covers (blockLoc (g / L.block) (kvBase L (t % 3)) row d z) →
        w = .async (kvLane L (g / L.block) row d, jc) (.write .copy) ∨
        modelCausality L X (blockLoc (g / L.block) (kvBase L (t % 3)) row d z) w
          (.async (kvLane L (g / L.block) row d, jc) (.write .copy)) ∨
        modelCausality L X (blockLoc (g / L.block) (kvBase L (t % 3)) row d z)
          (.async (g, k) (.mmaRead true idx)) w := by
  set l := blockLoc (g / L.block) (kvBase L (t % 3)) row d z with hl
  obtain ⟨hyc, hyw, hyl⟩ := kvLane_spec (L := L) hp (c := g / L.block) (row := row) (d := d)
  obtain ⟨pc, hge⟩ := hC.get
  have hpk : pkt X (kvLane L (g / L.block) row d) jc = t := by
    have := hC.cnt
    unfold pkt
    omega
  obtain ⟨hdc, -⟩ := hC.covers hp hz
  have hcopyCov : ∀ {y j pc sp}, X.get (y, j) = some ⟨pc, .copy sp⟩ → LdCp L X y j sp →
      sp.dst.Covers l → AsyncCovers X (y, j) (.write .copy) l := by
    intro y j pc sp he hLd hc
    exact ⟨sp.dst, true, ⟨rfl, sp, ⟨_, he⟩, hLd.whole, rfl⟩, hc⟩
  refine ⟨kv_copy_read hp hX hFw hge hyw hC.ld hR hyc (by rw [hpk]) (by omega)
    (hcopyCov hge hC.ld hdc) hcov, ?_⟩
  intro w a bs hw hc
  have hsp : a.loc.space = .shared := hc.1.symm
  have hcta : a.loc.cta = g / L.block := hc.2.1.symm
  obtain ⟨c1, c2, c3, c4⟩ := hc
  have hlad : l.addr = blockAddr (kvBase L (t % 3)) row d z := rfl
  have hba := blockAddr_eq (base := kvBase L (t % 3)) (row := row) (d := d) (z := z)
    (by have := hp.shared.1; unfold kvBase; omega) hz
  have hcl := Loader.rowCol_lt _ (blockLane_lt row d)
  have hlo : L.sharedBase + 68608 + 32768 * (t % 3) ≤ l.addr ∧
      l.addr < L.sharedBase + 68608 + 32768 * (t % 3) + 32768 := by
    rw [hlad, hba]
    unfold kvBase
    constructor <;> omega
  have h3 := Nat.mod_lt t (show 0 < 3 by decide)
  cases sh_intent hp hX hFw hw.intent hsp with
  | allocWr hw' h =>
    exfalso
    obtain ⟨hz, hs⟩ := h
    rw [hs] at c3 c4
    simp only at c3 c4
    omega
  | @statWr gg _ _ hw' h =>
    exfalso
    obtain ⟨hz, n, hn, hs⟩ := h
    rw [hs] at c3 c4
    have hst : ∀ g, Softmax.stN L g ≤ 1 := fun g => by unfold Softmax.stN; split <;> omega
    have := hst gg
    simp only at c3 c4
    omega
  | @fstWr y j a hw' hw1 st h =>
    right; right
    obtain ⟨d', s', acc', mask', hi⟩ := hR.use.2.2
    obtain ⟨pc', he⟩ : ∃ pc', X.get (y, j) = some ⟨pc', .wr a bs⟩ := by
      rcases hw with h | ⟨old, pc', h⟩
      · exact h
      · exact (noActualRmw hX ⟨pc', h⟩).elim
    obtain ⟨hz, q, hq, ww, hww, hloc⟩ := h
    exact mma_fst hp hX hFw hw' hw1 he rfl ⟨c1, c2, c3, c4⟩ ⟨_, _, _, _, hi⟩ (by
        rw [hloc] at hcta; exact hcta.symm) hcov
  | @rowCp y j pc' sp' hy he h =>
    have hyc' : y / L.block = g / L.block := by
      obtain ⟨i', j', -, hd'⟩ := h.dst
      rw [hd'] at hcta
      exact hcta
    have hs3 : pkt X y j % 3 = t % 3 := by
      obtain ⟨off, ho, hlo'⟩ := copy_slot h (l := l) ⟨c1, c2, c3, c4⟩
      have hadd := congrArg Loc.addr hlo'
      simp only at hadd
      have := Nat.mod_lt (pkt X y j) (show 0 < 3 by decide)
      omega
    have hcv := hcopyCov he h ⟨c1, c2, c3, c4⟩
    rcases Nat.lt_trichotomy (pkt X y j) t with hlt | heq | hgt
    · right; left
      exact kv_copy_copy hp hX hFw he hge hy h hyw hC.ld (hyc'.trans hyc.symm) (by rw [hpk, hs3])
        (by omega) ⟨c1, c2, c3, c4⟩ hcv (hcopyCov hge hC.ld hdc)
    · left
      have := kv_copy_unique hp hX hFw he hge ⟨c1, c2, c3, c4⟩ hdc (by rw [hpk, heq])
      rw [this]
    · right; right
      exact kv_read_copy hp hX hFw he hy h hR hyc' hs3 hgt hcov hcv
  | tmaWr _ _ hz _ _ j hlo' hhi' =>
    exfalso
    have := tload_off_apart j
    omega

/-- **The byte a K/V operand byte is**: the copy's write of it. -/
theorem kv_operand {t row d z idx : Nat} {dd : Nat} {s : OperandSpec} {acc : Bool}
    {mask : List Nat} {ops : AsyncCopy.MmaOperands} (hR : KvRead L X g k t)
    (hi : X.MmaIssue (g, k) dd s acc mask) (hops : X.async.mmaOperands (g, k) = some ops)
    (hrow : row < 128) (hd : d < 128) (hz : z < 2)
    (hbl : s.byteLoc .b idx = some (blockLoc (g / L.block) (kvBase L (t % 3)) row d z)) :
    ∃ jc sp bs, KvCp L X (g / L.block) t row d jc sp ∧
      (X.async.copies (kvLane L (g / L.block) row d, jc)).writeBytes = some bs ∧
      ops.b[idx]? = some (bs[(2 * (d % 64) + z) % 16]?) := by
  obtain ⟨jc, sp, hC, hw⟩ := kv_copy_exists hp hX hFw hR hrow hd
  obtain ⟨bs, hbs⟩ := Option.isSome_iff_exists.mp hw
  refine ⟨jc, sp, bs, hC, hbs, ?_⟩
  obtain ⟨obs, hrd, hob⟩ := hX.tma.2.1.mma_read_exists (isB := true) hi hops hbl
  simp only [↓reduceIte] at hob
  have hcov : AsyncCovers X (g, k) (.mmaRead true idx)
      (blockLoc (g / L.block) (kvBase L (t % 3)) row d z) := mma_covers hi hbl
  obtain ⟨hv, horder⟩ := kv_write_order hp hX hFw hR hrow hd hz hcov hC
  obtain ⟨pc, hge⟩ := hC.get
  have hwr : X.MemWrites (.async (kvLane L (g / L.block) row d, jc) (.write .copy)) sp.dst bs :=
    ⟨sp, ⟨_, hge⟩, hC.ld.whole, rfl, hbs⟩
  obtain ⟨hdc, hadd⟩ := hC.covers hp hz
  have hval := read_byte_of_ordered_reuse hX hrd.memReads (k := 0) (by exact Nat.zero_lt_succ 0)
    hwr (by simpa only [Loc.at, Nat.add_zero] using hdc)
    (by simpa only [Loc.at, Nat.add_zero] using hv)
    (by simpa only [Loc.at, Nat.add_zero] using horder)
  simp only [Loc.at, Nat.add_zero, List.getElem?_cons_zero, Option.some.injEq] at hval
  rw [hob, hval, wbyte]
  congr 1
  rw [hadd, Nat.add_sub_cancel_left]

end

end
end PTX.Kernels.TmlFa4Fwd.Proof.Values
