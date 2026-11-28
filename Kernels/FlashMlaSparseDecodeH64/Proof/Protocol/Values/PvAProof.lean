-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.W0Epi
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.PvAElem
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.PvStore
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.MmaBytePair
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.MmaElem
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.PvATc
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.PStoreAt
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Value
import Lemmas.Tcgen05.TcMmaIdealEval

@[expose] public section

/-! # The A elements of the PV MMAs are numbers

`pv_a_elements` (`PvAElements X`, valid rows): the two bytes of a PV MMA's A element are two bytes
of one P store of warpgroup 0 (`pv_a_pair`); the store writes the bytes of the bf16 pair of two
probabilities (`w0_pstore_value`, from the valid trace of the lane, `W0Trace`), and a 16-bit
half of that pair is a bf16 number. -/

/-! # The two bytes of a PV MMA's A element are two bytes of one P store

The bytes `2 n` and `2 n + 1` of the A operand of a PV MMA are bytes of one 4-byte P store of
the lane that stores them (`pv_a_pair`): the stores covering the two bytes are the lane's last
stores of block `d` (`pv_a_core`), the store is 4-byte aligned (`wg0_ostAt`) and covers both. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow PTX.MbarRing MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- A 4-byte window at a multiple of 4 covers an even byte and its successor, or neither. -/
theorem covers_succ4 {ac : Acc} (h4 : ac.loc.addr % 4 = 0) (hs : ac.size = 4) {l : Loc}
    (hev : l.addr % 2 = 0) :
    (ac.Covers l ↔ ac.Covers ⟨l.space, l.cta, l.addr + 1⟩) := by
  unfold Acc.Covers Loc.InRange
  rw [hs]
  constructor <;> intro h <;> refine ⟨h.1, h.2.1, ?_, ?_⟩ <;> dsimp only at h ⊢ <;> omega

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
  (hR : MbarRows P L X) (hI : InitRows L X) (hB : Bar0Rows L X)
  (hBar : BarRows P L X)
include hp hX hFw hR hI hB hBar

/-- **The two bytes of a PV MMA's A element are bytes of one P store**: the lane `h`'s store at pc
`704 + j`, at an even offset `o` of its four bytes. -/
theorem pv_a_pair {g i pc bb n : Nat} {s : TcMma.OperandSpec} {acc : Bool} {mask : List Nat}
    {l : Loc} {ops : AsyncCopy.MmaOperands}
    (hx : X.get (g, i) = some ⟨pc, .tc (.mma bb s acc mask)⟩) (hbb : bb < 256)
    (hat : MmaAt L g pc) (hops : X.async.mmaOperands (g, i) = some ops)
    (hk : s.descriptor.kind = .f16 .bf16 .f32)
    (hd : s.a.start % 2 = 0 ∧ s.a.leading % 2 = 0 ∧ s.a.stride % 2 = 0)
    (hl : s.byteLoc .a (2 * n) = some l) :
    ∃ d h k j pcw ac bs o, (∀ jj : Fin 2, okPolls (mbarLoc L (g / L.block) (.soReady jj))
        ((X.tr g).take i) = ringUses 2 jj (d + 1)) ∧
      ((X.tr h).take k).countP (Execution.isBarId 9) = 2 * d + 2 ∧
      warp L h < 4 ∧ X.get (h, k) = some ⟨pcw, .wr ac bs⟩ ∧ pcw = 704 + j ∧
      j < 4 ∧ (o = 0 ∨ o = 2) ∧ (ops.a.drop (2 * n)).take 2 = [bs[o]?, bs[o + 1]?] ∧
      h / L.block = g / L.block ∧ ac.loc.addr + o = l.addr := by
  classical
  have hSB : L.sharedBase % 16 = 0 := by
    have := hp.sharedAlignment
    rw [← hp.sharedBase] at this
    omega
  obtain ⟨hl', hev⟩ := MmaFoot.byteLoc_pair (op := .a) hk hd hl
  obtain ⟨d, h, k, pcw, ac, bs, hdp, hw, hhw, hW, hp1, hp2, hcov, hcnt, hob, hmax⟩ :=
    pv_a_core hp hX hFw hR hI hB hBar hx hbb hat hops hl
  obtain ⟨d', h', k', pcw', ac', bs', hdp', hw', hhw', hW', hp1', hp2', hcov', hcnt', hob',
    hmax'⟩ := pv_a_core hp hX hFw hR hI hB hBar hx hbb hat hops hl'
  have hdd : d = d' := by
    have e0 := (hdp 0).symm.trans (hdp' 0)
    have e1 := (hdp 1).symm.trans (hdp' 1)
    simp only [Fin.val_zero, Fin.val_one] at e0 e1
    unfold ringUses at e0 e1
    omega
  subst hdd
  obtain ⟨el, hel, hsz, hloc⟩ := wg0_ostAt hp hX hFw hw (j := pcw - 704)
    (by omega) (by rw [show 704 + (pcw - 704) = pcw by omega]; exact hW)
  obtain ⟨el', hel', hsz', hloc'⟩ := wg0_ostAt hp hX hFw hw' (j := pcw' - 704)
    (by omega) (by rw [show 704 + (pcw' - 704) = pcw' by omega]; exact hW')
  have ha4 : ac.loc.addr % 4 = 0 := by
    rw [hloc]
    simp only [wsLoc]
    omega
  have ha4' : ac'.loc.addr % 4 = 0 := by
    rw [hloc']
    simp only [wsLoc]
    omega
  have hc1 : ac.Covers ⟨l.space, l.cta, l.addr + 1⟩ := (covers_succ4 ha4 hsz hev).1 hcov
  have hc2 : ac'.Covers l := (covers_succ4 ha4' hsz' hev).2 hcov'
  have haeq : ac.loc.addr = ac'.loc.addr := by
    obtain ⟨-, -, h1, h2⟩ := hcov
    obtain ⟨-, -, h3, h4⟩ := hcov'
    rw [hsz] at h2
    rw [hsz'] at h4
    dsimp only at h3 h4
    omega
  have hh : h = h' := by
    rw [hloc, hloc'] at haeq
    simp only [wsLoc] at haeq
    have ht : tidOf L h < 128 := MemRow.wg0_tid hw
    have ht' : tidOf L h' < 128 := MemRow.wg0_tid hw'
    have hi := MemRow.wg0Ost_inj ht ht' (k := pcw - 704)
      (k' := pcw' - 704) (by omega) (by omega) hel hel' (by omega)
    have h1 : h % L.block = h' % L.block := by
      have := hi.1
      rw [tidOf_eq hp, tidOf_eq hp, ← hp.block] at this
      exact this
    exact thread_eq h1 (hhw.trans hhw'.symm)
  subst hh
  have hkk : k' = k := le_antisymm (hmax k' ⟨pcw', ac', bs', hW', hp1', hp2', hc2, hcnt'⟩)
    (hmax' k ⟨pcw, ac, bs, hW, hp1, hp2, hc1, hcnt⟩)
  subst hkk
  obtain ⟨rfl, rfl, rfl⟩ : pcw = pcw' ∧ ac = ac' ∧ bs = bs' := by
    obtain ⟨h1, h2⟩ := Event.mk.inj (Option.some.inj (hW.symm.trans hW'))
    obtain ⟨h3, h4⟩ := Kind.wr.inj h2
    exact ⟨h1, h3, h4⟩
  obtain ⟨-, -, hlo, hhi⟩ := hcov
  rw [hsz] at hhi
  refine ⟨d, h, k', pcw - 704, pcw, ac, bs, l.addr - ac.loc.addr, hdp, hcnt, hw, hW, by omega,
    by omega, by omega, ?_, hhw, by omega⟩
  have h2 := TcMma.take_two hob hob'
  rw [h2]
  simp only [wbyte]
  rw [show l.addr + 1 - ac.loc.addr = l.addr - ac.loc.addr + 1 by omega]

end

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.TmRace
open PTX PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- The A row of a PV MMA's cell is below 128. -/
theorem pv_operandRow_lt :
    ∀ row < 64, ∀ col < 256, TcMma.operandRow MmaFoot.pvD row col < 128 := by
  decide +kernel

/-- The even-offset half of a bf16 pair's bytes is a bf16 number. -/
theorem pair_half {x y : ℝ} {o : Nat} (ho : o = 0 ∨ o = 2) :
    ∃ z : ℝ, [(Assumptions.bf16Pair x y).toBytes[o]?, (Assumptions.bf16Pair x y).toBytes[o + 1]?] =
      (Value.float .bf16 z).toBytes.map some := by
  rcases ho with rfl | rfl
  · exact ⟨x, rfl⟩
  · exact ⟨y, rfl⟩

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
  (hR : MbarRows P L X) (hI : InitRows L X) (hB : Bar0Rows L X)
  (hBar : BarRows P L X)
  (hS : ∀ i d s acc mask, X.MmaIssue i d s acc mask → TcMma.IssueShape L i d s mask)
  (hT : TmemRows P L X)
include hp hX hFw hR hI hB hBar hS hT

/-- **The A elements of one completed PV MMA are numbers** (valid rows): given the validity of the
prefix of every warpgroup-0 lane before a write with a tcgen05 path to the MMA. -/
theorem pv_a_elem_at {i : EvId}
    (hW : ∀ h k2 ev, X.get (h, k2) = some ev →
      Relation.TransGen (TcMma.TcStep L X) (h, k2) i → warp L h < 4 →
      W0Valid P.scale ((X.tr h).take k2)) :
    ∀ d s acc mask ops row col cell, X.MmaIssue i d s acc mask → X.async.mmaDone i = true →
      X.async.mmaOperands i = some ops → TcMma.writeCell s d mask row col = some cell →
      d < 256 → ∀ k < 16, ∃ x, Assumption.idealMmaElement (.f16 .bf16 .f32) .a ops.a
        (TcMma.operandRow s.descriptor row col) k = .ok x := by
  intro d s acc mask ops row col cell hi hdone hops hcell hd256 k hk16
  obtain ⟨g, j⟩ := i
  obtain ⟨pc, he⟩ := hi
  obtain ⟨hcol, hrow⟩ := writeCell_col hcell
  rcases mma_kind hT hX he with ⟨rfl, -⟩ | ⟨-, k', hk', rfl, hon, hmo⟩
  · omega
  have hD := MmaFoot.pvD_eq hmo.2.1
  have hkd := (desc_bf16 (Or.inr rfl) hmo.2.1).1
  obtain ⟨-, hvalid, -, -, ⟨-, -, -, hs1, hs2, hs3⟩, -, -, -, -, hex⟩ :=
    hS _ _ _ _ _ (show X.MmaIssue (g, j) d s acc mask from ⟨_, he⟩)
  have hr : TcMma.operandRow s.descriptor row col < 128 := by
    rw [hD] at hrow hcol ⊢
    exact pv_operandRow_lt row (by simpa [MmaFoot.pvD] using hrow) col
      (by simpa [MmaFoot.pvD] using hcol)
  have hidx : 2 * (TcMma.operandRow s.descriptor row col * 16 + k) <
      TcMma.Operand.a.bytes s.descriptor := by
    have hb : TcMma.Operand.a.bytes s.descriptor = 4096 := by
      rw [hD]
      decide
    omega
  obtain ⟨l, hl⟩ : ∃ l, s.byteLoc .a (2 * (TcMma.operandRow s.descriptor row col * 16 + k)) =
      some l := by
    rcases hex .a _ hidx with h | ⟨-, c, hc⟩
    · exact h
    · simp [TcMma.aCell, hmo.1] at hc
  obtain ⟨dd, h, k2, j2, pcw, ac, bs, o, hdp, hcnt, hw, hWe, hpcw, hj2, ho, hbytes, hhw, -⟩ :=
    pv_a_pair hp hX hFw hR hI hB hBar he (by omega) hon.1 hops hkd
      ⟨by omega, by omega, by omega⟩ hl
  have hv := hW h k2 _ hWe
    (pv_a_tc hp hX hFw hR hI hB he (by omega) hdp hWe hpcw hj2 hw hhw hcnt) hw
  obtain ⟨q, -, -, -, hbs⟩ := w0_pstore_value hp hX hFw hw hWe hj2 hpcw hv ac bs rfl
  obtain ⟨z, hz⟩ := pair_half (x := w0PWord P.scale ((X.tr h).take k2) (2 * (4 * j2 + q)))
    (y := w0PWord P.scale ((X.tr h).take k2) (2 * (4 * j2 + q) + 1)) ho
  rw [← hbs] at hz
  exact ⟨z, Result.bf16MmaElement_of_bytes (hbytes.trans hz)⟩

/-- **The A elements of the completed PV MMAs are numbers** (valid rows). -/
theorem pv_a_elements (hW : ∀ g, warp L g < 4 → W0Trace P X g) : PvAElements X :=
  fun _ d s acc mask ops row col cell hi hdone hops hcell hd256 =>
    pv_a_elem_at hp hX hFw hR hI hB hBar hS hT (fun h _ _ _ _ hw => (hW h hw).take) d s acc
      mask ops row col cell hi hdone hops hcell hd256

end

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.TmRace
