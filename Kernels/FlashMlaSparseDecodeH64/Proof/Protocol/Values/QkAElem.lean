-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.UbBefore
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Launch
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.QueryTile
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Query.CpValue
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.TmemRace.ASource
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.QkSource
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.TensorSrc
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Grid
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.QkAEx
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Result.Gemm
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.CpAddr
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.CpOnce
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.QFill
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.QLoadSpec
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.QWait
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Shared.DqClass
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.TmemRace.Writers
import Lemmas.Async.ReadReuse
import Lemmas.Flow.NthEv
import Lemmas.Kit.CpWord
import Lemmas.Tcgen05.TcMmaIdealEval
import Lemmas.Tensor.TensorReadSources

@[expose] public section

/-! # The A elements of a QK MMA are the query values

Element `t` of row `r` of the A operand of a done QK MMA `k` decodes (`idealMmaElement`) to the
number `q e q h f` of `Pre`'s query tensor, head `h = r % 64`, feature
`f = 128 (k / 4) + 64 (r / 64) + 16 (k % 4) + t`, of the MMA's CTA (`qk_a_elem`): lane `h` of
the Tensor Memory copy holds the features `128 (k / 4) + 16 (k % 4) + t`, lane `64 + h` those
`64` higher. -/

/-! # The A operand bytes of a QK MMA are the query bytes

The A byte `32 r + 2 t + z` of QK MMA `k` (row `r < 128`, element `t < 16`, byte `z < 2`) is the
byte `z` of the bf16 value of head `r % 64` and feature `128 (k / 4) + 64 (r / 64) + 16 (k % 4) +
t` of the query of its CTA (`qk_a_byte`). The byte is the one of the word its read source wrote
(`AReadOk`), the word of copy `k` (the only writer of the cell, `writer_cases`), which is four
bytes of the query tile (`word_byteAt`, `cp_q_byte`). -/

/-! # The bytes a query copy reads are the query values

Source byte `32 r + 2 t + z` of copy `k` (row `r < 128` of the 128-lane copy, element `t < 16`,
byte `z < 2`) is the byte `z` of the bf16 value `q e q h f` of head `h = r % 64` and feature
`f = 128 (k / 4) + 64 (r / 64) + 16 (k % 4) + t` (`cp_q_byte`): the byte of the query tensor load
that wrote it (`q_tload_byte`), once the copy has read it. -/

/-! # The bytes a query load writes

A notified query load `a` of the MMA lane (`mma_qLoad_spec`) has written, for each slot
`(x, y, z)` (feature `x < 64` of head `y < 64`, byte `z < 2`), the byte `z` of the bf16 value
`q (ctaid.y) (ctaid.x) y (64 a + x)` of `Pre`'s query tensor (`q_tload_byte`): the global byte
is in bounds, `Pre` initializes it and no write covers it (`load_source`). Its shared byte is
the swizzled linear byte of that head and feature (`QueryTile.linear`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX TensorDescriptor

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **A query load's slot byte**: for a slot `(x, y, z)` the load writes (`writeLoc` is some
location `l`) with the recorded byte `b`, the load's index `a`, the swizzled shared byte of head
`y`, feature `64 a + x`, and `b` is byte `z` of the query value there. -/
theorem q_tload_byte (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hnu : NoUbInner L X) {g k pc al : Nat} {s : TensorCopy.Spec}
    {o : TensorCopy.Observation} (he : X.get (g, k) = some ⟨pc, .tensorIssue al s⟩)
    (hat : MbarRow.MmaAt L g pc) (ho : X.tensor (g, k) = some o) {x y z : Nat} {l : Loc} {b : Byte}
    (hl : TensorCopy.writeLoc s x y z = some l) (hb : TensorCopy.writeByte o x y z = some b) :
    ∃ a < 8, x < 64 ∧ y < 64 ∧ z < 2 ∧
      l = ⟨.shared, g / L.block,
        TensorSwizzle.offset .b128 0 (QueryTile.linear L.sharedBase y (64 * a + x) z)⟩ ∧
      b = (Value.float .bf16 (P.q (ctaidY L g) (ctaidX L g) y (64 * a + x))).byteAt z := by
  obtain ⟨a, ha, hmap, hsb, hrows, horg⟩ := mma_qLoad_spec hp hX hFw he hat
  obtain ⟨⟨addr, pc', hiss⟩, -, -⟩ := hX.tensor _ o ho
  rw [he] at hiss
  obtain ⟨-, hk⟩ := Event.mk.inj (Option.some.inj hiss)
  obtain ⟨hal, hs⟩ := Kind.tensorIssue.inj hk
  subst hal hs
  have hissue : X.TensorIssue (g, k) al o.spec := ⟨pc, he⟩
  obtain ⟨hcx, hcy⟩ := ctaid_lt hp g
  obtain ⟨hx, hy, hz⟩ := QueryTile.q_bounds hmap hl
  have hwl := QueryTile.q_writeLoc (cta := g / L.block) hmap hsb (shared_base_128 hp) hx hy hz
  have hrl := QueryTile.q_readLoc hcx hcy ha hmap horg hrows hx hy hz
  refine ⟨a, ha, hx, hy, hz, (Option.some.inj (hl.symm.trans hwl)), ?_⟩
  have hin := hp.qInput (ctaidY L g) hcy (ctaidX L g) hcx y hy (64 * a + x) (by omega) z hz
  have hsl : ∃ slot, TensorTransfer.slotAt o.spec.descriptor x y z = some slot ∧
      TensorCopy.source o.spec slot = .global
        (P.qBase + 2 * (((ctaidY L g * P.s_q + ctaidX L g) * 64 + y) * 512 + (64 * a + x)) +
          z) := by
    rw [TensorCopy.readLoc_source] at hrl
    cases hsl : TensorTransfer.slotAt o.spec.descriptor x y z with
    | none => simp [hsl] at hrl
    | some slot =>
      refine ⟨slot, rfl, ?_⟩
      cases hsrc : TensorCopy.source o.spec slot with
      | global ad => simp [hsl, hsrc] at hrl; rw [← hrl]
      | fill _ _ _ => simp [hsl, hsrc] at hrl
  obtain ⟨slot, -, hsrc⟩ := hsl
  obtain ⟨-, hnw⟩ := load_source hp hX hFw hnu hissue hsrc
  exact tensor_writeByte_of_initial hX ho hissue hrl hb
    (value := (Value.float .bf16 (P.q (ctaidY L g) (ctaidX L g) y (64 * a + x))).byteAt z)
    (by simpa only [Loc.at, Nat.add_assoc] using hin) hnw

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow PTX.MbarRing PTX.AsyncCopy MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
  (hR : MbarRows P L X) (hI : InitRows L X) (hB : Bar0Rows L X) (hnu : NoUbInner L X)
include hp hX hFw hR hI hB hnu

/-- **A query copy's source byte is the query value's byte**: the copy `k` of the lane (its source
descriptor is `keyDesc S k`) has read, for source byte `32 r + 2 t + z`, the byte `z` of the bf16
value of head `r % 64` and feature `128 (k / 4) + 64 (r / 64) + 16 (k % 4) + t` of the query of
its CTA. -/
theorem cp_q_byte {g iC pc k r t z : Nat} {c : TcCopy.Spec}
    (hC : X.get (g, iC) = some ⟨pc, .tc (.cp c)⟩) (hk : k < 16)
    (hsrc : c.src = MmaFoot.keyDesc L.sharedBase k) {operands : MmaOperands}
    (hop : X.async.mmaOperands (g, iC) = some operands) (hr : r < 128) (ht : t < 16) (hz : z < 2) :
    operands.a[32 * r + 2 * t + z]? = some (some
      ((Value.float .bf16 (P.q (ctaidY L g) (ctaidX L g) (r % 64)
        (QueryTile.feature k r t))).byteAt z)) := by
  have hat : MmaAt L g pc := cp_mmaAt hp hX hFw hC
  obtain ⟨-, hsh, -, hct⟩ := mma_cp_spec hp hX hFw hC ⟨hat.2.1, hat.2.2⟩
  have hbl : TcCopy.byteLoc c.shape c.src (g / L.block) (32 * r + 2 * t + z) =
      some ⟨.shared, g / L.block, TensorSwizzle.offset .b128 0
        (QueryTile.linear L.sharedBase (r % 64) (QueryTile.feature k r t) z)⟩ := by
    rw [hsh, hsrc]
    exact QueryTile.qcopy_byteLoc hr ht hz
  rw [hsh, hsrc] at hbl
  have hB128 := shared_base_128 hp (L := L)
  obtain ⟨hls, hlc, hlo, hhi⟩ := MmaFoot.copy_foot hB128 hk hbl
  generalize hl : (⟨.shared, g / L.block, TensorSwizzle.offset .b128 0
    (QueryTile.linear L.sharedBase (r % 64) (QueryTile.feature k r t) z)⟩ : Loc) = l at *
  have hloc : MemRow.LocIn L (g / L.block) (.dequant 0) l :=
    ⟨hls, hlc, by simp only [Region.lo]; omega, by simp only [Region.lo, Region.size]; omega⟩
  have hidx : 32 * r + 2 * t + z < 4096 := by omega
  have hf : X.MmaFootprint (g, iC) false (32 * r + 2 * t + z) l := by
    refine Or.inr ⟨c, 0, g / L.block, ⟨pc, hC⟩, rfl, by rw [hct]; rfl, ?_, ?_⟩
    · rw [hsh]
      simp only [TcCpShape.sourceBytes, TcCpShape.rows, TcCpShape.rowBytes]
      omega
    · rw [hsh, hsrc]
      simp only [TcCpShape.sourceBytes, TcCpShape.rows, TcCpShape.rowBytes]
      rw [Nat.mod_eq_of_lt (by omega)]
      exact hbl
  obtain ⟨bo, hoB⟩ := cp_operand_byte hp hX hFw hR hI hB (c := c) ⟨pc, hC⟩ hop
    (k := 32 * r + 2 * t + z) (by rw [hct, hsh]; simp only [List.length_singleton,
      TcCpShape.sourceBytes, TcCpShape.rows, TcCpShape.rowBytes]; omega)
  have hlane : g = mmaLane L X (g / L.block) :=
    laneOn_eq (mmaOne hp hX hFw) hC (fun _ h => by cases h) ⟨hat, mma_cp_on hp hX hFw hC hat⟩
  obtain ⟨jw, pcw, p, acq, sc, hjf, hpoll, -⟩ := UnitHandoff.exists_poll
    (m := mbarLoc L (g / L.block) .qTma) (h := g) (f := iC) (c := 0)
    (mma_cp_qWait hp hX hFw hC hat).ge
  have hw4 : warp L g = 4 := hat.1
  generalize hc : g / L.block = c' at *
  subst hlane
  obtain ⟨iT, pcT, al, x, y, j, s, bT, hT, hwl, hW⟩ :=
    q_tload_write hp hX hFw hR hI hB hpoll hw4 hc hloc
  have hatT := mma_qLoad_at hp hX hFw hw4 hT
  have hq := mma_cp_qWait hp hX hFw hC hat
  have hcov : Acc.Covers { loc := l, size := 1 } l :=
    Acc.covers_at (k := 0) (show 0 < 1 by decide)
  have hrd : X.MemReads (.async (mmaLane L X c', iC) (.mmaRead false (32 * r + 2 * t + z)))
      { loc := l, size := 1 } [some bo] := ⟨some bo, ⟨hf, operands, hop, hoB⟩, rfl, rfl⟩
  have hprior := q_tload_after hp hX hFw hR hI hB hT hatT hC hq ⟨_, true, hW.intent, hcov⟩
    (q := .mmaRead false (32 * r + 2 * t + z)) ⟨_, false, ⟨rfl, rfl, hf⟩, hcov⟩
  have horder : ∀ w a bs, X.MemWrites w a bs → a.Covers l →
      w = .async (mmaLane L X c', iT) (.write (.load x y j)) ∨
        modelCausality L X l w (.async (mmaLane L X c', iT) (.write (.load x y j))) ∨
        modelCausality L X l (.async (mmaLane L X c', iC) (.mmaRead false (32 * r + 2 * t + z)))
          w := by
    intro w a bs hw hcw
    cases hcl : dq_classify hp hX hFw hw.intent hcw hloc with
    | dq hW' hat' hcov' hc' =>
      exact .inr (.inr (q_cp_dq hp hX hFw hR hI hB hC hat hf hls hW' hat' hcov'
        (hc'.trans hc.symm)))
    | stage _ _ hr _ _ _ => exact absurd hr (by decide)
    | tload _ hT' hatT' hrl hc' =>
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ :=
        q_tload_ww hp hX hFw hT hatT hwl hT' hatT' hrl (hc.trans hc'.symm)
      exact .inl rfl
  have hrb := read_byte_of_ordered_reuse hX hrd (k := 0) Nat.zero_lt_one hW
    (by simpa [Loc.at] using hcov) (by simpa [Loc.at] using hprior)
    (fun w a bs hw' hc' => by simpa [Loc.at] using horder w a bs hw' (by simpa [Loc.at] using hc'))
  have hbo : some bo = some bT := by simpa [wbyte, Loc.at] using hrb
  obtain ⟨o', addr, b', ho', hiss', hwl', hwb, -, hbs, -⟩ := hW
  obtain ⟨pc', hget⟩ := hiss'
  rw [hT] at hget
  obtain ⟨-, hk'⟩ := Event.mk.inj (Option.some.inj hget)
  obtain ⟨-, hs⟩ := Kind.tensorIssue.inj hk'
  subst hs
  have hbb : bT = b' := List.singleton_inj.mp hbs
  obtain ⟨a', ha', hx, hy, hz', hl', hb'⟩ := q_tload_byte hp hX hFw hnu hT hatT ho' hwl hwb
  obtain ⟨-, -, hoff⟩ := Loc.mk.inj (hl.trans hl')
  have hlin := congrArg (TensorSwizzle.offset .b128 0) hoff
  rw [TensorSwizzle.offset_involutive, TensorSwizzle.offset_involutive] at hlin
  have h3 : y = r % 64 ∧ 64 * a' + x = QueryTile.feature k r t ∧ j = z := by
    simp only [QueryTile.linear, QueryTile.feature] at hlin ⊢
    omega
  obtain ⟨rfl, hf2, rfl⟩ := h3
  rw [hoB, Option.some.inj hbo, hbb, hb', hf2]

end

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.TmRace
open PTX PTX.Flow MbarRow PTX.Kit

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- The QK pc is injective in `k`. -/
theorem qkPc_injective {k k' : Nat} (h : TmemRow.qkPc k = TmemRow.qkPc k') : k = k' := by
  simp only [TmemRow.qkPc] at h
  split_ifs at h <;> omega

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
  (hT : TmemRows P L X) (hO : MmaOne L X) (hR : MbarRows P L X) (hI : InitRows L X)
  (hB : Bar0Rows L X) (ht : Tmem.One.Tmem1Facts L X 0) (hmd : Tmem.AccessCp.AsyncDoneDealloc L X)
  (hnu : NoUbInner L X)
include hp hX hFw hT hO hR hI hB ht hmd hnu

/-- **The A operand bytes of a QK MMA**: byte `32 r + 2 t + z` of a done QK MMA `k`'s snapshot is
byte `z` of the bf16 value of the query at head `r % 64`, feature
`QueryTile.feature k r t`, of the MMA's CTA. -/
theorem qk_a_byte {g i k : Nat} {s : TcMma.OperandSpec} {mask : List Nat}
    (he : X.get (g, i) = some ⟨TmemRow.qkPc k, .tc (.mma 400 s (k != 0) mask)⟩) (hk : k < 16)
    {ops : AsyncCopy.MmaOperands} (hops : X.async.mmaOperands (g, i) = some ops)
    {r t z : Nat} (hr : r < 128) (htt : t < 16) (hz : z < 2) :
    ops.a[32 * r + 2 * t + z]? = some (some ((Value.float .bf16
      (P.q (ctaidY L g) (ctaidX L g) (r % 64) (QueryTile.feature k r t))).byteAt z)) := by
  obtain ⟨k', hk', hpc, -, -, -, hs⟩ := qk_pc hT hX he
  obtain rfl : k = k' := qkPc_injective hpc
  have hidx : 32 * r + 2 * t + z < 4096 := by omega
  obtain ⟨cell, hac⟩ := TmemRow.qk_aCell_ex hk hs hidx
  obtain ⟨-, hcell⟩ := TmemRow.qk_aCell_cell hk hs hac
  have hmma : X.MmaACell (g, i) cell := ⟨400, s, _, mask, _, _, ⟨_, he⟩, hac⟩
  obtain ⟨source, value, hsrc, hwr⟩ := a_source hp hX hFw hT hO hR hI hB ht hmd
    (cp_defined hp hX hFw hR hI hB) hmma
  have hwr0 := hwr
  obtain ⟨gs, ic⟩ := source
  obtain ⟨hcta, hcl⟩ := writer_cases hp hX hT hwr.tmemWrite
  have hcol : cell.column = 256 + 8 * k + (32 * r + 2 * t + z) % 32 / 4 := by rw [hcell]
  rcases hcl with ⟨k1, -, h1, -⟩ | ⟨b, -, hb, hb2, h1, h2⟩ |
    ⟨k1, ⟨pc', c, hk1, he', hon', haddr, hsh'⟩, h1, h2⟩ | ⟨-, h1, -⟩
  · omega
  · omega
  swap
  · omega
  obtain rfl : k1 = k := by omega
  have hr' := hon'.1.2
  have hsrcK := mma_cp_addr hp hX hFw he' hr' haddr
  have hfmt := mma_cp_fmt hp hX hFw he' hr'
  obtain ⟨-, hsh2, -, hct2⟩ := mma_cp_spec hp hX hFw he' hr'
  have hcpv : TcMma.CpValue X (gs, ic) cell value := by
    rcases hwr with h | ⟨a, vals, sh, j, ⟨pcS, hS⟩, -⟩ | h |
        ⟨_, _, ⟨⟨s2, ⟨pcS, hS⟩, -⟩, -, -, -⟩, -⟩
    · obtain ⟨d, s', acc, mask', pcM, hM⟩ := h.mmaIssue
      cases get_tc_inj he' hM
    · cases get_tc_inj he' hS
    · exact h
    · cases get_tc_inj he' hS
  obtain ⟨c0, kk, cta, opsC, row, col, lane, ⟨pc0, hC0⟩, hctk, hopC, hrow, hcolC, hlane, hcellEq,
    hword⟩ := hcpv
  obtain rfl : c0 = c := TcKind.cp.inj (get_tc_inj hC0 he')
  rw [hct2] at hctk
  obtain ⟨rfl, hctE⟩ : kk = 0 ∧ gs / L.block = cta := by
    cases kk with
    | zero => exact ⟨rfl, by simpa using hctk⟩
    | succ n => simp at hctk
  rw [hsh2] at hrow hcolC hlane hword
  rw [hsh2, haddr] at hcellEq
  simp only [TcCpShape.rows, TcCpShape.rowBytes] at hrow hcolC
  simp [TcCpShape.lanes] at hlane
  simp only [TcCopy.cell, TcCpShape.rowBytes] at hcellEq
  have e1 : (256 + 8 * k1) / 2 ^ 16 = 0 := Nat.div_eq_of_lt (by omega)
  have e2 : (256 + 8 * k1) % 2 ^ 16 = 256 + 8 * k1 := Nat.mod_eq_of_lt (by omega)
  rw [e1, e2] at hcellEq
  have hcc := hcell.symm.trans hcellEq
  simp only [TcMma.Cell.mk.injEq] at hcc
  obtain ⟨hcc1, hcc2, hcc3⟩ := hcc
  have hrowr : row = r := by omega
  have hcolr : col = (32 * r + 2 * t + z) % 32 / 4 := by omega
  rw [TcCopy.cpWord_none hfmt, Nat.zero_mul, List.drop_zero, hsh2] at hword
  have hbytes : ∀ u < 4, ∃ f x w, opsC.a.getD (row * 32 + 4 * col + u) none =
      some ((Value.float f x).byteAt w) := by
    intro u hu
    refine ⟨.bf16, P.q (ctaidY L gs) (ctaidX L gs) (r % 64)
      (QueryTile.feature k1 r ((4 * col + u) / 2)), (4 * col + u) % 2, ?_⟩
    have := cp_q_byte hp hX hFw hR hI hB hnu hC0 hk hsrcK hopC (r := r) (t := (4 * col + u) / 2)
      (z := (4 * col + u) % 2) (by omega) (by omega) (by omega)
    rw [List.getD_eq_getElem?_getD]
    rw [show row * 32 + 4 * col + u = 32 * r + 2 * ((4 * col + u) / 2) + (4 * col + u) % 2 by
      omega, this]
    rfl
  obtain ⟨hb4, hall⟩ := word_byteAt hword hbytes
  obtain ⟨f, x, w, hg, hv⟩ := hall ((32 * r + 2 * t + z) % 4) (by omega)
  have hspec := cp_q_byte hp hX hFw hR hI hB hnu hC0 hk hsrcK hopC (r := r) (t := t) (z := z)
    hr htt hz
  have hg' : opsC.a.getD (row * 32 + 4 * col + (32 * r + 2 * t + z) % 4) none =
      some ((Value.float f x).byteAt w) := hg
  rw [List.getD_eq_getElem?_getD, show row * 32 + 4 * col + (32 * r + 2 * t + z) % 4 =
    32 * r + 2 * t + z by omega, hspec, Option.getD_some] at hg'
  have hpos : (32 * r + 2 * t + z) % 4 < value.bytes := by rw [hb4]; omega
  have hread := hX.tcRead.2 (g, i) (32 * r + 2 * t + z) cell ((32 * r + 2 * t + z) % 4)
    (gs, ic) value ops ⟨400, s, _, mask, ⟨_, he⟩, hac⟩ hsrc hwr0 hops hpos
  have hsame : gs / L.block = g / L.block := by
    obtain ⟨hlo, hhi⟩ := ops_cta hp (Frame.lt_of_get hX he) (.inl rfl) hs
    rw [← hcta, hcell]
    split <;> assumption
  rw [hread, hv, Option.some.inj hg'.symm]
  simp only [ctaidX, ctaidY, ctaOf, hsame]

end

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.TmRace

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.TmRace
open PTX PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
  (hT : TmemRows P L X) (hO : MmaOne L X) (hR : MbarRows P L X) (hI : InitRows L X)
  (hB : Bar0Rows L X) (ht : Tmem.One.Tmem1Facts L X 0) (hmd : Tmem.AccessCp.AsyncDoneDealloc L X)
  (hnu : NoUbInner L X)
include hp hX hFw hT hO hR hI hB ht hmd hnu

/-- **The A element of a QK MMA** is the query value. -/
theorem qk_a_elem {g i k : Nat} {s : TcMma.OperandSpec} {mask : List Nat}
    (he : X.get (g, i) = some ⟨TmemRow.qkPc k, .tc (.mma 400 s (k != 0) mask)⟩) (hk : k < 16)
    {ops : AsyncCopy.MmaOperands} (hops : X.async.mmaOperands (g, i) = some ops)
    {r t : Nat} (hr : r < 128) (htt : t < 16) :
    Assumption.idealMmaElement (.f16 .bf16 .f32) .a ops.a r t =
      .ok (P.q (ctaidY L g) (ctaidX L g) (r % 64) (QueryTile.feature k r t)) := by
  apply Result.bf16MmaElement_of_bytes
  have h0 := qk_a_byte hp hX hFw hT hO hR hI hB ht hmd hnu he hk hops hr htt (z := 0) (by omega)
  have h1 := qk_a_byte hp hX hFw hT hO hR hI hB ht hmd hnu he hk hops hr htt (z := 1) (by omega)
  rw [show 32 * r + 2 * t + 0 = 2 * (r * 16 + t) by omega] at h0
  rw [show 32 * r + 2 * t + 1 = 2 * (r * 16 + t) + 1 by omega] at h1
  rw [TcMma.take_two h0 h1]
  rfl

end

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.TmRace
