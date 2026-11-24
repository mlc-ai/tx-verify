-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.FactsProof
public import Kernels.TmlFa4Fwd.Proof.Protocol.Values.Def
public import Core.Tc.TcMmaSafety
public import Lemmas.Order.GuardOrder
import Kernels.TmlFa4Fwd.Proof.Lib.SmemElements
import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.ASource
import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.AccSource
import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.Handoffs
import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.Issue
import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.LoadSource
import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.SourceFacts
import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.Words
import Lemmas.Tcgen05.MmaOperandObservations
import Lemmas.Tcgen05.TcMmaACell
import Lemmas.Tcgen05.TcMmaF16Sum
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The values of the MMAs' results

A completed MMA read its operands, so its ideal arithmetic gives a single-precision number at every
cell it writes when its operand elements and its old value are numbers (`eval_cell`): the shared
elements are (`SmemElements`), the A elements of a PV MMA are the halves of the words its tile's
softmax stores wrote (`pv_elements`), and an old value is an earlier MMA's of the lane, pipelined
before it and so completed, or a correction store's word (`accSource`). The stores' words need the
loads that precede them, and a load that precedes an MMA in the `tcgen05` orders reads an earlier
MMA of its lane, since the orders have no cycle. So one induction along the lane gives every result
(`results`) and the loaded values (`load_f32`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Values
open PTX PTX.Proof PTX.Flow TcMma Tm

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- A completed MMA recorded its operands. -/
theorem operands_of_done (hX : Consistent L kernel Assumptions.all m X) {i : EvId}
    (hd : X.async.mmaDone i = true) : ∃ ops, X.async.mmaOperands i = some ops := by
  have hst := hX.tma.2.1.2 i hd
  cases h : X.async.mmaOperands i with
  | none => simp [AsyncCopy.Snapshot.mmaStarted, h] at hst
  | some ops => exact ⟨ops, rfl⟩

/-- An event's lane's program order, as a step of the `tcgen05` orders. -/
theorem po_step {g k k' pc : Nat} {tk : TcKind} (he : X.get (g, k) = some ⟨pc, .tc tk⟩)
    (hk : k < k') (hl : k' < (X.tr g).length) : TcStep L X (g, k) (g, k') :=
  .inl (.single (.inl (po_of_source_not_access (e := (g, k)) (f := (g, k')) rfl hk hl
    (by rw [he]; rfl))))

/-- The loads before an event that precedes another of its CTA. -/
theorem LoadsBefore.mono {e f : EvId} (h : LoadsBefore L X f) (hc : e.1 / L.block = f.1 / L.block)
    (hp : Relation.TransGen (TcStep L X) e f) : LoadsBefore L X e :=
  fun l a vals hl hlc hlp => h l a vals hl (hlc.trans hc) (hlp.trans hp)

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
include hp hX hFw

/-- **The ideal value of an MMA** whose elements of its row and column are `x` and `y`, over the
old value `prev`. -/
theorem eval_mma {i : EvId} {d : Nat} {s : OperandSpec} {acc : Bool} {mask : List Nat}
    {ops : AsyncCopy.MmaOperands} {row col : Nat} {cell : Cell}
    (hi : X.MmaIssue i d s acc mask) (hops : X.async.mmaOperands i = some ops)
    (hpos : writeCell s d mask row col = some cell) {x y : Nat → ℝ}
    (ha : ∀ k, k < 16 → Assumption.idealMmaElement (.f16 .bf16 .f32) .a ops.a row k = .ok (x k))
    (hb : ∀ k, k < 16 → Assumption.idealMmaElement (.f16 .bf16 .f32) .b ops.b col k = .ok (y k))
    {old : Option Value} {prev : ℝ}
    (hprev : Assumption.idealMmaAccumulator .f32 acc old = .ok prev) :
    eval Assumptions.all s.descriptor acc ops.a ops.b old row col =
      .ok (.float .f32 (∑ k ∈ Finset.range 16, x k * y k + prev)) := by
  obtain ⟨-, hs, -⟩ := mma_acc_at hp hX hFw hi
  obtain ⟨hv, hla, hlb⟩ := hX.mma_observation_shape hi hops
  obtain ⟨hrow, hcol⟩ := resultCell_rowcol (writeCell_resultCell hpos)
  have hk : s.descriptor.kind = .f16 .bf16 .f32 ∧ s.descriptor.ws = false ∧
      s.descriptor.negateA = false ∧ s.descriptor.negateB = false := by
    rcases hs.dsc with h | h <;> rw [h] <;> exact ⟨rfl, rfl, rfl, rfl⟩
  exact eval_sum16 (name := _) (sc := Assumptions.arithScope) rfl hk.1
    (by rw [hk.1]; exact List.mem_singleton.mpr rfl) hv hk.2.1 hk.2.2.1 hk.2.2.2
    (by rw [hla]; simp [Operand.bytes, Operand.rows, Operand.extent, hk.2.1])
    (by rw [hlb]; simp [Operand.bytes, Operand.rows, Operand.extent]) hrow hcol ha hb hprev

/-- **The A elements of a completed PV MMA are BF16 numbers**, when the words its tile's softmax
stores wrote are pairs of them. -/
theorem pv_elements {i : EvId} {d : Nat} {s : OperandSpec} {acc : Bool} {mask : List Nat}
    {ops : AsyncCopy.MmaOperands} (hi : X.MmaIssue i d s acc mask)
    (haT : s.aTmem.isSome = true) (hops : X.async.mmaOperands i = some ops) {row k : Nat}
    (hrow : row < 128) (hk : k < 16) (hst : SoftStores L X) (hld : LoadsBefore L X i) :
    ∃ x, Assumption.idealMmaElement (.f16 .bf16 .f32) .a ops.a row k = .ok x := by
  have ht := scoreFacts hp hX hFw
  have ho := oAccFacts hp hX hFw
  have hT := sourceFacts hp hX hFw
  have hH := handoffs hp hX hFw
  obtain ⟨-, hs, -⟩ := mma_acc_at hp hX hFw hi
  have hb : 2 * (row * 16 + k) < Operand.bytes .a s.descriptor := by rw [opBytes hs]; omega
  obtain ⟨⟨cell, pos⟩, hac⟩ : ∃ c, aCell s (2 * (row * 16 + k)) = some c := by
    obtain ⟨-, -, -, -, -, -, -, -, -, hsh⟩ := issueShape hp hX hFw hi
    rcases hsh .a _ hb with ⟨loc, hl⟩ | ⟨-, hc⟩
    · rw [byteLoc_a_tmem haT] at hl
      cases hl
    · exact hc
  obtain ⟨hac1, hp2, hp4⟩ := aCell_pair hac
  obtain ⟨cellO, st, hst2, hco, hO, h, kk, a, j, vals, hh, hw, hs', hj, rfl, hu⟩ :=
    pvAStore hp ht hT hH.p hi hac
  have hsrc := fun {index pos : Nat} (ha : aCell s index = some (tcDataCell32 L h a j, pos)) =>
    p_aReadSource hp ht ho hH.p hH.p2 hH.s hi hco hO ha hh hw hs' hj hu
      (sourceLive hT.live ⟨_, _, _, _, hi⟩ (.inr (.inr ⟨_, _, _, _, _, _, hi, ha⟩)))
  have hcta : h / L.block = i.1 / L.block := by
    obtain ⟨-, -, -, hA⟩ := ht.pv_polls hi hco hO
    exact (hA _ _ _ hac).2.1
  obtain ⟨x, y, h4, hxy⟩ := hst hh hw hs' (hld.mono hcta (hsrc hac).2.2.1.tcStep) vals[j]
    (List.getElem_mem hj)
  have hwr : Wrote L Assumptions.all X (h, kk) (tcDataCell32 L h a j) vals[j] :=
    .inr (.inl ⟨a, vals, _, j, hs', List.getElem?_eq_getElem hj,
      (tcDataCell_s32x32b _ _ _ _).symm⟩)
  have hb0 := hX.tcRead.2 _ _ _ _ _ _ _ ⟨_, _, _, _, hi, hac⟩ (hsrc hac) hwr hops (by omega)
  have hb1 := hX.tcRead.2 _ _ _ _ _ _ _ ⟨_, _, _, _, hi, hac1⟩ (hsrc hac1) hwr hops (by omega)
  rcases (by omega : pos = 0 ∨ pos = 2) with rfl | rfl
  · refine ⟨x, element_of_bytes (.inr rfl) fun z hz => ?_⟩
    rcases (by omega : z = 0 ∨ z = 1) with rfl | rfl
    · rw [Nat.add_zero, hb0, (hxy 0 (by omega)).1]
    · rw [hb1, (hxy 1 (by omega)).1]
  · refine ⟨y, element_of_bytes (.inr rfl) fun z hz => ?_⟩
    rcases (by omega : z = 0 ∨ z = 1) with rfl | rfl
    · rw [Nat.add_zero, hb0, ← (hxy 0 (by omega)).2]
    · rw [hb1, ← (hxy 1 (by omega)).2]

/-- **A load returns single-precision numbers** once the MMAs writing its cells that completed
before it have values. -/
theorem load_of_values {e : EvId} (hv : ∀ {a j : Nat} {x d s acc mask},
      X.MmaIssue x d s acc mask → X.MmaCell x (tcDataCell32 L e.1 a j) → DoneBefore L X x e →
      CompletedValues L Assumptions.all X x)
    {a : Nat} {vals : List Value} (hld : X.TLd e a vals .s32x32b) : F32s vals := by
  have ht := scoreFacts hp hX hFw
  have ho := oAccFacts hp hX hFw
  have hT := sourceFacts hp hX hFw
  have hH := handoffs hp hX hFw
  have hR : OReady L X := oready ht hH.s hH.o hH.route
  obtain ⟨h, i⟩ := e
  intro v hv'
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hv'
  obtain ⟨hh, h12⟩ := ht.tc_role (.inl hld)
  obtain ⟨src, value, hrs, hwr, d, s, acc, mask, hm⟩ : ∃ src value,
      ReadSource L X .ld src (h, i) (tcDataCell32 L h a j) ∧
      Wrote L Assumptions.all X src (tcDataCell32 L h a j) value ∧ IsMma X src := by
    by_cases h8 : Prologue.warpIndex L h < 8
    · exact soft_source hp hX ht ho hH.p hH.p2 hH.s hT (fun hx hc hd => hv hx hc hd) hh h8 hld hj
    · exact corr_source hp hX ht ho hH.p hR hT (fun hx hc hd => hv hx hc hd) hh (by omega) h12
        hld hj
  obtain ⟨word, hword, hcw⟩ :=
    hX.tcRead.1 _ a vals _ j src _ value hld (loadCell32 hld hj) hrs hwr
  have hres : ∃ r, value = .float .f32 r := by
    rcases hwr with h | ⟨a', vals', sh, j', hs', -⟩ | ⟨c, -, -, -, -, -, -, hcp, -⟩ |
      ⟨-, -, ⟨hsc, -⟩, -⟩
    · exact result_f32 hp hX hFw h
    · exfalso
      obtain ⟨hg, hgw⟩ := ht.tc_role (g := src.1) (i := src.2) (.inr hs')
      have := (ht.mma_cells hm).2.1
      omega
    · exact (ht.no_cp _ _ hcp).elim
    · obtain ⟨sp, hsp, -⟩ := hsc
      exact (ht.no_shift _ _ hsp).elim
  obtain ⟨r, rfl⟩ := hres
  rw [List.getElem?_eq_getElem hj, Option.some.injEq] at hword
  rw [hword]
  rcases hcw with ⟨-, rfl⟩ | ⟨hb, -⟩
  · exact ⟨r, rfl⟩
  · simp [Value.bytes, FloatFmt.bytes] at hb

/-- **Every cell of a completed MMA has a single-precision value.** -/
theorem results (hg : SyncGuarded L kernel X) (hE : ElementFacts L X) :
    ∀ k g d s acc mask row col cell, X.MmaIssue (g, k) d s acc mask →
      writeCell s d mask row col = some cell → X.async.mmaDone (g, k) = true →
      ∃ r, Result L Assumptions.all X (g, k) cell (.float .f32 r) := by
  have ht := scoreFacts hp hX hFw
  have ho := oAccFacts hp hX hFw
  have hT := sourceFacts hp hX hFw
  have hH := handoffs hp hX hFw
  have hR : OReady L X := oready ht hH.s hH.o hH.route
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro g d s acc mask row col cell hi hpos hd
  have hc : X.MmaCell (g, k) cell := ⟨_, _, _, _, _, _, hi, hpos⟩
  -- the loads of the CTA before the MMA return numbers
  have hld : LoadsBefore L X (g, k) := by
    intro f a vals hl hfc hfp
    refine load_of_values hp hX hFw ?_ hl
    intro a' j x dx sx ax mx hx hxc hdb hdx c0 ⟨d0, s0, a1, m0, r0, c0', hx0, hp0⟩
    have hxg : x.1 = g := ht.tc_one ⟨_, _, _, _, hx⟩ (.inl ⟨_, _, _, _, hi⟩) (by
      rw [mma_lead ht ⟨_, _, _, _, hx⟩ hxc]
      exact hfc)
    have hpath : Relation.TransGen (TcStep L X) x (g, k) := hdb.tcStep.trans hfp
    have hxk : x.2 < k := by
      by_contra hge
      obtain ⟨pcx, hxget⟩ := hx
      rcases Nat.lt_or_eq_of_le (Nat.le_of_not_lt hge) with hlt | heq
      · exact tcStep_acyclic hX hg _ (hpath.tail (.inl (.single (.inl
          (po_of_not_access (e := (g, k)) (f := x) hxg.symm hlt (len_of_get hxget)
            (by rw [hxget]; rfl))))))
      · have hx' : x = (g, k) := Prod.ext hxg heq.symm
        subst hx'
        exact tcStep_acyclic hX hg _ hpath
    obtain ⟨xg, xk⟩ := x
    simp only at hxg hxk
    subst hxg
    obtain ⟨r, hr⟩ := ih xk hxk xg d0 s0 a1 m0 r0 c0' c0 hx0 hp0 hdx
    exact ⟨_, hr⟩
  obtain ⟨ops, hops⟩ := operands_of_done hX hd
  -- the ideal arithmetic over a number
  have heval : ∀ {old : Option Value} {prev : ℝ},
      Assumption.idealMmaAccumulator .f32 acc old = .ok prev →
      ∃ r, eval Assumptions.all s.descriptor acc ops.a ops.b old row col =
        .ok (.float .f32 r) := by
    intro old prev hprev
    obtain ⟨-, hs, -⟩ := mma_acc_at hp hX hFw hi
    obtain ⟨hrow, hcol⟩ := resultCell_rowcol (writeCell_resultCell hpos)
    have hmn : s.descriptor.m = 128 ∧ s.descriptor.n = 128 := by
      rcases hs.dsc with h | h <;> rw [h] <;> exact ⟨rfl, rfl⟩
    rw [hmn.1] at hrow
    rw [hmn.2] at hcol
    have hA : ∀ k, k < 16 →
        ∃ x, Assumption.idealMmaElement (.f16 .bf16 .f32) .a ops.a row k = .ok x := by
      intro k hk
      cases haT : s.aTmem with
      | none => exact (hE.smem hi hd hops hrow hk).2 haT
      | some _ => exact pv_elements hp hX hFw hi (by simp [haT]) hops hrow hk hE.soft hld
    have hB : ∀ k, k < 16 →
        ∃ y, Assumption.idealMmaElement (.f16 .bf16 .f32) .b ops.b col k = .ok y :=
      fun k hk => (hE.smem hi hd hops hcol hk).1
    choose! x hx using hA
    choose! y hy using hB
    exact ⟨_, eval_mma hp hX hFw hi hops hpos hx hy hprev⟩
  cases acc
  · obtain ⟨r, hr⟩ := heval (old := none) (prev := 0) rfl
    exact ⟨r, .overwrite hi hpos hops hr⟩
  obtain ⟨src, hsrc, ⟨hs1, hs2, hcs⟩ | ⟨hgl, h8, h12, a, vals, sh, j, hst, hj, hceq⟩⟩ :=
    accSource hp ht ho hT hH.s hH.p hH.p2 hR hi hc
  · obtain ⟨g', k'⟩ := src
    simp only at hs1 hs2
    subst hs1
    obtain ⟨dK, sK, aK, mK, rowK, colK, hiK, hposK⟩ := id hcs
    obtain ⟨hacc, hw⟩ := hT.same_write hiK hi rfl hcs hc
    have hds : X.async.mmaDone (g', k') = true :=
      hX.mmaCompletion (g', k') (g', k) ⟨rfl, hs2, mma_pipe ht hiK hi rfl hs2 hacc,
        _, _, _, _, _, _, _, _, hiK, hi, hw, rowK, colK, cell, hposK⟩ hd
    obtain ⟨r', hr'⟩ := ih k' hs2 g' dK sK aK mK rowK colK cell hiK hposK hds
    obtain ⟨r, hr⟩ := heval (old := some (.float .f32 r')) (prev := r') rfl
    exact ⟨r, .accumulate hi hpos hops hr' hsrc hr⟩
  · obtain ⟨g', k'⟩ := src
    simp only at hgl h8 h12 hst hceq
    obtain rfl := ht.tc_shape (.inr hst)
    have hcta : g' / L.block = g / L.block := by
      rw [tcDataCell_s32x32b] at hceq
      rw [mma_lead ht ⟨_, _, _, _, hi⟩ hc, hceq]
      rfl
    obtain ⟨r', hr'⟩ := hE.corr hgl h8 h12 hst (hld.mono hcta hsrc.2.2.1.tcStep) vals[j]
      (List.getElem_mem hj)
    obtain ⟨r, hr⟩ := heval (old := some (.float .f32 r')) (prev := r') rfl
    exact ⟨r, .accumulateStored hi hpos hops (old := .float .f32 r') ⟨a, vals, _, j, hst,
      by rw [← hr']; exact List.getElem?_eq_getElem hj, hceq⟩ hsrc hr⟩

/-- **Every completed MMA's cells have values.** -/
theorem completedValues (hg : SyncGuarded L kernel X) (hE : ElementFacts L X) {i : EvId} {d : Nat}
    {s : OperandSpec} {acc : Bool} {mask : List Nat} (_hi : X.MmaIssue i d s acc mask) :
    CompletedValues L Assumptions.all X i := by
  intro hd cell ⟨d, s, acc, mask, row, col, hi, hpos⟩
  obtain ⟨r, h⟩ := results hp hX hFw hg hE i.2 i.1 d s acc mask row col cell hi hpos hd
  exact ⟨_, h⟩

/-- **Every Tensor Memory load returns single-precision numbers.** -/
theorem load_f32 (hg : SyncGuarded L kernel X) (hE : ElementFacts L X) {e : EvId} {a : Nat}
    {vals : List Value} (hld : X.TLd e a vals .s32x32b) : F32s vals :=
  load_of_values hp hX hFw (fun hx _ _ => completedValues hp hX hFw hg hE hx) hld

/-- **The loads before any event return numbers.** -/
theorem loadsBefore (hg : SyncGuarded L kernel X) (hE : ElementFacts L X) (e : EvId) :
    LoadsBefore L X e := fun _ _ _ hl _ _ => load_f32 hp hX hFw hg hE hl

end

end
end PTX.Kernels.TmlFa4Fwd.Proof.Values
