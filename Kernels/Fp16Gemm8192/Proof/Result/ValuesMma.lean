-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Result.ValuesTile
public import Kernels.Fp16Gemm8192.Proof.Support.Numerics
public import Lemmas.Tcgen05.MmaOperandObservations

@[expose] public section

/-! # The values of the MMAs

An MMA of K step `j` at slot `s` of its task's block `M % 128` (its thread's commits `M`) is the
task's MMA number `4 (M % 128) + j`; its operands are the elements of the task's tile at K index
`64 (M % 128) + 16 j + kk` (`operand_value`): the copy its operand bytes come from
(`OperandValues`) is the loader's load of the same block of the same task
(`ThreadFacts.loader_block`, `ThreadFacts.tensor_issue` against `ThreadFacts.mma_block`), whose tile
is the task's (`taskTile_agree`). By induction along the thread, a completed MMA leaves at cell
`(row, col)` the prefix of the dot product over its task's MMAs so far (`mma_value`): the task's
first MMA overwrites, and an accumulating MMA adds its 16 terms to the previous MMA of its task, its
accumulator source (`MmaAccSources`, `ThreadFacts.mma_prev`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Flow TcMma

noncomputable section

namespace Result

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The cells an MMA of a warp writes do not depend on its stage or K step. -/
theorem writeCell_step (L : Launch) (cta w sl j sl' j' d : Nat) (mask : List Nat) (row col : Nat) :
    writeCell (InputRing.mmaSpec L cta w sl j) d mask row col =
      writeCell (InputRing.mmaSpec L cta w sl' j') d mask row col := rfl

/-- The row of the output an MMA's accumulator row `row` is, in tile row `m`. -/
def accRow (m w row : Nat) : Nat := outputRow m (row / 128) (w % 2) (row % 128)

/-- **An MMA's operand elements.** Element `(row, kk)` of an MMA of K step `jj` at block `M % 128`
of task `M / 128` with tile `(tm, tn)` is `A`'s element of row `accRow tm w row`, or `B`'s element
of row `256 tn + row`, at K index `64 (M % 128) + 16 jj + kk`. -/
theorem operand_value (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X)
    (hov : OperandValues P L X) (hag : AllResponsesAgree L X) {g km pc dst : Nat}
    {sp : OperandSpec} {acc : Bool} {mask : List Nat} {m : Mma.D} {s jj : Fin 4}
    {ops : AsyncCopy.MmaOperands}
    (he : X.get (g, km) = some ⟨pc, .tc (.mma dst sp acc mask)⟩)
    (hσ : Frame.stateAt (code L) X g km = some (some (.inr (.mma m)))) (hs : m.site = .mma s jj)
    (hops : X.async.mmaOperands (g, km) = some ops) {tm tn : Nat}
    (htile : TaskTile L X (g / L.block / 2) (mmaCount L g ((X.tr g).take km) / 128) tm tn)
    (isB : Bool) {row kk : Nat} (hrow : row < 256) (hkk : kk < 16) :
    Assumption.idealMmaElement (.f16 .f16 .f32) (if isB then .b else .a)
        (if isB then ops.b else ops.a) row kk =
      .ok ((if isB then P.b else P.a)
        (if isB then 256 * tn + row else accRow tm (g % L.block / 32) row)
        (64 * (mmaCount L g ((X.tr g).take km) % 128) + 16 * jj.val + kk)) := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨gw, kw, pcw, alw, spw, lw, bw, jw, hgw, hσw, hsw, hcta, hslot, hjw, hcnt, hval⟩ :=
    hov g km pc dst sp acc mask m s jj ops he hσ hs hops isB row kk hrow hkk
  have hgwl := Frame.lt_of_get hX hgw
  obtain ⟨hlc, hq8, hq128, hrank, htw, hm16, hn32, horig, -⟩ := ht.loader_block hgwl hgw hσw hsw
  obtain ⟨l', b', j', hd', hs', -, ⟨base, cls, origin, hspw, -⟩, -, hic⟩ :=
    ht.tensor_issue hgwl hgw hσw rfl
  simp only [Sum.inr.injEq, Prologue.Role.loader.injEq] at hd'
  subst hd'
  rw [hsw] at hs'
  simp only [Loader.Site.load.injEq] at hs'
  obtain ⟨rfl, rfl⟩ := hs'
  obtain ⟨hMq, hq4, hcm, -, -⟩ := ht.mma_block hg he hσ hs
  have hcl : gw / L.block / 2 = g / L.block / 2 := by omega
  have hfull : Loader.fullOf L gw (InputRing.slotOf bw) = InputRing.fullLoc L (g / L.block / 2) s :=
    by
    simp only [Loader.fullOf, hcl, hslot]
  rw [hfull, hcnt, hcm] at hic
  simp only [Loader.emptyOf] at hic
  rw [hrank] at hic
  have hsb : (InputRing.slotOf bw).val = bw.val % 4 := rfl
  rw [hslot] at hsb
  have hb8 := bw.isLt
  have hs4 := s.isLt
  -- the load's block is the MMA's block
  have hM : mmaCount L g ((X.tr g).take km) =
      128 * okPolls (Bar.loc L (gw / L.block) ⟨.clc, 0, true⟩) ((X.tr gw).take kw) + lw.q +
        bw.val := by
    rw [hslot] at hic
    omega
  have hE : mmaCount L g ((X.tr g).take km) / 128 =
      okPolls (Bar.loc L (gw / L.block) ⟨.clc, 0, true⟩) ((X.tr gw).take kw) := by omega
  have hR : mmaCount L g ((X.tr g).take km) % 128 = lw.q + bw.val := by omega
  -- the load's tile is the task's
  have htw' : TaskTile L X (g / L.block / 2) (mmaCount L g ((X.tr g).take km) / 128) lw.m lw.n :=
    ⟨gw, kw, hgwl, hcl, (List.getElem?_eq_some_iff.mp hgw).1.le, by rw [hE]; exact htw⟩
  obtain ⟨rfl, rfl⟩ := taskTile_agree ht hag htw' htile
  -- the box's origin
  have hout : spw.outer = 1 := by rw [hspw]; rfl
  have ho0 := horig ⟨0, by omega⟩
  have ho1 := horig ⟨1, by omega⟩
  have h0 : (spw.origin 0).toNat = 64 * (lw.q + bw.val) := by
    have : (0 : Fin (spw.outer + 1)) = ⟨0, by omega⟩ := rfl
    rw [this, ho0]; simp only [↓reduceIte, Int.toNat_natCast]
  have h1 : (spw.origin 1).toNat = (if jw.val < 2 then outputRow lw.m (gw / L.block % 2) jw.val 0
      else 256 * lw.n + 128 * (gw / L.block % 2)) := by
    have : (1 : Fin (spw.outer + 1)) = ⟨1, by omega⟩ := Fin.ext (by simp [hout])
    rw [this, ho1]; simp only [one_ne_zero, ↓reduceIte, Int.toNat_natCast]
  rw [hval, h0, h1, hR]
  have hr : gw / L.block % 2 = row / 128 := by omega
  cases isB
  · simp only [Bool.false_eq_true, ↓reduceIte] at hjw ⊢
    simp only [hjw, show g % L.block / 32 % 2 < 2 from Nat.mod_lt _ (by decide), ↓reduceIte, hr,
      accRow, outputRow]
    congr 2
    omega
  · simp only [↓reduceIte] at hjw ⊢
    simp only [hjw, show ¬ (2 < 2) by omega, ↓reduceIte, hr]
    congr 2 <;> omega


/-- The kernel's profile evaluates its FP16 MMAs by the ideal-real rule. -/
theorem eval_prod {d : Descriptor} (hkind : d.kind = .f16 .f16 .f32) (acc : Bool)
    (a b : List (Option Byte)) (old : Option Value) (row col : Nat) :
    TcMma.eval Prod d acc a b old row col = Assumption.execIdealMma d acc a b old row col := by
  simp [TcMma.eval, hkind, Assumptions.idealArith, Assumption.idealReal]

/-- The operand byte counts of the kernel's MMA descriptor. -/
theorem mmaDescriptor_bytes' :
    (if InputRing.mmaDescriptor.ws = true ∧ InputRing.mmaDescriptor.m < 128 then 128
      else InputRing.mmaDescriptor.m) * InputRing.mmaDescriptor.kind.k *
      InputRing.mmaDescriptor.kind.width = InputRing.mmaDescriptor.m * 16 * 2 ∧
    InputRing.mmaDescriptor.n * InputRing.mmaDescriptor.kind.k *
      InputRing.mmaDescriptor.kind.width = InputRing.mmaDescriptor.n * 16 * 2 := by
  decide

set_option maxHeartbeats 8000000 in
/-- **A completed MMA's value**: at cell `(row, col)`, the prefix of the dot product of its task's
tile over its task's MMAs up to it. -/
theorem mma_value (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X)
    (hov : OperandValues P L X) (hag : AllResponsesAgree L X) (hacs : MmaAccSources L X) :
    ∀ k g pc dst sp acc mask (m : Mma.D) (s jj : Fin 4),
      X.get (g, k) = some ⟨pc, .tc (.mma dst sp acc mask)⟩ →
      Frame.stateAt (code L) X g k = some (some (.inr (.mma m))) → m.site = .mma s jj →
      X.async.mmaDone (g, k) = true → ∀ tm tn,
      TaskTile L X (g / L.block / 2) (mmaCount L g ((X.tr g).take k) / 128) tm tn →
      ∀ row col cell, row < 256 → col < 256 → writeCell sp dst mask row col = some cell →
      TcMma.Result L Prod X (g, k) cell (.float .f32 (prefixDot P (accRow tm (g % L.block / 32) row)
        (256 * tn + col) (16 * (4 * (mmaCount L g ((X.tr g).take k) % 128) + jj.val + 1)))) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro g pc dst sp acc mask m s jj he hσ hs hd tm tn htile row col cell hr hc hpos
  have hg := Frame.lt_of_get hX he
  obtain ⟨m', s', j', hd', hs', -, hsp, -⟩ := ht.mma_issue hg he hσ rfl
  simp only [Sum.inr.injEq, Prologue.Role.mma.injEq] at hd'
  subst hd'
  rw [hs] at hs'
  simp only [Mma.Site.mma.injEq] at hs'
  obtain ⟨rfl, rfl⟩ := hs'
  obtain ⟨hMq, hq4, -, -, hacc⟩ := ht.mma_block hg he hσ hs
  -- the operands
  have hst := hX.tma.2.1.2 (g, k) hd
  obtain ⟨ops, hops⟩ : ∃ ops, X.async.mmaOperands (g, k) = some ops := by
    cases h : X.async.mmaOperands (g, k) with
    | none => simp [AsyncCopy.Snapshot.mmaStarted, h] at hst
    | some ops => exact ⟨ops, rfl⟩
  obtain ⟨-, hla, hlb⟩ := hX.mma_observation_shape ⟨pc, he⟩ hops
  have hsd : sp.descriptor = InputRing.mmaDescriptor := by rw [hsp]; rfl
  rw [hsd] at hla hlb
  rw [mmaDescriptor_bytes'.1] at hla
  rw [mmaDescriptor_bytes'.2] at hlb
  set M := mmaCount L g ((X.tr g).take k) with hMdef
  have ha : ∀ kk < 16, Assumption.idealMmaElement (.f16 .f16 .f32) .a ops.a row kk =
      .ok (P.a (accRow tm (g % L.block / 32) row) (16 * (4 * (M % 128) + jj.val) + kk)) := by
    intro kk hkk
    have := operand_value hX ht hov hag he hσ hs hops htile false hr hkk
    simp only [Bool.false_eq_true, ↓reduceIte] at this
    rw [this]
    congr 2
    omega
  have hb : ∀ kk < 16, Assumption.idealMmaElement (.f16 .f16 .f32) .b ops.b col kk =
      .ok (P.b (256 * tn + col) (16 * (4 * (M % 128) + jj.val) + kk)) := by
    intro kk hkk
    have := operand_value hX ht hov hag he hσ hs hops htile true hc hkk
    simp only [↓reduceIte] at this
    rw [this]
    congr 2
    omega
  have hkind : sp.descriptor.kind = .f16 .f16 .f32 := by rw [hsd]; rfl
  have hv : TcMma.Valid sp.descriptor := by rw [hsd]; decide
  have hr' : row < sp.descriptor.m := by rw [hsd]; exact hr
  have hc' : col < sp.descriptor.n := by rw [hsd]; exact hc
  have hneg : sp.descriptor.negateA = false ∧ sp.descriptor.negateB = false := by
    rw [hsd]; exact ⟨rfl, rfl⟩
  have hws : sp.descriptor.ws = false := by rw [hsd]; rfl
  rw [← hsd] at hla hlb
  cases hacc' : acc
  · -- the task's first MMA overwrites
    have hfirst : M % 128 = 0 ∧ jj.val = 0 := by
      rw [hacc'] at hacc
      simp [Mma.accumulates] at hacc
      omega
    rw [hacc'] at he
    refine .overwrite ⟨pc, he⟩ hpos hops ?_
    rw [eval_prod hkind]
    have h := execIdealMma_segment (P := P) (globalRow := accRow tm (g % L.block / 32) row)
      (globalCol := 256 * tn + col) (first := 0) (old := none) (accumulate := false)
      hkind hv hr' hc' hla hlb hws hneg.1 hneg.2
      (fun kk hkk => by simpa [hfirst] using ha kk hkk)
      (fun kk hkk => by simpa [hfirst] using hb kk hkk)
      (show Assumption.idealMmaAccumulator .f32 false none = .ok 0 from rfl)
    rw [h]
    simp only [segmentDot_from_zero, add_zero, hfirst]
  · -- an accumulating MMA adds its terms to the previous MMA of its task
    rw [hacc'] at he hacc
    obtain ⟨k', hk', ⟨d', s', a', mask', hi'⟩, hd', hnb, hsrc⟩ :=
      hacs g k dst sp mask ⟨pc, he⟩ hd
    have hkl : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
    obtain ⟨k'', m'', s'', j'', hk'', hσ'', hs'', ⟨pc'', d'', sp'', a'', mask'', he''⟩, hnb'',
      hKidx, hE⟩ := ht.mma_prev hg hkl hσ hs hacc.symm
    have hkk : k' = k'' := by
      rcases Nat.lt_trichotomy k' k'' with h1 | h1 | h1
      · exact absurd he'' (hnb k'' pc'' d'' sp'' a'' mask'' h1 hk'')
      · exact h1
      · obtain ⟨pci, hei⟩ := hi'
        exact absurd hei (hnb'' k' pci d' s' a' mask' h1 hk')
    subst hkk
    obtain ⟨pci, hei⟩ := hi'
    rw [hei] at he''
    simp only [Option.some.injEq, Event.mk.injEq, Kind.tc.injEq, TcKind.mma.injEq] at he''
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := he''
    obtain ⟨m3, s3, j3, hd3, hs3, -, hsp3, -⟩ := ht.mma_issue hg hei hσ'' rfl
    simp only [Sum.inr.injEq, Prologue.Role.mma.injEq] at hd3
    subst hd3
    rw [hs''] at hs3
    simp only [Mma.Site.mma.injEq] at hs3
    obtain ⟨rfl, rfl⟩ := hs3
    obtain ⟨hdst', hmask'⟩ := ht.mma_dst hg hei hσ'' rfl
    obtain ⟨hdst, hmask⟩ := ht.mma_dst hg he hσ rfl
    have hpos' : writeCell s' d' mask' row col = some cell := by
      rw [hsp3, hdst', hmask', ← hpos, hsp, hdst, hmask]
      exact writeCell_step L _ _ _ _ _ _ _ _ _ _
    have hIH := ih k' hk' g pci d' s' a' mask' m'' s'' j'' hei hσ'' hs'' hd' tm tn
      (by rw [hE]; exact htile) row col cell hr hc hpos'
    have hfirst : 16 * (4 * (mmaCount L g ((X.tr g).take k') % 128) + j''.val + 1) =
        16 * (4 * (M % 128) + jj.val) := by omega
    rw [hfirst] at hIH
    refine .accumulate ⟨pc, he⟩ hpos hops hIH (hsrc row col cell hpos) ?_
    rw [eval_prod hkind]
    have hp : Assumption.idealMmaAccumulator .f32 true
        (some (.float .f32 (prefixDot P (accRow tm (g % L.block / 32) row) (256 * tn + col)
          (16 * (4 * (M % 128) + jj.val))))) =
        .ok (prefixDot P (accRow tm (g % L.block / 32) row) (256 * tn + col)
          (16 * (4 * (M % 128) + jj.val))) := by
      simp [Assumption.idealMmaAccumulator, valFloat]
      rfl
    have h := execIdealMma_segment (P := P) (globalRow := accRow tm (g % L.block / 32) row)
      (globalCol := 256 * tn + col) (first := 16 * (4 * (M % 128) + jj.val))
      hkind hv hr' hc' hla hlb hws hneg.1 hneg.2 ha hb hp
    rw [h]
    have hadd : segmentDot P (accRow tm (g % L.block / 32) row) (256 * tn + col)
        (16 * (4 * (M % 128) + jj.val)) 16 +
        prefixDot P (accRow tm (g % L.block / 32) row) (256 * tn + col)
          (16 * (4 * (M % 128) + jj.val)) =
        prefixDot P (accRow tm (g % L.block / 32) row) (256 * tn + col)
          (16 * (4 * (M % 128) + jj.val + 1)) := by
      rw [add_comm, show 16 * (4 * (M % 128) + jj.val + 1) =
        16 * (4 * (M % 128) + jj.val) + 16 by ring, ← prefixDot_add]
    rw [hadd]

end Result

end
end PTX.Kernels.Fp16Gemm8192.Proof
