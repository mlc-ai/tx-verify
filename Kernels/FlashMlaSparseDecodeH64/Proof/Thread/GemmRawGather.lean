-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg1Tma
import Lemmas.Flow.TensorLoadFacts

@[expose] public section

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.GemmRawGather

open PTX PTX.Flow PTX.Proof Wg1Tma

noncomputable section

set_option maxRecDepth 100000

private def gatherReg (k : Fin 16) (j : Fin 4) : Nat :=
  (if k.val = 0 then 692 else 693 + 5 * k.val) + j.val

private theorem gatherOps (k : Fin 16) :
    ((coordRegs.drop (4 * k.val)).take 4).map Opnd.reg =
      [.reg (gatherReg k 0), .reg (gatherReg k 1),
        .reg (gatherReg k 2), .reg (gatherReg k 3)] := by
  fin_cases k <;> rfl

/-- The words a gather issue reads are the role's recorded words of its four positions. -/
abbrev Words (P : Params) (L : Launch) (g : Nat) (d : D) (k : Fin 16) : Prop :=
  ∀ j : Fin 4, d.cw (coordPos k.val j.val) = b32 (coordAt P L g d.block (coordPos k.val j.val))

private theorem gather_reg {P : Params} {L : Launch} {g : Nat} {d : D} {t : TState}
    (k : Fin 16) (j : Fin 4) (hd : d.site = .issue k) (ha : (Wg1Tma.code P L g).AtD d t)
    (hw : Words P L g d k) :
    t.regs (gatherReg k j) = some (b32 (coordAt P L g d.block (coordPos k.val j.val))) := by
  have hm : gatherReg k j ∈ (Flow.live d.site.pc).filter tracked.contains := by
    rw [hd]
    fin_cases k <;> fin_cases j <;> decide +kernel
  rw [atD_reg ha hm, ← hw j]
  fin_cases k <;> fin_cases j <;> rfl

private theorem gather_zero {P : Params} {L : Launch} {g : Nat} {d : D} {t : TState}
    (k : Fin 16) (hd : d.site = .issue k) (ha : (Wg1Tma.code P L g).AtD d t) :
    t.regs 691 = some (b32 0) := by
  have hm : 691 ∈ (Flow.live d.site.pc).filter tracked.contains := by
    rw [hd]
    fin_cases k <;> decide +kernel
  exact atD_reg ha hm

private theorem readCoordBits {L : Launch} {g : Nat} {t : TState} {r n : Nat}
    (hr : t.regs r = some (b32 n)) :
    readBits L g t 32 (.reg r) = .ok (BitVec.ofNat 64 (n % 2 ^ 32)) := by
  simp only [readBits, readReg, hr, b32, bind, Except.bind, pure, Except.pure, truncBits,
    BitVec.toNat_ofNat, Nat.mod_mod_of_dvd _ (by decide : 2 ^ 32 ∣ 2 ^ 64)]

/-- The saved gather operands read as one zero column and four 32-bit row coordinates. -/
theorem read_coordinates {P : Params} {L : Launch} {g : Nat} {d : D} {t : TState}
    (k : Fin 16) (hd : d.site = .issue k) (ha : (Wg1Tma.code P L g).AtD d t)
    (hw : Words P L g d k) :
    let b (j : Fin 4) :=
      BitVec.ofNat 64 (coordAt P L g d.block (coordPos k.val j.val) % 2 ^ 32)
    (Opnd.reg 691 :: ((coordRegs.drop (4 * k.val)).take 4).map Opnd.reg).mapM
      (readBits L g t 32) = .ok ((0 : BitVec 64) :: [b 0, b 1, b 2, b 3]) := by
  dsimp only
  have hr (j : Fin 4) : readBits L g t 32 (.reg (gatherReg k j)) =
      .ok (BitVec.ofNat 64 (coordAt P L g d.block (coordPos k.val j.val) % 2 ^ 32)) :=
    readCoordBits (gather_reg k j hd ha hw)
  have hz : readBits L g t 32 (.reg 691) = .ok 0 :=
    readBits_b32 (gather_zero k hd ha) (by decide)
  rw [gatherOps]
  simp only [List.mapM_cons, List.mapM_nil, hr, hz, bind, Except.bind, pure, Except.pure]

private theorem gather_copy {L : Launch} {g : Nat} {t : TState}
    {e : Event} {u : Option TState} {k : Fin 16} {a : Nat} {s : TensorCopy.Spec}
    (hf : Fires (Site.issue k).pc (eventTmpl asms L g t (issueInstr k).op) e u)
    (hkind : e.kind = .tensorIssue a s) :
    tensorLoadCopy L g t false false (issueRegs.getD k.val 0) 0 (.reg 3049)
      (.reg 691 :: ((coordRegs.drop (4 * k.val)).take 4).map Opnd.reg) 696 0 .fourRows =
        .ok (a, s) := by
  let dst := issueRegs.getD k.val 0
  let coords := .reg 691 :: ((coordRegs.drop (4 * k.val)).take 4).map Opnd.reg
  change Fires (Site.issue k).pc
    (tensorTmpl L g t (.cpTensor false false dst 0 (.reg 3049) coords 696 0 none .fourRows
      (some (.reg 3050)))) e u at hf
  simp only [tensorTmpl, ofExec, bind, Except.bind, pure, Except.pure, throw, throwThe,
    MonadExceptOf.throw] at hf
  rcases hp : cachePolicyRead L g t (some (.reg 3050)) with fault | ⟨⟩ <;> rw [hp] at hf
  · simp only [Fires] at hf
    rw [hf.1] at hkind
    cases hkind
  · rcases hc : tensorLoadCopy L g t false false dst 0 (.reg 3049) coords 696 0 .fourRows with
      fault | ⟨addr, copy⟩ <;> rw [hc] at hf
    · simp only [Fires] at hf
      rw [hf.1] at hkind
      cases hkind
    · dsimp only at hf
      split_ifs at hf
      · simp only [Fires] at hf
        rw [hf.1] at hkind
        cases hkind
        rfl
      · simp only [Fires] at hf
        rw [hf.1] at hkind
        cases hkind

private theorem copy_rows {L : Launch} {g : Nat} {t : TState} {dst : Nat} {cs : List Opnd}
    {a : Nat} {s : TensorCopy.Spec} {vals : List (BitVec 64)}
    (hcopy : tensorLoadCopy L g t false false dst 0 (.reg 3049) cs 696 0 .fourRows = .ok (a, s))
    (hv : cs.mapM (readBits L g t 32) = .ok vals) :
    s.rows = some (fun j : Fin 4 => (BitVec.ofNat 32 (vals.getD (j.val + 1) 0).toNat).toInt) := by
  unfold tensorLoadCopy at hcopy
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw, hv]
    at hcopy
  rcases hm : tensorMap L g t (.reg 3049) cs .fourRows with f | ⟨mapAddr, outer, desc⟩ <;>
    rw [hm] at hcopy
  · cases hcopy
  rcases hd : sharedEffAddr L g t false dst 0 with f | loc <;> simp only [hd] at hcopy
  · cases hcopy
  all_goals repeat' (split at hcopy <;> (try (cases hcopy; done)))
  all_goals cases hcopy
  all_goals rfl

private theorem copy_reads {L : Launch} {g : Nat} {t : TState} {dst : Nat} {cs : List Opnd}
    {a : Nat} {s : TensorCopy.Spec}
    (hcopy : tensorLoadCopy L g t false false dst 0 (.reg 3049) cs 696 0 .fourRows = .ok (a, s)) :
    ∃ vals, cs.mapM (readBits L g t 32) = .ok vals := by
  rcases hv : cs.mapM (readBits L g t 32) with f | vals
  · unfold tensorLoadCopy at hcopy
    simp only [bind, Except.bind, throw, throwThe, MonadExceptOf.throw, hv] at hcopy
    rcases hm : tensorMap L g t (.reg 3049) cs .fourRows with f' | ⟨mapAddr, outer, desc⟩ <;>
      rw [hm] at hcopy
    · cases hcopy
    rcases hd : sharedEffAddr L g t false dst 0 with f' | loc <;> simp only [hd] at hcopy
    · cases hcopy
    all_goals repeat' (split at hcopy <;> (try cases hcopy))
  · exact ⟨vals, rfl⟩

/-- Each gather takes its descriptor from the launch's actual tensor-map binding, its first
coordinate is zero and it names four rows, whatever words its row registers hold. -/
theorem gather_layout {P : Params} {L : Launch} {g : Nat} {mem0 : Mem0}
    {d : D} {t : TState} {e : Event} {u : Option TState} {a : Nat} {s : TensorCopy.Spec}
    (hpre : Pre P L mem0) (k : Fin 16) (hd : d.site = .issue k) (ha : (Wg1Tma.code P L g).AtD d t)
    (hi : Inv P L g d) (hf : Fires d.site.pc (eventTmpl asms L g t (issueInstr k).op) e u)
    (he : e.kind = .tensorIssue a s) :
    (∃ desc : TensorDescriptor.Descriptor s.outer,
      L.tensorMaps (P.param1Base + Wg1Tma.kvOff d) = some ⟨s.outer, desc⟩ ∧
      s.descriptor = desc.fourRows) ∧
    s.origin ⟨0, Nat.zero_lt_succ _⟩ = 0 ∧ ∃ rows, s.rows = some rows := by
  have hf' := hf
  rw [hd] at hf'
  have hc := gather_copy hf' he
  have hfields := gather_issue_fields hpre hd ha hi hf he
  obtain ⟨_, _, desc, hdesc, _, hspec, _⟩ := tensorLoadCopy_ok hc
  change s.descriptor = desc.fourRows at hspec
  obtain ⟨vals, hvs⟩ := copy_reads hc
  have hz : readBits L g t 32 (.reg 691) = .ok 0 :=
    readBits_b32 (gather_zero k hd ha) (by decide)
  have hhead : vals.getD 0 0 = 0 := by
    rw [List.mapM_cons, hz] at hvs
    simp only [bind, Except.bind] at hvs
    rcases hr : (((coordRegs.drop (4 * k.val)).take 4).map Opnd.reg).mapM
      (readBits L g t 32) with f | rest <;> rw [hr] at hvs
    · cases hvs
    · cases hvs
      rfl
  refine ⟨⟨desc, hfields.1 ▸ hdesc, hspec⟩, ?_, _, copy_rows hc hvs⟩
  rw [tensorLoadCopy_origin_all hc hvs]
  change (BitVec.ofNat 32 (vals.getD 0 0).toNat).toInt = 0
  rw [hhead]
  rfl

/-- Each gather uses signed coordinates from its four saved logical sparse slots. -/
theorem gather_coordinates {P : Params} {L : Launch} {g : Nat}
    {d : D} {t : TState} {e : Event} {u : Option TState} {a : Nat} {s : TensorCopy.Spec}
    (k : Fin 16) (hd : d.site = .issue k) (ha : (Wg1Tma.code P L g).AtD d t)
    (hf : Fires d.site.pc (eventTmpl asms L g t (issueInstr k).op) e u)
    (he : e.kind = .tensorIssue a s) (hw : Words P L g d k) :
    s.rows = some (fun j : Fin 4 =>
      (BitVec.ofNat 32 (coordAt P L g d.block (coordPos k.val j.val))).toInt) := by
  have hf' := hf
  rw [hd] at hf'
  have hc := gather_copy hf' he
  let value (j : Fin 4) := coordAt P L g d.block (coordPos k.val j.val)
  let b (j : Fin 4) := BitVec.ofNat 64 (value j % 2 ^ 32)
  let vals := (0 : BitVec 64) :: [b 0, b 1, b 2, b 3]
  have hvs : (Opnd.reg 691 :: ((coordRegs.drop (4 * k.val)).take 4).map Opnd.reg).mapM
      (readBits L g t 32) = .ok vals :=
    read_coordinates k hd ha hw
  rw [copy_rows hc hvs]
  congr 1
  funext j
  have heq (n : Nat) :
      BitVec.ofNat 32 (BitVec.ofNat 64 (n % 2 ^ 32)).toNat = BitVec.ofNat 32 n := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat, Nat.mod_mod_of_dvd _ (by decide : 2 ^ 32 ∣ 2 ^ 64),
      Nat.mod_mod]
  fin_cases j <;> exact congrArg BitVec.toInt (heq (value _))

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.GemmRawGather
