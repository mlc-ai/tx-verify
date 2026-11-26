-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Assumptions
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Seg
public import Lemmas.Flow.OutLit

@[expose] public section

/-! # The peer exchange's readings for generated runs (spike)

The local rule `sharedBits` reads the 64 integer instructions of the peer-score pack
(pcs 394 to 473, `Assumptions.peerPack`) as moves of the ideal score payloads. This file gives the
widening `cvt.u64.u32` of the pack as a role reading (`XItem.fn`) for `Tools/out_gen.py`: at a
pc whose `peerPack` step is that widening, it writes `extE` of its source, the payload paired with
the zero word for a score half, else Core's conversion (`rule_ext`). The other two forms of the
pack (`shl.b64` by 32, `or.b64` in two operand orders) are not run items yet: the shift has an
immediate operand and the merge's outcome depends on the site's operand order. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
open PTX PTX.Flow PTX.Proof PTX.Kernels.FlashMlaSparseDecodeH64

noncomputable section
variable {L : Launch} {g : Nat}

theorem w0SegFree (pc : Nat) : Assumption.SegFreePc Assumptions.all pc :=
  noSegments.segFreePc

/-- `cvt.u64.u32 d, a`. -/
def extC (d a : Nat) : CvtInstr :=
  { dst := .int .u 64, src := .int .u 32, d := d, srcs := [.reg a] }

def extOp (d : Nat) (s : List Nat) : Op := .cvt (extC d (s.getD 0 0))

/-- Core's `cvt.u64.u32` of a register holding `v` (THREAD-CVT): a non-generic 32-bit pointer
widens, any other value's low 32 bits are zero-extended. -/
def coreExt (v : Value) : Exec Value :=
  match v with
  | .ptr w generic sp off =>
    if w = 32 ∧ generic = false then .ok (.ptr 64 generic sp off) else .error .noRule
  | .policy => .error .noRule
  | .bits _ x => .ok (.bits 64 (truncBits 64 (truncBits 32 x)))
  | v => match v.bitPattern with
    | some n => .ok (.bits 64 (truncBits 64 (truncBits 32 (BitVec.ofNat 64 n))))
    | none => .error .typeMismatch

/-- `scoreHalf` as a Boolean the kernel evaluates (the assumption's own decision procedure is
built with a private splitter that importing modules cannot reduce). -/
def halfB : Value → Bool
  | .float .f32 _ => true
  | .bits 32 b => decide (b.toNat < 2 ^ 32)
  | _ => false

theorem halfB_iff (v : Value) : halfB v = true ↔ Assumptions.scoreHalf v := by
  unfold halfB Assumptions.scoreHalf
  split <;> split <;> simp_all

/-- What the peer pack's widening writes: a score half paired with the zero word, else Core's. -/
def extE : List Value → Exec Value
  | [v] => if halfB v then .ok (.pair v Assumptions.peerPackZero) else coreExt v
  | _ => .error .noRule

theorem execLocal_ext {t : TState} {d a : Nat} {v : Value} (h : t.regs a = some v) :
    execLocal L g t (.cvt (extC d a)) = (coreExt v).map fun w => PTX.next (setReg t d w) := by
  have hr : (Op.cvt (extC d a)).rule = some .threadCvt := by
    simp [Op.rule, CvtInstr.rule, CvtInstr.exact, extC]
  simp only [execLocal, hr]
  cases v <;>
    simp [execCvt, extC, readValue, readReg, readBits, h, coreExt, bind, Except.bind, pure,
      Except.pure, Except.map, throw, throwThe, MonadExceptOf.throw]
  all_goals first
    | (split_ifs <;> simp_all)
    | (split <;> rename_i hx <;> split at hx <;> simp_all)

/-- Every assumption other than `sharedBits` declines a conversion of the pack. -/
theorem execLocalA_peer {t : TState} {d a : Nat} (hs : 394 ≤ t.pc) (he : t.pc < 474) :
    execLocalA Assumptions.all L g t (.cvt (extC d a)) =
      (Assumptions.peerPackRule t (.cvt (extC d a))).getD (execLocal L g t (.cvt (extC d a))) := by
  have hpa : t.pc ∉ paramAdds := by simp [paramAdds]; omega
  have hpf : t.pc ∉ prefetchTensorMapSites := by simp [prefetchTensorMapSites]; omega
  have hsb : Assumptions.sharedBitsSites.contains t.pc = false := by
    simp [Assumptions.sharedBitsSites]; omega
  have hd : Assumptions.deadPackWords t.pc = none :=
    Assumptions.deadPackWords.eq_3 _ (by omega) (by omega)
  rw [execLocalA_noSegment (fun a ha => noSegments a ha L g t), execLocalRule]
  simp only [Assumptions.all, List.findSome?_cons, List.findSome?_nil]
  have hpar : Assumptions.paramPointers.localRule L g t (.cvt (extC d a)) = none := by
    simp [Assumptions.paramPointers, hpa, hpf]
  have hsh : Assumptions.sharedBits.localRule L g t (.cvt (extC d a)) =
      Assumptions.peerPackRule t (.cvt (extC d a)) := by
    simp only [Assumptions.sharedBits, hsb, Bool.false_eq_true, ↓reduceIte,
      Assumptions.deadPackRule_of_none hd, Option.orElse]
  rw [show Assumptions.idealArith.localRule L g t (.cvt (extC d a)) = none from rfl,
    show Assumptions.approx.localRule L g t (.cvt (extC d a)) = none from rfl,
    show Assumptions.mulBf16x2.localRule L g t (.cvt (extC d a)) = none from rfl,
    show Assumptions.cvtBf16x2.localRule L g t (.cvt (extC d a)) = none from rfl,
    show Assumptions.cvtUe8m0.localRule L g t (.cvt (extC d a)) = none from rfl,
    show Assumptions.lg2Exact.localRule L g t (.cvt (extC d a)) = none from rfl,
    show Assumptions.ncReadOnly.localRule L g t (.cvt (extC d a)) = none from rfl, hpar,
    show Assumptions.storeDrain.localRule L g t (.cvt (extC d a)) = none from rfl, hsh,
    show Assumptions.commitOrder.localRule L g t (.cvt (extC d a)) = none from rfl]
  cases Assumptions.peerPackRule t (.cvt (extC d a)) <;> rfl

/-- **The pack's widening** at a pc whose peer step is `extend d a`. -/
theorem rule_ext {d a : Nat} (pc : Nat) (hp : Assumptions.peerPack pc = some (.extend d a)) :
    ∀ s : TState, s.pc = pc → (XItem.fn (extOp d [a]) d [a] extE).Rule Assumptions.all L g s := by
  intro t ht W hW
  have h := hW a (by simp)
  have hr : 394 ≤ pc ∧ pc < 474 := by
    unfold Assumptions.peerPack at hp; split_ifs at hp with hc
    · exact hc
  rw [show extOp d [a] = .cvt (extC d a) from rfl, execLocalA_peer (ht ▸ hr.1) (ht ▸ hr.2),
    execLocal_ext h]
  have hpk : Assumptions.peerPackRule t (.cvt (extC d a)) =
      ((Assumptions.PeerPack.extend d a).run t).map Except.ok := by
    simp [Assumptions.peerPackRule, extC, ht, hp]
  have hrun : (Assumptions.PeerPack.extend d a).run t =
      if Assumptions.scoreHalf (W a) then
        some (PTX.next (setReg t d (.pair (W a) Assumptions.peerPackZero))) else none := by
    show (t.regs a).bind _ = _
    rw [h, Option.bind_some]
  rw [hpk, hrun, show List.map W [a] = [W a] from rfl]
  by_cases hs : Assumptions.scoreHalf (W a)
  · have he : extE [W a] = .ok (.pair (W a) Assumptions.peerPackZero) := by
      simp only [extE, (halfB_iff _).mpr hs, ↓reduceIte]
    simp only [hs, ↓reduceIte, he]
    rfl
  · have hb : halfB (W a) = false := by
      cases hh : halfB (W a)
      · rfl
      · exact absurd ((halfB_iff _).mp hh) hs
    have he : extE [W a] = coreExt (W a) := by simp only [extE, hb, Bool.false_eq_true, ↓reduceIte]
    simp only [hs, ↓reduceIte, he]
    rfl

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
