-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.GenRules
public import Lemmas.Flow.OutCoreRules

@[expose] public section

/-! # The peer pack's shifts and merges as run items, and the stretch's moves

The two other integer forms of the peer-score pack (`Assumptions.peerPack`): `shl.b64 d, a, 32`
(`upper`: a score half paired with the zero word moves to the high half, `upperE`) and
`or.b64 d, x, y` (`merge`: the low word of one pair and the high word of the other, `mergeE`).
Where the pack's rule declines, Core's value (`coreF`, obtained from `XItem.core_shl`,
`XItem.core_or` under no assumptions) is written. A merge's operand order is the site's: the
high pair first exactly when its register is the smaller (`mergeStep`), so the outcome function
takes the source registers (`mergeE d s`). `noRuleMove` covers the stretch's Core moves. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
open PTX PTX.Flow PTX.Proof PTX.Kernels.FlashMlaSparseDecodeH64

noncomputable section
variable {L : Launch} {g : Nat}

/-- At a pc of the pack, the rules other than `sharedBits` decline an instruction they do not
read, and `sharedBits` is the pack's rule. -/
theorem execLocalA_peerOp {t : TState} {op : Op} (hs : 394 ≤ t.pc) (he : t.pc < 477)
    (hn : ∀ a ∈ [Assumptions.idealArith, Assumptions.approx, Assumptions.mulBf16x2,
      Assumptions.cvtBf16x2, Assumptions.cvtUe8m0, Assumptions.lg2Exact, Assumptions.ncReadOnly,
      Assumptions.storeDrain, Assumptions.commitOrder], a.localRule L g t op = none) :
    execLocalA Assumptions.all L g t op =
      (Assumptions.peerPackRule t op).getD (execLocal L g t op) := by
  have hpa : t.pc ∉ paramAdds := by simp [paramAdds]; omega
  have hpf : t.pc ∉ prefetchTensorMapSites := by simp [prefetchTensorMapSites]; omega
  have hsb : Assumptions.sharedBitsSites.contains t.pc = false := by
    simp [Assumptions.sharedBitsSites]; omega
  have hd : Assumptions.deadPackWords t.pc = none :=
    Assumptions.deadPackWords.eq_3 _ (by omega) (by omega)
  rw [execLocalA_noSegment (fun a ha => noSegments a ha L g t), execLocalRule]
  simp only [Assumptions.all, List.findSome?_cons, List.findSome?_nil]
  have hpar : Assumptions.paramPointers.localRule L g t op = none := by
    simp [Assumptions.paramPointers, hpa, hpf]
  have hsh : Assumptions.sharedBits.localRule L g t op = Assumptions.peerPackRule t op := by
    simp only [Assumptions.sharedBits, hsb, Bool.false_eq_true, ↓reduceIte,
      Assumptions.deadPackRule_of_none hd, Option.orElse]
  rw [hn _ (by simp), hn _ (by simp), hn _ (by simp), hn _ (by simp), hn _ (by simp),
    hn _ (by simp), hn _ (by simp), hpar, hn _ (by simp), hsh, hn _ (by simp)]
  cases Assumptions.peerPackRule t op <;> rfl

theorem peer_pc {s : Assumptions.PeerPack} {pc : Nat} (hp : Assumptions.peerPack pc = some s) :
    394 ≤ pc ∧ pc < 474 := by
  unfold Assumptions.peerPack at hp; split_ifs at hp with hc
  · exact hc

/-- `noRuleMove`: no assumption reads a move at a pc of the stretch. -/
theorem noRuleMove {op : Op} (pc : Nat)
    (hk : (match op with | .move _ => true | _ => false) = true := by exact rfl)
    (hp : 394 ≤ pc ∧ pc < 477 := by decide) : NoLocalRule Assumptions.all L g pc op := by
  cases op <;> simp at hk
  intro s hs a ha
  have hpa : s.pc ∉ paramAdds := by simp [paramAdds]; omega
  have hpf : s.pc ∉ prefetchTensorMapSites := by simp [prefetchTensorMapSites]; omega
  have hsb : Assumptions.sharedBitsSites.contains s.pc = false := by
    simp [Assumptions.sharedBitsSites]; omega
  have hd : Assumptions.deadPackWords s.pc = none :=
    Assumptions.deadPackWords.eq_3 _ (by omega) (by omega)
  simp only [Assumptions.all, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | rfl
    | (simp [Assumptions.paramPointers, hpa, hpf]; done)
    | simp only [Assumptions.sharedBits, hsb, Bool.false_eq_true, ↓reduceIte,
        Assumptions.deadPackRule_of_none hd, Option.orElse, Assumptions.peerPackRule_move]

/-- Core's value of an instruction of Core's forms, from its rule lemma under no assumptions. -/
theorem core_exec {op : Op} {d : Nat} {srcs : List Nat} {t : TState} {W : Nat → Value}
    (h : ∀ s : TState, s.pc = t.pc → (XItem.fn op d srcs (coreF op srcs)).Rule [] L g s)
    (hW : ∀ r ∈ srcs, t.regs r = some (W r)) :
    execLocal L g t op = (coreF op srcs (srcs.map W)).map fun v => PTX.next (setReg t d v) :=
  h t rfl W hW

theorem segFree_nil (pc : Nat) : Assumption.SegFreePc [] pc := fun _ h => by cases h
theorem noRule_nil (pc : Nat) (op : Op) : NoLocalRule [] L g pc op := fun _ _ _ h => by cases h

theorem rule_pack {d a b : Nat} (pc : Nat) (hp : 394 ≤ pc ∧ pc < 477 := by decide) :
    ∀ s : TState, s.pc = pc → (XItem.base (.pack d a b)).Rule Assumptions.all L g s :=
  fun s hs => noRuleMove pc rfl hp s hs

/-! ### The shifts -/

/-- `shl.b64 d, a, 32`. -/
def upOp (d : Nat) (s : List Nat) : Op :=
  .int ⟨.shl, .int .b 64, false, [some d], [.reg (s.getD 0 0), .imm 32]⟩

/-- What the pack's shift writes: a score half paired with the zero word moves to the high half;
otherwise Core's value. -/
def upperE (d : Nat) (s : List Nat) : List Value → Exec Value
  | [.pair x z] => if z = Assumptions.peerPackZero ∧ halfB x = true then
      .ok (.pair Assumptions.peerPackZero x) else coreF (upOp d s) s [.pair x z]
  | vs => coreF (upOp d s) s vs

theorem rule_upper {d a : Nat} (pc : Nat) (hp : Assumptions.peerPack pc = some (.upper d a)) :
    ∀ s : TState, s.pc = pc →
      (XItem.fn (upOp d [a]) d [a] (upperE d [a])).Rule Assumptions.all L g s := by
  intro t ht W hW
  have h := hW a (by simp)
  have hr := peer_pc hp
  have hc := core_exec (L := L) (g := g) (op := upOp d [a]) (d := d) (srcs := [a]) (t := t) (W := W)
    (XItem.core_shl (segFree_nil t.pc) (noRule_nil t.pc _) rfl) hW
  rw [execLocalA_peerOp (ht ▸ hr.1) (by omega) (fun a ha => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl), hc]
  have hpk : Assumptions.peerPackRule t (upOp d [a]) =
      ((Assumptions.PeerPack.upper d a).run t).map Except.ok := by
    simp [Assumptions.peerPackRule, upOp, ht, hp]
  rw [hpk, show List.map W [a] = [W a] from rfl]
  simp only [Assumptions.PeerPack.run, h, Option.bind_eq_bind, Option.bind_some]
  cases hv : W a
  case pair x z => ?_
  all_goals try rfl
  by_cases hz : z = Assumptions.peerPackZero ∧ Assumptions.scoreHalf x
  · have hb : z = Assumptions.peerPackZero ∧ halfB x = true := ⟨hz.1, (halfB_iff x).mpr hz.2⟩
    simp only [hz, hb, and_self, ↓reduceIte, upperE]
    rfl
  · have hb : ¬ (z = Assumptions.peerPackZero ∧ halfB x = true) :=
      fun h' => hz ⟨h'.1, (halfB_iff x).mp h'.2⟩
    simp only [hz, hb, ↓reduceIte, upperE]
    rfl

/-! ### The merges -/

/-- `or.b64 d, x, y`. -/
def mgOp (d : Nat) (s : List Nat) : Op :=
  .int ⟨.or, .int .b 64, false, [some d], [.reg (s.getD 0 0), .reg (s.getD 1 0)]⟩

/-- The pack's step of a merge with sources `s`: the high pair first when its register is the
smaller. -/
def mergeStep (d : Nat) (s : List Nat) : Assumptions.PeerPack :=
  if s.getD 0 0 < s.getD 1 0 then .merge d (s.getD 1 0) (s.getD 0 0) true
  else .merge d (s.getD 0 0) (s.getD 1 0) false

/-- The merged pair of a low pair `l` and a high pair `h`, if both carry a score half beside the
zero word. -/
def mergeOf (l h : Value) : Option Value :=
  match l, h with
  | .pair lo zl, .pair zh hi =>
    if zl = Assumptions.peerPackZero ∧ zh = Assumptions.peerPackZero ∧ halfB lo = true ∧
        halfB hi = true then some (.pair lo hi) else none
  | _, _ => none

/-- What the pack's merge writes: the merged pair, else Core's value. -/
def mergeE (d : Nat) (s : List Nat) : List Value → Exec Value
  | [va, vb] =>
    let r := if s.getD 0 0 < s.getD 1 0 then mergeOf vb va else mergeOf va vb
    match r with
    | some v => .ok v
    | none => coreF (mgOp d s) s [va, vb]
  | vs => coreF (mgOp d s) s vs

theorem run_merge {t : TState} {d low high : Nat} {hf : Bool} {vl vh : Value}
    (h1 : t.regs low = some vl) (h2 : t.regs high = some vh) :
    (Assumptions.PeerPack.merge d low high hf).run t =
      (mergeOf vl vh).map fun v => PTX.next (setReg t d v) := by
  simp only [Assumptions.PeerPack.run, h1, h2, Option.bind_eq_bind, Option.bind_some]
  cases vl
  case pair lo zl =>
    cases vh
    case pair zh hi =>
      simp only [mergeOf]
      by_cases hz : zl = Assumptions.peerPackZero ∧ zh = Assumptions.peerPackZero ∧
          Assumptions.scoreHalf lo ∧ Assumptions.scoreHalf hi
      · obtain ⟨hzl, hzh, hlo, hhi⟩ := hz
        have hb : zl = Assumptions.peerPackZero ∧ zh = Assumptions.peerPackZero ∧
            halfB lo = true ∧ halfB hi = true :=
          ⟨hzl, hzh, (halfB_iff lo).mpr hlo, (halfB_iff hi).mpr hhi⟩
        have hz : zl = Assumptions.peerPackZero ∧ zh = Assumptions.peerPackZero ∧
            Assumptions.scoreHalf lo ∧ Assumptions.scoreHalf hi := ⟨hzl, hzh, hlo, hhi⟩
        simp only [hz, hb, and_self, ↓reduceIte, Option.map_some]
      · have hb : ¬ (zl = Assumptions.peerPackZero ∧ zh = Assumptions.peerPackZero ∧
            halfB lo = true ∧ halfB hi = true) := fun ⟨h1, h2, h3, h4⟩ =>
          hz ⟨h1, h2, (halfB_iff lo).mp h3, (halfB_iff hi).mp h4⟩
        simp only [hz, hb, ↓reduceIte, Option.map_none]
    all_goals rfl
  all_goals rfl

theorem rule_merge {d a b : Nat} (pc : Nat)
    (hp : Assumptions.peerPack pc = some (mergeStep d [a, b])) :
    ∀ s : TState, s.pc = pc →
      (XItem.fn (mgOp d [a, b]) d [a, b] (mergeE d [a, b])).Rule Assumptions.all L g s := by
  intro t ht W hW
  have ha := hW a (by simp)
  have hb := hW b (by simp)
  have hr := peer_pc hp
  have hc := core_exec (L := L) (g := g) (op := mgOp d [a, b]) (d := d) (srcs := [a, b])
    (t := t) (W := W) (XItem.core_or (segFree_nil t.pc) (noRule_nil t.pc _) rfl) hW
  rw [execLocalA_peerOp (ht ▸ hr.1) (by omega) (fun a ha => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl), hc,
    show List.map W [a, b] = [W a, W b] from rfl]
  by_cases hab : a < b
  · have hs : mergeStep d [a, b] = .merge d b a true := by simp [mergeStep, hab]
    have hpk : Assumptions.peerPackRule t (mgOp d [a, b]) =
        ((Assumptions.PeerPack.merge d b a true).run t).map Except.ok := by
      simp [Assumptions.peerPackRule, mgOp, ht, hp, hs]
    rw [hpk, run_merge hb ha]
    simp only [mergeE, List.getD_cons_zero, List.getD_cons_succ, hab, ↓reduceIte]
    cases mergeOf (W b) (W a) <;> rfl
  · have hs : mergeStep d [a, b] = .merge d a b false := by simp [mergeStep, hab]
    have hpk : Assumptions.peerPackRule t (mgOp d [a, b]) =
        ((Assumptions.PeerPack.merge d a b false).run t).map Except.ok := by
      simp [Assumptions.peerPackRule, mgOp, ht, hp, hs]
    rw [hpk, run_merge ha hb]
    simp only [mergeE, List.getD_cons_zero, List.getD_cons_succ, hab, ↓reduceIte]
    cases mergeOf (W a) (W b) <;> rfl

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
