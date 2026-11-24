-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionMbarAddress
public import Kernels.TmlFa4Fwd.Proof.CorrectionStatsSync
public import Kernels.TmlFa4Fwd.Proof.StatsBarrierSetup
import Kernels.TmlFa4Fwd.Proof.RegisterHintBody
import Kernels.TmlFa4Fwd.Flow.Code.Part124
import Kernels.TmlFa4Fwd.Flow.Code.Part125
import Kernels.TmlFa4Fwd.Flow.Code.Part128
import Kernels.TmlFa4Fwd.Flow.Code.Part132
import Kernels.TmlFa4Fwd.Flow.Code.Part136

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Flow PTX.Proof PTX.EventFrame Prologue Softmax Epilogue

private def statsRegisters (l : Launch) (g : Nat) (s : TState) : Prop :=
  s.regs 1625 = some (b32 (statsBarrierId l g 0)) ∧
    s.regs 1626 = some (b32 (statsBarrierId l g 1))

private def statsOrigin (l : Launch) (g : Nat) (s : TState) : Prop :=
  ∃ t, t.pc = 7932 ∧ t.fault = none ∧ t.regs 1062 = some (b32 (warpIndex l g)) ∧
    run kernel Assumptions.all l g (s.pc-7932) t = some s

private def statsFrame (l : Launch) (g : Nat) (s : TState) : Prop :=
  s.regs 1062 = some (b32 (warpIndex l g)) ∧
    (7932 < s.pc → s.pc < 7935 → statsOrigin l g s) ∧
    (7935 ≤ s.pc → s.pc < 9205 → statsRegisters l g s)

private def statsWrites (op : Op) : List Nat := writesRegs op ++ scoreEventWrites op

private def statsFrameCode (pc : Nat) (ins : Instr) : Bool :=
  (ins.op.isLocal || correctionReturningOp ins.op) &&
  !(statsWrites ins.op).contains 1062 &&
  ((7932 ≤ pc && pc < 7935) ||
    [1625, 1626].all (fun r => !(statsWrites ins.op).contains r)) &&
  match ins.op with
  | .bra dest _ => !(7932 < dest && dest < 7935) &&
      (!decide (pc < 7935) || decide (dest ≤ 7932 ∨ dest = 9205))
  | .brx .. => false
  | _ => true

private theorem statsAuditAt {pc : Nat} {ins : Instr}
    (hLo : 7745 ≤ pc) (hHi : pc < 9205) (hc : kernel.code[pc]? = some ins) :
    statsFrameCode pc ins = true := by
  let code := ((kernel.code.drop 7745).take (9205-7745)).zipIdx 7745
  have hAll : code.all (fun (ins, pc) => statsFrameCode pc ins) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  apply List.all_eq_true.mp hAll (ins, pc)
  apply List.mem_of_getElem? (i := pc-7745)
  dsimp only [code]
  rw [List.getElem?_zipIdx, List.getElem?_take_of_lt (by omega), List.getElem?_drop,
    Nat.add_sub_of_le hLo, hc]
  rfl

private theorem inStatsSetup {pc : Nat} {ins : Instr} (hLo : 7932 ≤ pc) (hHi : pc < 7935)
    (hc : kernel.code[pc]? = some ins) :
    ins.guard = none ∧ ins.op.isLocal = true ∧
      nextPc ins.op pc = pc+1 := by
  have hPc : pc = 7932 ∨ pc = 7933 ∨ pc = 7934 := by omega
  rcases hPc with rfl | rfl | rfl
  all_goals
    first | rw [Flow.code_7932] at hc | rw [Flow.code_7933] at hc | rw [Flow.code_7934] at hc
    obtain rfl := Option.some.inj hc.symm
    exact ⟨rfl, rfl, rfl⟩

private theorem appendStatsOrigin {l : Launch} {g : Nat} {s u : TState}
    (hLo : 7932 ≤ s.pc) (hHi : s.pc < 7935) (hf : s.fault = none)
    (hFrame : statsFrame l g s) (hNext : u.pc = s.pc+1)
    (ht : Tau kernel Assumptions.all l g s u) :
    statsOrigin l g u := by
  have hStep : run kernel Assumptions.all l g 1 s = some u := by
    simp only [run, tauStep_iff.mpr ht, Option.bind_some]
  rcases Nat.eq_or_lt_of_le hLo with h | h
  · exact ⟨s, h.symm, hf, hFrame.1, by rw [hNext, ← h]; exact hStep⟩
  · obtain ⟨t, ht0, htf, hw, hr⟩ := hFrame.2.1 h hHi
    exact ⟨t, ht0, htf, hw, by
      rw [hNext, show s.pc+1-7932 = (s.pc-7932)+1 by omega]
      exact run_comp hr hStep⟩

private theorem finishStatsOrigin {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} {u : TState} (hPc : u.pc = 7935) (hOrigin : statsOrigin l g u) :
    statsRegisters l g u := by
  obtain ⟨t, ht, hf, hw, hr⟩ := hOrigin
  obtain ⟨s, hRun, hSPc, hA, hB⟩ :=
    correctionStatsBarrierRaw ⟨warpIndex l g, warpIndex_lt hp g⟩ ht hf hw
  rw [hPc] at hr
  have hS := Option.some.inj (hr.symm.trans hRun)
  subst s
  exact ⟨hA, by simpa [statsBarrierId, Nat.add_assoc] using hB⟩

private theorem statsFrameStep {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} {s u : TState} {e : Option Event}
    (hLo : 7745 ≤ s.pc) (hHi : s.pc < 9205) (hSub : s.sub ≤ 3)
    (hFrame : statsFrame l g s) (hStep : WStep kernel Assumptions.all l g s e u) :
    statsFrame l g u := by
  have keptWarp {ins : Instr} (hc : kernel.code[s.pc]? = some ins) :
      1062 ∉ statsWrites ins.op := by
    have h := statsAuditAt hLo hHi hc
    simp only [statsFrameCode, Bool.and_eq_true] at h
    simpa using h.1.1.2
  have keptPair {ins : Instr} (hc : kernel.code[s.pc]? = some ins) (h : 7935 ≤ s.pc)
      {r : Nat} (hr : r ∈ [1625, 1626]) : r ∉ statsWrites ins.op := by
    have hCode := statsAuditAt hLo hHi hc
    simp only [statsFrameCode, Bool.and_eq_true] at hCode
    have hList := hCode.1.2
    simp only [show ¬ s.pc < 7935 by omega, decide_false, Bool.and_false, Bool.false_or] at hList
    simpa using List.all_eq_true.mp hList _ hr
  have carry {ins : Instr} (hc : kernel.code[s.pc]? = some ins)
      (hKeep : ∀ r, r ∉ statsWrites ins.op → u.regs r = s.regs r)
      (hInside : 7932 < u.pc → u.pc < 7935 → statsOrigin l g u)
      (hAfter : 7935 ≤ u.pc → u.pc < 9205 →
        7935 ≤ s.pc ∨ u.pc = 7935 ∧ statsOrigin l g u) : statsFrame l g u := by
    refine ⟨(hKeep _ (keptWarp hc)).trans hFrame.1, hInside, ?_⟩
    intro hu huEnd
    rcases hAfter hu huEnd with h | ⟨hPc, hOrigin⟩
    · obtain ⟨hA, hB⟩ := hFrame.2.2 h hHi
      exact ⟨(hKeep _ (keptPair hc h (by simp))).trans hA,
        (hKeep _ (keptPair hc h (by simp))).trans hB⟩
    · exact finishStatsOrigin hp hPc hOrigin
  have crossing (hNext : u.pc = s.pc+1)
      (hFire : 7932 ≤ s.pc → s.pc < 7935 → statsOrigin l g u) :
      (7932 < u.pc → u.pc < 7935 → statsOrigin l g u) ∧
      (7935 ≤ u.pc → u.pc < 9205 → 7935 ≤ s.pc ∨ u.pc = 7935 ∧ statsOrigin l g u) := by
    constructor
    · intro hlo hhi
      exact hFire (by omega) (by omega)
    · intro hlo hhi
      by_cases hs : 7935 ≤ s.pc
      · exact .inl hs
      · exact .inr ⟨by omega, hFire (by omega) (by omega)⟩
  rcases hStep with ⟨_, ht⟩ | ⟨event, _, he⟩
  · have hOff : s.pc ∉ Assumptions.swExp2Sites := by
      simp only [Assumptions.swExp2Sites, List.mem_cons, List.not_mem_nil, or_false]
      omega
    obtain ⟨ins, hc, hf, hStep⟩ := correctionTauFrame hOff ht
    rcases hStep with ⟨rfl, hGuard⟩ | ⟨_, _, hLocal⟩
    · obtain ⟨hA, hB⟩ := crossing rfl (fun h₁ h₂ => by
        rw [(inStatsSetup h₁ h₂ hc).1] at hGuard
        cases hGuard)
      exact carry hc (fun _ _ => rfl) hA hB
    · have hKeep (r : Nat) (hr : r ∉ statsWrites ins.op) : u.regs r = s.regs r :=
        hLocal.regs r (fun h => hr (List.mem_append_left _ h))
      have hPc := hLocal.pc
      cases ho : ins.op <;> simp only [ho, nextPc, BrxTarget, or_false] at hPc
      case bra dest uni =>
        have hCode := statsAuditAt hLo hHi hc
        simp only [statsFrameCode, ho, Bool.and_eq_true, Bool.or_eq_true] at hCode
        have hNot := hCode.2.1
        have hDest := hCode.2.2
        apply carry hc hKeep
        · intro hl hh
          exfalso
          have hBad : (7932 < dest && dest < 7935) = true := by simp [← hPc, hl, hh]
          rw [hBad] at hNot
          contradiction
        · intro hl hh
          exact .inl (by
            rcases hDest with h | h
            · simpa using h
            · have h := of_decide_eq_true h
              omega)
      case brx =>
        have hCode := statsAuditAt hLo hHi hc
        simp [statsFrameCode, ho] at hCode
      all_goals
        obtain ⟨hA, hB⟩ := crossing hPc (fun h₁ h₂ =>
          appendStatsOrigin h₁ h₂ hf hFrame hPc ht)
        exact carry hc hKeep hA hB
  · obtain ⟨ins, hc, hl, _⟩ := estep_event_source he
    have hCode := statsAuditAt hLo hHi hc
    simp only [statsFrameCode, hl, Bool.false_or, Bool.and_eq_true] at hCode
    have hEv := hCode.1.1.1
    have hKeep (r : Nat) (hr : r ∉ statsWrites ins.op) : u.regs r = s.regs r :=
      (correctionEventProgress hc hEv hSub
        (fun hm => hr (List.mem_append_right _ hm)) he).2
    have hPos := (correctionEventProgress hc hEv hSub (r := 1062)
      (fun hm => keptWarp hc (List.mem_append_right _ hm)) he).1.pc
    have hNo (h₁ : 7932 ≤ s.pc) (h₂ : s.pc < 7935) : False := by
      rw [(inStatsSetup h₁ h₂ hc).2.1] at hl
      cases hl
    rcases hPos with ⟨hPc, _⟩ | ⟨hPc, _⟩
    · obtain ⟨hA, hB⟩ := crossing hPc (fun h₁ h₂ => (hNo h₁ h₂).elim)
      exact carry hc hKeep hA hB
    · exact carry hc hKeep (fun hl hh => (hNo (by omega) (by omega)).elim)
        (fun hl _ => .inl (by omega))

/-- The correction warp reads statistics from these two groups of named barriers. -/
def correctionStatsSites (stage : Fin 2) : List Nat :=
  if stage.val = 0 then [7985, 8006, 8465] else [7988, 8225, 8761]

private theorem correctionBarrierCode (stage : Fin 2) {pc : Nat}
    (hc : pc ∈ correctionStatsSites stage) :
    kernel.code[pc]? = some ⟨none, .barSyncN (.reg (statsBarrierReg stage)) (.imm 64) true⟩ := by
  fin_cases stage <;> simp [correctionStatsSites] at hc
  all_goals rcases hc with rfl | rfl | rfl
  · exact Flow.code_7985
  · exact Flow.code_8006
  · exact Flow.code_8465
  · exact Flow.code_7988
  · exact Flow.code_8225
  · exact Flow.code_8761

private theorem correctionBarrierTemplate {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} {t : TState} (stage : Fin 2) (hPc : t.pc ∈ correctionStatsSites stage)
    (hf : t.fault = none) (hR : statsRegisters l g t) :
    out kernel Assumptions.all l g t =
      .ev (.bar (statsBarrierId l g stage) (next t) (some 64) .sync) := by
  have hReg : t.regs (statsBarrierReg stage) = some (b32 (statsBarrierId l g stage)) := by
    fin_cases stage
    · exact hR.1
    · exact hR.2
  have hId : statsBarrierId l g stage < 16 := by
    have hWarp := Nat.mod_lt (warpIndex l g) (by decide : 0 < 4)
    have := stage.isLt
    unfold statsBarrierId
    omega
  have hWord := readBits_b32 (L := l) (g := g) hReg (by omega : statsBarrierId l g stage < 2^32)
  have hIdNat : (BitVec.ofNat 64 (statsBarrierId l g stage)).toNat = statsBarrierId l g stage :=
    toNat_ofNat_lt (by omega)
  have hCount : 64 ≠ l.block := by rw [hp.block]; decide
  have hImm : readBits l g t 32 (.imm 64) = .ok 64#64 := rfl
  rw [out_event hf (correctionBarrierCode stage hPc) rfl rfl]
  change Out.ev (barTmpl l g t (.reg (statsBarrierReg stage)) (some (.imm 64)) .sync) = _
  simp [barTmpl, hWord, hIdNat, hImm, hCount, show ¬16 ≤ statsBarrierId l g stage by omega]

/-- Every actual correction statistics wait has the ID of its decoded stage and warp. -/
theorem actualCorrectionStatsBarrierId {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g j pc id : Nat} {cnt : Option Nat} {mode : BarMode} (stage : Fin 2)
    (hSite : pc ∈ correctionStatsSites stage)
    (he : X.get (g,j) = some ⟨pc, .bar id cnt mode⟩) :
    id = statsBarrierId l g stage := by
  have hPc : 7935 ≤ pc ∧ pc < 9205 := by
    fin_cases stage <;> simp [correctionStatsSites] at hSite <;> omega
  have hHint : pc ∉ registerHintSites := by
    simp only [registerHintSites, List.mem_cons, List.not_mem_nil, or_false]
    omega
  have hRole := roleBodyPcOfEvent hp hX (g := g) he (show 173 < pc by omega) hHint
  change roleBodyPc (warpIndex l g) pc at hRole
  have hw : 8 ≤ warpIndex l g ∧ warpIndex l g < 12 := by
    rcases hRole with h | h
    · omega
    · split_ifs at h <;> omega
  obtain ⟨t, o, htPc, _, ht, hEStep⟩ := correctionRoleEventWith hp hX (g := g) hw.1 hw.2 he
    (show 173 < pc by omega) hPc.2 (Q := statsFrame l g) (fun t hAt => by
      have hWarp : t.regs 1062 = some (b32 (warpIndex l g)) :=
        holds_mem hAt.2.2.2.2 (by simp [nonzeroBarrierFacts])
      exact ⟨hWarp, fun h _ => (by rw [hAt.1] at h; omega : False).elim,
        fun h _ => (by rw [hAt.1] at h; omega : False).elim⟩)
    (fun hLo hHi hSub hs h => statsFrameStep hp hLo hHi hSub hs h)
  change t.pc = pc at htPc
  obtain ⟨tm, hOut, hFire⟩ := hEStep
  have hFault : t.fault = none := by
    cases hf : t.fault with
    | none => rfl
    | some f =>
      have hEq : out kernel Assumptions.all l g t = .ev (.ub f) := by simp [out, hf]
      obtain rfl := Out.ev.inj (hOut.symm.trans hEq)
      exact Kind.noConfusion (congrArg Event.kind hFire.1)
  have hTemplate := correctionBarrierTemplate hp stage (htPc.symm ▸ hSite) hFault
    (ht.2.2 (by omega) (by omega))
  obtain rfl := Out.ev.inj (hOut.symm.trans hTemplate)
  exact (Kind.bar.inj (congrArg Event.kind hFire.1)).1

end PTX.Kernels.TmlFa4Fwd.Correction
