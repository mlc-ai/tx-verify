-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxMbarAddress
public import Kernels.TmlFa4Fwd.Proof.StatsBarrierSetup
import Kernels.TmlFa4Fwd.Proof.MmaLinearEvents
import Kernels.TmlFa4Fwd.Proof.EpilogueWarpReady
import Kernels.TmlFa4Fwd.Proof.OutputAssignedBox
import Kernels.TmlFa4Fwd.Proof.EpiloguePrefixStartup
import Kernels.TmlFa4Fwd.Proof.EpilogueCuts
import Kernels.TmlFa4Fwd.Proof.OutputFrame
import Kernels.TmlFa4Fwd.Proof.MmaLoopEntryBound
import Lemmas.Flow.NotClc
import Lemmas.Step.CtaBar
import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopEvents
import Kernels.TmlFa4Fwd.Proof.RoleDispatch
import Kernels.TmlFa4Fwd.Proof.PrologueDispatchTrace
import Kernels.TmlFa4Fwd.Proof.PrologueWarp0Prefix
import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopFlow
import Kernels.TmlFa4Fwd.Proof.LoaderCountExit
import Kernels.TmlFa4Fwd.Proof.Thread.DecodedEventFrame
import Kernels.TmlFa4Fwd.Flow.Code.Part068
import Kernels.TmlFa4Fwd.Flow.Code.Part088
import Kernels.TmlFa4Fwd.Flow.Code.Part107
import Kernels.TmlFa4Fwd.Flow.Code.Part119

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof PTX.EventFrame PTX.Assumption Prologue Mma

private def statsOrigin (l : Launch) (g : Nat) (w : Fin 8) (s : TState) : Prop :=
  ∃ t, At t 3274 [(1062, b32 w.val)] ∧
    run kernel Assumptions.all l g (s.pc-3274) t = some s

private def statsFrame (l : Launch) (g : Nat) (w : Fin 8) (s : TState) : Prop :=
  (s.pc < 3283 → s.sub = 0 ∧ s.acc = []) ∧
    (3274 < s.pc → s.pc < 3283 → statsOrigin l g w s) ∧
    (3283 ≤ s.pc → s.pc < 7742 → s.regs 5127 = some (b32 (3+w.val)))

private def statsWrites (op : Op) : List Nat := writesRegs op ++ scoreEventWrites op

private def statsCode (pc : Nat) (i : Instr) : Bool :=
  (i.op.isLocal || scoreEventOp i.op) &&
  (!decide (pc < 3283) || (i.op.isLocal || (linearEventOp i.op && !allocationOp i.op))) &&
  ((3274 ≤ pc && pc < 3283) || !(statsWrites i.op).contains 5127) &&
  match i.op with
  | .bra dst _ => !(3274 < dst && dst < 3283) &&
      (!decide (pc < 3283) || decide (dst ≤ 3274 ∨ dst = 7742)) &&
      (!decide (3283 ≤ pc) || decide (3283 ≤ dst))
  | .brx .. => false
  | _ => true

private theorem statsCodeAt {pc : Nat} {i : Instr}
    (hLo : 3103 ≤ pc) (hHi : pc < 7742) (hc : kernel.code[pc]? = some i) :
    statsCode pc i = true := by
  let code := ((kernel.code.drop 3103).take (7742-3103)).zipIdx 3103
  have hAll : code.all (fun (ins, pc) => statsCode pc ins) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  apply List.all_eq_true.mp hAll (i, pc)
  apply List.mem_of_getElem? (i := pc-3103)
  dsimp only [code]
  rw [List.getElem?_zipIdx, List.getElem?_take_of_lt (by omega), List.getElem?_drop,
    Nat.add_sub_of_le hLo, hc]
  rfl

private theorem setupIsLocal {pc : Nat} {ins : Instr} (hLo : 3274 ≤ pc) (hHi : pc < 3283)
    (hc : kernel.code[pc]? = some ins) : ins.guard = none ∧ ins.op.isLocal = true := by
  let code := (kernel.code.drop 3274).take 9
  have hAll : code.all (fun i => i.guard.isNone && i.op.isLocal) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  have hi : code[pc-3274]? = some ins := by
    dsimp only [code]
    rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_sub_of_le hLo]
    exact hc
  have h := List.all_eq_true.mp hAll _ (List.mem_of_getElem? hi)
  exact ⟨Option.isNone_iff_eq_none.mp (Bool.and_eq_true_iff.mp h).1,
    (Bool.and_eq_true_iff.mp h).2⟩

private theorem extendOrigin {l : Launch} {g : Nat} {w : Fin 8} {s u : TState}
    (hLo : 3274 ≤ s.pc) (hHi : s.pc < 3283) (hf : s.fault = none)
    (hWarp : s.regs 1062 = some (b32 w.val)) (hFrame : statsFrame l g w s)
    (hNext : u.pc = s.pc+1) (ht : Tau kernel Assumptions.all l g s u) :
    statsOrigin l g w u := by
  have hStep : run kernel Assumptions.all l g 1 s = some u := by
    simp only [run, tauStep_iff.mpr ht, Option.bind_some]
  rcases Nat.eq_or_lt_of_le hLo with h | h
  · obtain ⟨hSub, hAcc⟩ := hFrame.1 hHi
    exact ⟨s, ⟨h.symm, hSub, hAcc, hf, hWarp, trivial⟩, by rw [hNext, ← h]; exact hStep⟩
  · obtain ⟨t, hT, hr⟩ := hFrame.2.1 h hHi
    exact ⟨t, hT, by
      rw [hNext, show s.pc+1-3274 = (s.pc-3274)+1 by omega]
      exact run_comp hr hStep⟩

private theorem finishOrigin {l : Launch} {g : Nat} {w : Fin 8} {u : TState}
    (hPc : u.pc = 3283) (hOrigin : statsOrigin l g w u) :
    u.regs 5127 = some (b32 (3+w.val)) := by
  obtain ⟨t, hT, hr⟩ := hOrigin
  obtain ⟨s, hRun, hS⟩ := softmaxStatsBarrierSetup l g w t hT
  rw [hPc] at hr
  obtain rfl := Option.some.inj (hr.symm.trans hRun)
  exact hS.2.2.2.2.1

private theorem frameStep {l : Launch} {g : Nat} {s u : TState} {e : Option Event} (w : Fin 8)
    (hLo : 3103 ≤ s.pc) (hHi : s.pc < 7742) (hSub : s.sub ≤ 3)
    (hWarp : s.regs 1062 = some (b32 w.val)) (hFrame : statsFrame l g w s)
    (hStep : WStep kernel Assumptions.all l g s e u) :
    statsFrame l g w u := by
  have carry {ins : Instr} (hc : kernel.code[s.pc]? = some ins)
      (hShape : u.pc < 3283 → u.sub = 0 ∧ u.acc = [])
      (hKeep : 5127 ∉ statsWrites ins.op → u.regs 5127 = s.regs 5127)
      (hInside : 3274 < u.pc → u.pc < 3283 → statsOrigin l g w u)
      (hAfter : 3283 ≤ u.pc → u.pc < 7742 →
        3283 ≤ s.pc ∨ u.pc = 3283 ∧ statsOrigin l g w u) : statsFrame l g w u := by
    refine ⟨hShape, hInside, ?_⟩
    intro hu huEnd
    rcases hAfter hu huEnd with h | ⟨hPc, hOrigin⟩
    · have hc' := statsCodeAt hLo hHi hc
      simp only [statsCode, Bool.and_eq_true] at hc'
      have hKeep' : 5127 ∉ statsWrites ins.op := by
        simpa [show ¬s.pc < 3283 by omega] using hc'.1.2
      exact (hKeep hKeep').trans (hFrame.2.2 h hHi)
    · exact finishOrigin hPc hOrigin
  have crossing (hNext : u.pc = s.pc+1)
      (hFire : 3274 ≤ s.pc → s.pc < 3283 → statsOrigin l g w u) :
      (3274 < u.pc → u.pc < 3283 → statsOrigin l g w u) ∧
      (3283 ≤ u.pc → u.pc < 7742 → 3283 ≤ s.pc ∨ u.pc = 3283 ∧ statsOrigin l g w u) := by
    constructor
    · intro hlo hhi
      exact hFire (by omega) (by omega)
    · intro hlo hhi
      by_cases hs : 3283 ≤ s.pc
      · exact .inl hs
      · exact .inr ⟨by omega, hFire (by omega) (by omega)⟩
  rcases hStep with ⟨_, ht⟩ | ⟨_, _, he⟩
  · obtain ⟨ins, hc, hf, hSource⟩ := tauScoreSource ht
    rcases hSource with ⟨rfl, hGuard⟩ | ⟨_, _, hExec⟩
    · obtain ⟨hA, hB⟩ := crossing rfl (fun h₁ h₂ => by
        rw [(setupIsLocal h₁ h₂ hc).1] at hGuard
        cases hGuard)
      exact carry hc (fun _ => ⟨rfl, rfl⟩) (fun _ => rfl) hA hB
    · rcases scoreExecLocal hExec with hLocal | ⟨m, hSite, hm, hRun⟩
      · have hKeep (hr : 5127 ∉ statsWrites ins.op) : u.regs 5127 = s.regs 5127 :=
          hLocal.regs _ (fun h => hr (List.mem_append_left _ h))
        have hShape (h : s.pc < 3283) : u.sub = 0 ∧ u.acc = [] :=
          ⟨hLocal.sub.trans (hFrame.1 h).1, hLocal.acc.trans (hFrame.1 h).2⟩
        have hPc := hLocal.pc
        cases ho : ins.op <;> simp only [ho, nextPc, BrxTarget, or_false] at hPc
        case bra dest uni =>
          have hCode := statsCodeAt hLo hHi hc
          simp only [statsCode, ho, Bool.and_eq_true, Bool.or_eq_true] at hCode
          have hBounds := hCode.2
          refine carry hc ?_ hKeep ?_ ?_
          · intro hU
            apply hShape
            rcases hBounds.2 with h | h
            · simpa using h
            · have h := of_decide_eq_true h
              omega
          · intro hlo hhi
            have hBad : (3274 < dest && dest < 3283) = true := by simp [← hPc, hlo, hhi]
            have hNot := hBounds.1.1
            rw [hBad] at hNot
            contradiction
          · intro hl hh
            exact .inl (by
              rcases hBounds.1.2 with h | h
              · simpa using h
              · have h := of_decide_eq_true h
                omega)
        case brx =>
          have hCode := statsCodeAt hLo hHi hc
          simp [statsCode, ho] at hCode
        all_goals
          obtain ⟨hA, hB⟩ := crossing hPc (fun h₁ h₂ =>
            extendOrigin h₁ h₂ hf hWarp hFrame hPc ht)
          exact carry hc (fun h => hShape (by omega)) hKeep hA hB
      · have hAll : Assumptions.swExp2Sites.all (fun pc =>
          match cuteExp2.matchAt kernel pc with
          | none => false
          | some m => 3283 ≤ pc && 3283 ≤ m.stop && !(scoreSegmentWrites m).contains 5127) =
            true := by
            set_option maxRecDepth 100000 in kernel_rfl
        have hAudit := List.all_eq_true.mp hAll _ hSite
        rw [hm] at hAudit
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hAudit
        obtain ⟨hPc, _, _, hKeep⟩ := scoreSegmentFrame hRun
        refine ⟨fun h => (by omega : False).elim, fun _ h => (by omega : False).elim, ?_⟩
        intro _ _
        exact (hKeep _ (by simpa using hAudit.2)).trans (hFrame.2.2 hAudit.1.1 hHi)
  · obtain ⟨ins, hc, hl, hFire⟩ := estep_event_source he
    have hCode := statsCodeAt hLo hHi hc
    simp only [statsCode, hl, Bool.false_or, Bool.and_eq_true] at hCode
    have hEv := hCode.1.1.1
    have hKeep (hr : 5127 ∉ statsWrites ins.op) : u.regs 5127 = s.regs 5127 :=
      (scoreEventStep hc hEv hSub (fun hm => hr (List.mem_append_right _ hm)) he).2
    have hOrd : Epilogue.ordinaryEvent ins.op = true := by
      cases ho : ins.op <;> first | rfl | simp [ho, scoreEventOp] at hEv
    have hProgress := callbackFrame_fires (Epilogue.ordinaryEventFrame hOrd) hFire
    have hNo (h₁ : 3274 ≤ s.pc) (h₂ : s.pc < 3283) : False := by
      rw [(setupIsLocal h₁ h₂ hc).2] at hl
      cases hl
    have hShape (h : s.pc < 3283) : u.sub = 0 ∧ u.acc = [] := by
      have hA := hCode.1.1.2
      simp only [h, decide_true, Bool.not_true, Bool.false_or, Bool.and_eq_true] at hA
      obtain ⟨hSub0, hAcc⟩ := hFrame.1 h
      obtain ⟨_, hAcc', hPos | hAlloc | hFault⟩ :=
        linearEventProgressWithSub hc hA.1 (hSub0 ▸ Nat.zero_le 1) hAcc he
      · exact ⟨hPos.2.2.elim id (fun q => q.1.trans hSub0), hAcc'⟩
      · simp [hAlloc.2.2.2] at hA
      · exact ⟨hFault.2.1.trans hSub0, hAcc'⟩
    rcases hProgress with hPc | hPc
    · exact carry hc (fun h => hShape (by omega)) hKeep
        (fun hl hh => (hNo (by omega) (by omega)).elim) (fun hl _ => .inl (by omega))
    · obtain ⟨hA, hB⟩ := crossing hPc (fun h₁ h₂ => (hNo h₁ h₂).elim)
      exact carry hc (fun h => hShape (by omega)) hKeep hA hB

/-- The four decoded softmax statistics notifications. -/
def softmaxStatsSites : List Nat := [4397, 5683, 6891, 7616]

private theorem softmaxBarrierCode {pc : Nat} (hc : pc ∈ softmaxStatsSites) :
    kernel.code[pc]? = some ⟨none, .barArrive (.reg 5127) (.imm 64) true⟩ := by
  simp only [softmaxStatsSites, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact Flow.code_4397
  · exact Flow.code_5683
  · exact Flow.code_6891
  · exact Flow.code_7616

private theorem softmaxBarrierTemplate {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} {t : TState} (warp : Fin 8) (hPc : t.pc ∈ softmaxStatsSites)
    (hf : t.fault = none) (hR : t.regs 5127 = some (b32 (3+warp.val))) :
    out kernel Assumptions.all l g t = .ev (.bar (3+warp.val) (next t) (some 64) .arrive) := by
  have hWarp := warp.isLt
  have hWord := readBits_b32 (L := l) (g := g) hR (by omega : 3+warp.val < 2^32)
  have hIdNat : (BitVec.ofNat 64 (3+warp.val)).toNat = 3+warp.val := toNat_ofNat_lt (by omega)
  have hCount : 64 ≠ l.block := by rw [hp.block]; decide
  have hImm : readBits l g t 32 (.imm 64) = .ok 64#64 := rfl
  rw [out_event hf (softmaxBarrierCode hPc) rfl rfl]
  change Out.ev (barTmpl l g t (.reg 5127) (some (.imm 64)) .arrive) = _
  simp [barTmpl, hWord, hIdNat, hImm, hCount, show ¬16 ≤ 3+warp.val by omega]

/-- Every actual softmax statistics notification has the ID of its issuing warp. -/
theorem actualSoftmaxStatsBarrierId {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g j pc id : Nat} {cnt : Option Nat} {mode : BarMode} (hSite : pc ∈ softmaxStatsSites)
    (he : X.get (g,j) = some ⟨pc, .bar id cnt mode⟩) :
    id = 3 + warpIndex l g := by
  have hPc : 3420 ≤ pc ∧ pc < 7742 := by
    simp only [softmaxStatsSites, List.mem_cons, List.not_mem_nil, or_false] at hSite
    omega
  obtain ⟨w, hWarp, t, o, htPc, ht, hEStep⟩ := softmaxRoleEventWith hp hX (g := g) he
    hPc.1 hPc.2 (Q := statsFrame l g) (fun w t hAt => by
      exact ⟨fun _ => ⟨hAt.2.1, hAt.2.2.1⟩, fun h _ => (by rw [hAt.1] at h; omega : False).elim,
        fun h _ => (by rw [hAt.1] at h; omega : False).elim⟩)
    (fun w {_ _ _} hLo hHi hSub hW hs h => frameStep w hLo hHi hSub hW hs h)
  change t.pc = pc at htPc
  obtain ⟨tm, hOut, hFire⟩ := hEStep
  have hFault : t.fault = none := by
    cases hf : t.fault with
    | none => rfl
    | some f =>
      have hEq : out kernel Assumptions.all l g t = .ev (.ub f) := by simp [out, hf]
      obtain rfl := Out.ev.inj (hOut.symm.trans hEq)
      exact Kind.noConfusion (congrArg Event.kind hFire.1)
  have hTemplate := softmaxBarrierTemplate hp (g := g) w (htPc.symm ▸ hSite) hFault
    (ht.2.2 (by omega) (by omega))
  obtain rfl := Out.ev.inj (hOut.symm.trans hTemplate)
  rw [← hWarp]
  exact (Kind.bar.inj (congrArg Event.kind hFire.1)).1

end PTX.Kernels.TmlFa4Fwd.Softmax
