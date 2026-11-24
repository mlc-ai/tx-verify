-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.StatisticsAddressReplay
import Kernels.TmlFa4Fwd.Proof.SoftmaxMbarAddress
import Kernels.TmlFa4Fwd.Proof.LoaderEntry
import Kernels.TmlFa4Fwd.Flow.Code.Part088
import Kernels.TmlFa4Fwd.Flow.Code.Part104
import Kernels.TmlFa4Fwd.Flow.Code.Part107
import Lemmas.Execution.EventFrameSource

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Scores
open PTX PTX.Flow PTX.Proof PTX.EventFrame PTX.Assumption Prologue Softmax

noncomputable section

private def addressWindows : List StatisticsAddressWindow :=
  [.biased, .plainSetup, .plain, .final]

private theorem addressWindowMem (w : StatisticsAddressWindow) : w ∈ addressWindows := by
  cases w <;> decide

private def inAddress (w : StatisticsAddressWindow) (pc : Nat) : Prop :=
  w.start < pc ∧ pc ≤ w.stop

private instance (w : StatisticsAddressWindow) (pc : Nat) : Decidable (inAddress w pc) :=
  inferInstanceAs (Decidable (w.start < pc ∧ pc ≤ w.stop))

private def inPlain (pc : Nat) : Prop := 6664 ≤ pc ∧ pc < 7605

private instance (pc : Nat) : Decidable (inPlain pc) :=
  inferInstanceAs (Decidable (6664 ≤ pc ∧ pc < 7605))

private def allowedLanding (src dst : Nat) : Bool :=
  (addressWindows.all fun w => !decide (inAddress w dst)) &&
  decide (inPlain dst → inPlain src) && decide (dst ≠ 7615)

private def preserved (rs : List Nat) (writes : List Nat) : Bool :=
  rs.all fun r => !writes.contains r

private def addressCode (pc : Nat) (i : Instr) : Bool :=
  let writes := writesRegs i.op ++ scoreEventWrites i.op
  (i.op.isLocal || scoreEventOp i.op) && preserved [2535] writes &&
    (if inPlain pc then preserved [5176, 5177] writes else true) &&
    (addressWindows.all fun w =>
      if w.start ≤ pc ∧ pc < w.stop then i.op.isLocal else true) &&
    match i.op with
    | .bra dst _ => allowedLanding pc dst
    | .brx .. => false
    | _ => true

private theorem addressCodeAt {pc : Nat} {i : Instr} (hl : 3103 ≤ pc) (hh : pc < 7742)
    (hc : kernel.code[pc]? = some i) : addressCode pc i = true := by
  let code := ((kernel.code.drop 3103).take (7742 - 3103)).zipIdx 3103
  have hAll : code.all (fun (ins, src) => addressCode src ins) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  have hAt : code[pc-3103]? = some (i, pc) := by
    dsimp only [code]
    rw [List.getElem?_zipIdx, List.getElem?_take_of_lt (by omega), List.getElem?_drop,
      Nat.add_sub_of_le hl, hc]
    rfl
  exact List.all_eq_true.mp hAll _ (List.mem_of_getElem? hAt)

private theorem allowedLandingFacts {src dst : Nat} (h : allowedLanding src dst = true) :
    (∀ w, ¬ inAddress w dst) ∧ (inPlain dst → inPlain src) ∧ dst ≠ 7615 := by
  simp only [allowedLanding, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨fun w => by
    simpa using List.all_eq_true.mp h.1.1 w (addressWindowMem w), h.1.2, h.2⟩

private theorem segmentLanding {pc : Nat} {m : SegMatch CuteSlot}
    (hs : pc ∈ Assumptions.swExp2Sites) (hm : cuteExp2.matchAt kernel pc = some m) :
    allowedLanding pc m.stop = true ∧
      preserved [2535, 5176, 5177] (scoreSegmentWrites m) = true := by
  have hAll : Assumptions.swExp2Sites.all (fun src =>
    match cuteExp2.matchAt kernel src with
    | none => false
    | some mat => allowedLanding src mat.stop &&
        preserved [2535, 5176, 5177] (scoreSegmentWrites mat)) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  have h := List.all_eq_true.mp hAll _ hs
  rw [hm] at h
  exact Bool.and_eq_true_iff.mp h

private theorem keepsOfAudit {r : Nat} {rs writes : List Nat}
    (h : preserved rs writes = true) (hr : r ∈ rs) : r ∉ writes := by
  simpa [preserved] using List.all_eq_true.mp h r hr

private def AddressOrigin (l : Launch) (g : Nat) (warp : Fin 8) (s : TState)
    (w : StatisticsAddressWindow) : Prop :=
  ∃ t, At t w.start (w.entry l g warp) ∧
    run kernel Assumptions.all l g (s.pc - w.start) t = some s

private structure AddressFrame (l : Launch) (g : Nat) (warp : Fin 8) (s : TState) : Prop where
  shared : s.regs 2535 = some (b32 l.sharedBase)
  scratch : ScoreScratchState s
  plain : inPlain s.pc → s.regs 5176 = some (b32 (128 * (warp.val / 4))) ∧
    s.regs 5177 = some (b32 (g % l.block))
  origin : ∀ w, inAddress w s.pc → AddressOrigin l g warp s w
  maxWord : s.pc = 7615 → s.regs 5814 = some (b32 (statsBase l g warp))

private theorem originResult {p : Params} {l : Launch} {m : Mem0} {g : Nat}
    {warp : Fin 8} {s : TState} {w : StatisticsAddressWindow}
    (hp : Pre p l m) (hw : warp.val = warpIndex l g) (hPc : s.pc = w.stop)
    (h : AddressOrigin l g warp s w) : Holds s.regs (w.result l g warp) := by
  obtain ⟨t, ht, hr⟩ := h
  obtain ⟨u, hu, hU⟩ := (w.replay hp g warp hw).apply ht
  rw [hPc] at hr
  exact Option.some.inj (hu.symm.trans hr) ▸ hU.2.2.2.2

private theorem scalarStoreAdvances {l : Launch} {g base : Nat} {off : Int} {src : Opnd}
    {s u : TState} {e : Event}
    (hf : Fires s.pc (storeTmpl l g s .shared 32 base off [src]) e (some u)) :
    u.pc = s.pc + 1 ∧ u.regs = s.regs := by
  unfold storeTmpl at hf
  repeat' split at hf
  all_goals first
    | have hu := Option.some.inj hf.2
      exact ⟨by rw [hu]; simp [afterStore], by rw [hu]; simp [afterStore]⟩
    | cases hf.2

private theorem windowStoreAdvances {l : Launch} {g : Nat} {s u : TState}
    {e : Event} (w : StatisticsAddressWindow) (hPc : s.pc = w.stop)
    (he : EStep kernel Assumptions.all l g s e (some u)) :
    u.pc = s.pc + 1 ∧ u.regs = s.regs := by
  obtain ⟨i, hc, hn, hf⟩ := estep_event_source he
  cases w
  · rw [hPc] at hc
    change kernel.code[5682]? = some i at hc
    rw [Flow.code_5682] at hc
    obtain rfl := Option.some.inj hc
    exact scalarStoreAdvances (base := 4571) (off := 368) (src := .reg 1362) hf
  · rw [hPc] at hc
    change kernel.code[6664]? = some i at hc
    rw [Flow.code_6664] at hc
    obtain rfl := Option.some.inj hc
    cases hn
  · rw [hPc] at hc
    change kernel.code[6890]? = some i at hc
    rw [Flow.code_6890] at hc
    obtain rfl := Option.some.inj hc
    exact scalarStoreAdvances (base := 5518) (off := 368) (src := .reg 1492) hf
  · rw [hPc] at hc
    change kernel.code[7614]? = some i at hc
    rw [Flow.code_7614] at hc
    obtain rfl := Option.some.inj hc
    exact scalarStoreAdvances (base := 5814) (off := 368) (src := .reg 7257) hf

private theorem regionStep {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} {warp : Fin 8} {s u : TState} {e : Option Event} (hw : warp.val = warpIndex l g)
    (hl : 3103 ≤ s.pc) (hh : s.pc < 7742) (hSub : s.sub ≤ 3)
    (hWarp : s.regs 1062 = some (b32 warp.val)) (hF : AddressFrame l g warp s)
    (hStep : WStep kernel Assumptions.all l g s e u) : AddressFrame l g warp u := by
  have carry (keep : ∀ r ∈ [2535, 5176, 5177], u.regs r = s.regs r)
      (hScratch : ScoreScratchState u) (hLanding : allowedLanding s.pc u.pc = true) :
      AddressFrame l g warp u := by
    obtain ⟨hOutside, hPlain, hMax⟩ := allowedLandingFacts hLanding
    refine ⟨(keep _ (by decide)).trans hF.shared, hScratch, ?_, ?_, fun h => (hMax h).elim⟩
    · intro hP
      obtain ⟨h1, h2⟩ := hF.plain (hPlain hP)
      exact ⟨(keep _ (by decide)).trans h1, (keep _ (by decide)).trans h2⟩
    · exact fun w h => (hOutside w h).elim
  have finish {i : Instr} (hc : kernel.code[s.pc]? = some i)
      (keep : ∀ r, r ∉ writesRegs i.op ++ scoreEventWrites i.op → u.regs r = s.regs r)
      (hScratch : ScoreScratchState u)
      (hOrigin : ∀ w, inAddress w u.pc → AddressOrigin l g warp u w)
      (hPlain : inPlain u.pc → inPlain s.pc ∨ u.pc = 6664)
      (hMax : u.pc = 7615 → u.regs 5814 = some (b32 (statsBase l g warp))) :
      AddressFrame l g warp u := by
    have hCode := addressCodeAt hl hh hc
    simp only [addressCode, Bool.and_eq_true] at hCode
    refine ⟨(keep _ (keepsOfAudit hCode.1.1.1.2 (by decide))).trans hF.shared,
      hScratch, ?_, hOrigin, hMax⟩
    intro hU
    rcases hPlain hU with hS | hEnd
    · have hA := hCode.1.1.2
      rw [ite_eq_left hS] at hA
      obtain ⟨h1, h2⟩ := hF.plain hS
      exact ⟨(keep _ (keepsOfAudit hA (by decide))).trans h1,
        (keep _ (keepsOfAudit hA (by decide))).trans h2⟩
    · have hAt : inAddress .plainSetup u.pc := by rw [hEnd]; decide
      have h := originResult hp hw (w := .plainSetup) hEnd (hOrigin _ hAt)
      exact ⟨h.2.1, h.1⟩
  have stepForward (hPc : u.pc = s.pc + 1) : inPlain u.pc → inPlain s.pc ∨ u.pc = 6664 := by
    unfold inPlain
    omega
  have maxFromStore (hPc : u.pc = s.pc + 1) (hRegs : u.regs = s.regs) :
      u.pc = 7615 → u.regs 5814 = some (b32 (statsBase l g warp)) := by
    intro hu
    have hs : s.pc = 7614 := by omega
    have hAt : inAddress .final s.pc := by rw [hs]; decide
    rw [hRegs]
    exact (originResult hp hw (w := .final) hs (hF.origin _ hAt)).1
  have localOrigin {i : Instr} (hc : kernel.code[s.pc]? = some i) (hf : s.fault = none)
      (ht : Tau kernel Assumptions.all l g s u) (hPc : u.pc = s.pc + 1) :
      ∀ w, inAddress w u.pc → AddressOrigin l g warp u w := by
    intro w hu
    have hRange : w.start ≤ s.pc ∧ s.pc < w.stop := by unfold inAddress at hu; omega
    have hCode := addressCodeAt hl hh hc
    simp only [addressCode, Bool.and_eq_true] at hCode
    have hLoc := List.all_eq_true.mp hCode.1.2 w (addressWindowMem w)
    rw [ite_eq_left hRange] at hLoc
    have hRun : run kernel Assumptions.all l g 1 s = some u := by
      simp only [run, tauStep_iff.mpr ht, Option.bind_some]
    rcases Nat.eq_or_lt_of_le hRange.1 with h | h
    · obtain ⟨hSub, hAcc⟩ := scratchClearOfLocal hc hLoc hF.scratch
      have hEntry : Holds s.regs (w.entry l g warp) := by
        cases w
        case plain =>
          have hP : inPlain s.pc := by rw [← h]; decide
          have coords := hF.plain hP
          exact ⟨coords.2, coords.1, hF.shared, trivial⟩
        all_goals exact ⟨hWarp, hF.shared, trivial⟩
      exact ⟨s, ⟨h.symm, hSub, hAcc, hf, hEntry⟩, by
        rw [hPc, show s.pc + 1 - w.start = 1 by omega]
        exact hRun⟩
    · obtain ⟨t, hT, hR⟩ := hF.origin w ⟨h, hRange.2.le⟩
      exact ⟨t, hT, by
        rw [hPc, show s.pc + 1 - w.start = (s.pc - w.start) + 1 by omega]
        exact run_comp hR hRun⟩
  have noLocalAtSum {i : Instr} (hc : kernel.code[s.pc]? = some i)
      (ht : Tau kernel Assumptions.all l g s u) (hPc : u.pc = s.pc + 1) :
      u.pc ≠ 7615 := by
    intro h
    have hs : s.pc = 7614 := by omega
    rw [hs, Flow.code_7614] at hc
    obtain rfl := Option.some.inj hc
    obtain ⟨j, hj, _, hOp⟩ := tauScoreSource ht
    rw [hs, Flow.code_7614] at hj
    obtain rfl := Option.some.inj hj
    rcases hOp with ⟨_, h⟩ | ⟨_, h, _⟩ <;> cases h
  rcases hStep with ⟨rfl, ht⟩ | ⟨e, rfl, he⟩
  · obtain ⟨i, hc, hf, hSource⟩ := tauScoreSource ht
    rcases hSource with ⟨rfl, _⟩ | ⟨_, hLoc, hExec⟩
    · exact finish hc (fun _ _ => rfl) (scratchStateOfClear ⟨rfl, rfl⟩)
        (localOrigin hc hf ht rfl) (stepForward rfl) (fun h => (noLocalAtSum hc ht rfl h).elim)
    rcases scoreExecLocal hExec with hFrame | ⟨m, hs, hm, hSegment⟩
    · obtain ⟨hS, hA⟩ := scratchClearOfLocal hc hLoc hF.scratch
      have hScratch := scratchStateOfClear ⟨hFrame.sub.trans hS, hFrame.acc.trans hA⟩
      have hKeep : ∀ r, r ∉ writesRegs i.op ++ scoreEventWrites i.op → u.regs r = s.regs r :=
        fun r h => hFrame.regs r (fun hm => h (List.mem_append_left _ hm))
      have hCode := (Bool.and_eq_true_iff.mp (addressCodeAt hl hh hc)).2
      have hPc := hFrame.pc
      cases ho : i.op <;> simp only [ho, nextPc, BrxTarget, or_false] at hPc
      case bra dst uni =>
        have hLanding : allowedLanding s.pc u.pc = true := by simpa [ho, hPc] using hCode
        obtain ⟨hOutside, hPlain, hMax⟩ := allowedLandingFacts hLanding
        exact finish hc hKeep hScratch (fun w h => (hOutside w h).elim)
          (fun h => .inl (hPlain h)) (fun h => (hMax h).elim)
      case brx => simp [ho] at hCode
      all_goals
        exact finish hc hKeep hScratch (localOrigin hc hf ht hPc) (stepForward hPc)
          (fun h => (noLocalAtSum hc ht hPc h).elim)
    · obtain ⟨hLanding, hKeep⟩ := segmentLanding hs hm
      have hSeg := scoreSegmentFrame hSegment
      have hScratch : ScoreScratchState u := by
        apply scratchStateOfClear
        refine ⟨hSeg.2.1, ?_⟩
        unfold Assumptions.execSwExp2 at hSegment
        simp only [bind, Except.bind, pure, Except.pure] at hSegment
        split at hSegment
        · split at hSegment
          · contradiction
          · obtain rfl := Except.ok.inj hSegment
            rfl
        · contradiction
      exact carry (fun r hr => hSeg.2.2.2 r (keepsOfAudit hKeep hr))
        hScratch (hSeg.1.symm ▸ hLanding)
  · obtain ⟨i, hc, hl, _⟩ := estep_event_source he
    have hCode := addressCodeAt (by assumption) hh hc
    simp only [addressCode, Bool.and_eq_true, hl, Bool.false_or] at hCode
    have hKeep (r : Nat) (h : r ∉ writesRegs i.op ++ scoreEventWrites i.op) :
        u.regs r = s.regs r :=
      (scoreEventStep hc hCode.1.1.1.1 hSub (fun hm => h (List.mem_append_right _ hm)) he).2
    have hB := keepsOfAudit hCode.1.1.1.2 (by decide : 2535 ∈ [2535])
    have hB' : 2535 ∉ scoreEventWrites i.op := fun h => hB (List.mem_append_right _ h)
    have hProg := (scoreEventStep hc hCode.1.1.1.1 hSub hB' he).1
    have hReady : ScoreScratchReady i.op s := by
      simpa only [ScoreScratchState, hc, hl, Bool.false_eq_true, ite_false] using hF.scratch
    have hScratch : ScoreScratchState u := by
      have hN := scoreEventScratch hc hCode.1.1.1.1 hSub hB' he hReady
      by_cases hEq : u.pc = s.pc
      · simpa only [ScoreScratchState, hEq, hc, hl, Bool.false_eq_true, ite_false, ite_true]
          using hN
      · exact scratchStateOfClear (by simpa only [hEq, ite_false] using hN)
    have noEventIn (w : StatisticsAddressWindow) (hs : w.start ≤ s.pc ∧ s.pc < w.stop) :
        False := by
      have hL := List.all_eq_true.mp hCode.1.2 w (addressWindowMem w)
      rw [ite_eq_left hs] at hL
      cases hL
    rcases hProg.pc with ⟨hPc, _⟩ | ⟨hPc, _⟩
    · refine finish hc hKeep hScratch ?_ (stepForward hPc) ?_
      · intro w h
        unfold inAddress at h
        exact (noEventIn w ⟨by omega, by omega⟩).elim
      · intro h
        have hs : s.pc = 7614 := by omega
        exact maxFromStore hPc (windowStoreAdvances .final hs he).2 h
    · refine finish hc hKeep hScratch ?_ (fun h => .inl (hPc ▸ h)) ?_
      · intro w h
        unfold inAddress at h
        have hs : s.pc = w.stop := by
          by_contra! hn
          exact noEventIn w ⟨by omega, by omega⟩
        have hNext := (windowStoreAdvances w hs he).1
        omega
      · intro h
        have hs : s.pc = 7615 := hPc.symm.trans h
        have hReg : 5814 ∉ writesRegs i.op ++ scoreEventWrites i.op := by
          rw [hs, Flow.code_7615] at hc
          obtain rfl := Option.some.inj hc
          decide
        exact (hKeep _ hReg).trans (hF.maxWord hs)

private theorem initialAddressFrame {l : Launch} {g : Nat} (warp : Fin 8) {s : TState}
    (h : At s 3103 [(1062, b32 warp.val), (2535, b32 l.sharedBase)]) :
    AddressFrame l g warp s := by
  refine ⟨h.2.2.2.2.2.1, scratchStateOfClear ⟨h.2.1, h.2.2.1⟩, ?_, ?_, ?_⟩
  · rw [h.1]
    exact fun hp => (of_decide_eq_true rfl : ¬ inPlain 3103) hp |>.elim
  · intro w hw
    rw [h.1] at hw
    have hNo : ¬ inAddress w 3103 := by cases w <;> decide
    exact (hNo hw).elim
  · rw [h.1]
    exact fun hp => (by decide : 3103 ≠ 7615) hp |>.elim

private theorem storedWordFootprint {p : Params} {l : Launch} {m : Mem0} {g base : Nat}
    {off : Nat} {s : TState} {a : Acc} {bs : List Byte} {src : Opnd} {o : Option TState}
    (hp : Pre p l m) (warp : Fin 8) (hOff : off = 368 ∨ off = 1392)
    (hBase : s.regs base = some (b32 (statsBase l g warp)))
    (hf : Fires s.pc (storeTmpl l g s .shared 32 base (off : Int) [src]) ⟨s.pc, .wr a bs⟩ o) :
    a = {loc := ⟨.shared, g / l.block, statsBase l g warp + off⟩, size := 4} := by
  let dest : Loc := ⟨.shared, g / l.block, statsBase l g warp + off⟩
  have hLane : laneOf l g < 32 := Nat.mod_lt _ (by decide)
  have hw := warp.isLt
  have hSmall : statsBase l g warp + off < 2 ^ 32 := by
    have h := hp.shared.2.1
    unfold statsBase
    omega
  have hAlign : dest.addr % 4 = 0 := by
    have h := hp.shared.1
    dsimp [dest, statsBase]
    omega
  have hAddress : effAddr l g s .shared base (off : Int) = .ok dest :=
    effAddr_b32_off hBase hSmall
  unfold storeTmpl at hf
  rw [hAddress] at hf
  simp only [bind, Except.bind, List.length_singleton] at hf
  rw [elemAcc_ok (by decide) (by simpa using hAlign)] at hf
  cases hSub : s.sub with
  | succ k =>
    simp only [hSub, List.getElem?_cons_succ, List.getElem?_nil, Fires] at hf
    cases (congrArg Event.kind hf.1)
  | zero =>
    simp only [hSub, List.getElem?_cons_zero] at hf
    split at hf
    · cases (congrArg Event.kind hf.1)
    · exact (Kind.wr.inj (congrArg Event.kind hf.1)).1

/-- The softmax role's observation of a statistics store. -/
def StatisticsStore (X : Execution) (i : EvId) (site : Fin 4)
    (access : Acc) (bytes : List Byte) : Prop :=
  X.get i = some ⟨(statsStore site).pc, .wr access bytes⟩

/-- Every actual statistics store writes this lane's scalar word at its exact shared offset. -/
theorem statisticsStoreFootprint {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g index : Nat} {a : Acc} {bs : List Byte} (site : Fin 4)
    (he : X.get (g, index) = some ⟨(statsStore site).pc, .wr a bs⟩) :
    ∃ warp : Fin 8, warp.val = warpIndex l g ∧ a = statsAcc l g warp site := by
  have hLo : 3420 ≤ (statsStore site).pc := by fin_cases site <;> decide
  have hHi : (statsStore site).pc < 7742 := by fin_cases site <;> decide
  obtain ⟨warp, hWarp, s, o, hPc, hFrame, hStep⟩ := softmaxRoleEventWith
    (Q := fun w v => w.val = warpIndex l g → AddressFrame l g w v)
    hp hX he hLo hHi (fun w _ h _ => initialAddressFrame w h)
    (fun w {_ _ _} hlo hhi hs hw hF step hW => regionStep hp hW hlo hhi hs hw (hF hW) step)
  have hF := hFrame hWarp
  have hBase :
      s.regs (statsStore site).base = some (b32 (statsBase l g warp)) := by
    fin_cases site
    · have hs : s.pc = StatisticsAddressWindow.biased.stop := hPc
      have hAt : inAddress .biased s.pc := by rw [hs]; decide
      exact (originResult hp hWarp hs (hF.origin .biased hAt)).1
    · have hs : s.pc = StatisticsAddressWindow.plain.stop := hPc
      have hAt : inAddress .plain s.pc := by rw [hs]; decide
      exact (originResult hp hWarp hs (hF.origin .plain hAt)).1
    · have hs : s.pc = StatisticsAddressWindow.final.stop := hPc
      have hAt : inAddress .final s.pc := by rw [hs]; decide
      exact (originResult hp hWarp hs (hF.origin .final hAt)).1
    · exact hF.maxWord hPc
  have hReturns : ∃ outState,
      EStep kernel Assumptions.all l g s ⟨(statsStore site).pc, .wr a bs⟩ (some outState) := by
    cases o with
    | none =>
      obtain ⟨_, _, hf⟩ := hStep
      rcases fires_none_ends hf with ⟨_, h⟩ | h <;> exact Kind.noConfusion h
    | some outState => exact ⟨outState, hStep⟩
  obtain ⟨outState, hStep⟩ := hReturns
  obtain ⟨i, hc, _, hf⟩ := estep_event_source hStep
  rw [hPc] at hc
  have hf' : Fires s.pc (eventTmpl Assumptions.all l g s i.op)
      ⟨s.pc, .wr a bs⟩ (some outState) := by
    have hLabel : (⟨s.pc, .wr a bs⟩ : Event) = ⟨(statsStore site).pc, .wr a bs⟩ :=
      congrArg (fun pc => Event.mk pc (.wr a bs)) hPc
    rw [hLabel]
    exact hf
  refine ⟨warp, hWarp, ?_⟩
  fin_cases site
  · change kernel.code[5682]? = some i at hc
    rw [Flow.code_5682] at hc
    obtain rfl := Option.some.inj hc
    exact storedWordFootprint hp warp (.inl rfl) hBase hf'
  · change kernel.code[6890]? = some i at hc
    rw [Flow.code_6890] at hc
    obtain rfl := Option.some.inj hc
    exact storedWordFootprint hp warp (.inl rfl) hBase hf'
  · change kernel.code[7614]? = some i at hc
    rw [Flow.code_7614] at hc
    obtain rfl := Option.some.inj hc
    exact storedWordFootprint hp warp (.inl rfl) hBase hf'
  · change kernel.code[7615]? = some i at hc
    rw [Flow.code_7615] at hc
    obtain rfl := Option.some.inj hc
    exact storedWordFootprint hp warp (.inr rfl) hBase hf'

end
end PTX.Kernels.TmlFa4Fwd.Thread.Scores
