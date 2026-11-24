-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxAlpha
public import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopFlow
import Kernels.TmlFa4Fwd.Flow.Code.Part068
import Kernels.TmlFa4Fwd.Flow.Code.Part078
import Kernels.TmlFa4Fwd.Flow.Code.Part088
import Kernels.TmlFa4Fwd.Flow.Code.Part103
import Kernels.TmlFa4Fwd.Flow.Code.Part104
import Kernels.TmlFa4Fwd.Flow.Code.Part107
import Kernels.TmlFa4Fwd.Flow.Code.Part118
import Lemmas.Execution.EventFrameSource
import Lemmas.Flow.FloatOutcome

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Scores
open PTX PTX.Flow PTX.Proof PTX.Assumption PTX.EventFrame Softmax

noncomputable section

/-- A physically represented maximum is a real FP32 value or the fully masked sentinel. -/
def CanonicalMaximum (s : TState) (reg : Nat) : Prop :=
  ∃ mx : Option ℝ, s.regs reg = some (scoreValue mx)

private def copyMaximum (reg : Nat) : Op :=
  .move ⟨.scalar,.int .b 32,[some reg],[.reg 7256]⟩

private theorem copyKeepsMaximum {l : Launch} {g reg : Nat} {s u : TState}
    (hoff : s.pc ∉ Assumptions.swExp2Sites)
    (hMax : CanonicalMaximum s 7256)
    (hExec : execLocalA Assumptions.all l g s (copyMaximum reg) = .ok u) :
    CanonicalMaximum u reg := by
  obtain ⟨mx,hMax⟩ := hMax
  change execLocalA Assumptions.all l g s
    (.move ⟨.scalar,.int .b 32,[some reg],[.reg 7256]⟩) = .ok u at hExec
  rw [Assumptions.execLocalA_all_eq_numeric,Assumptions.execLocalA_eq_nil hoff rfl] at hExec
  rw [exec_movE (by simp [CoreMoves]) (by simp [NoSegments]) hMax,
    movE,ite_eq_left (scoreValue_bytes mx)] at hExec
  obtain rfl := Except.ok.inj hExec
  exact ⟨mx,Function.update_self ..⟩

private inductive MaximumField where
  | current | biased | plain

private def maxRegister : MaximumField → Nat
  | .current => 7256
  | .biased => 7251
  | .plain => 7255

private def maxStart : MaximumField → Nat
  | .current => 4398
  | .biased => 5032
  | .plain => 6661

private def maxStop : MaximumField → Nat
  | .current => 7616
  | .biased => 6653
  | .plain => 7604

private def maxUpdates : MaximumField → List Nat
  | .current => []
  | .biased => [5031,6652]
  | .plain => [6660,7603]

private def maxScope (field : MaximumField) (site : Nat) : Prop :=
  maxStart field ≤ site ∧ site ≤ maxStop field ∧
    match field with
    | .current => (site < 5672 ∨ 5682 < site) ∧ (site < 6883 ∨ 6890 < site)
    | .biased | .plain => True

private instance (field : MaximumField) (site : Nat) : Decidable (maxScope field site) :=
  by cases field <;> unfold maxScope <;> infer_instance

/-- The current and carried references have canonical score representations whenever
their respective decoder paths have initialized the registers. -/
@[no_expose] def MaximumFrame (s : TState) : Prop :=
  ∀ field, maxScope field s.pc → CanonicalMaximum s (maxRegister field)

private def maxAudit (field : MaximumField) (site : Nat) (ins : Instr) : Bool :=
  (ins.op.isLocal || scoreEventOp ins.op) &&
    !(scoreEventWrites ins.op).contains 0 &&
    (if maxScope field site then
      (!(scoreEventWrites ins.op).contains (maxRegister field) &&
        !(writesRegs ins.op).contains (maxRegister field)) || (maxUpdates field).contains site
      else true) &&
    match ins.op with
    | .bra dst _ => decide (maxScope field dst → maxScope field site)
    | .brx .. => false
    | _ => true

private theorem maxAuditAt (field : MaximumField) {pc : Nat} {ins : Instr}
    (hLo : 3103 ≤ pc) (hHi : pc < 7742) (hc : kernel.code[pc]? = some ins) :
    maxAudit field pc ins = true := by
  let code := ((kernel.code.drop 3103).take (7742-3103)).zipIdx 3103
  have hAll : code.all (fun (ins,site) => maxAudit field site ins) = true := by
    cases field <;> set_option maxRecDepth 100000 in kernel_rfl
  apply List.all_eq_true.mp hAll (ins,pc)
  apply List.mem_of_getElem? (i := pc-3103)
  dsimp only [code]
  rw [List.getElem?_zipIdx,List.getElem?_take_of_lt (by omega),List.getElem?_drop,
    Nat.add_sub_of_le hLo,hc]
  rfl

private theorem maximumSegmentKeeps (field : MaximumField) {pc : Nat} {m : SegMatch CuteSlot}
    (hSite : pc ∈ Assumptions.swExp2Sites) (hMatch : cuteExp2.matchAt kernel pc = some m)
    (hDest : maxScope field m.stop) :
    maxScope field pc ∧ maxRegister field ∉ scoreSegmentWrites m := by
  have hAll : Assumptions.swExp2Sites.all (fun src =>
      (cuteExp2.matchAt kernel src).any (fun seg =>
        !decide (maxScope field seg.stop) ||
          (decide (maxScope field src) &&
            !(scoreSegmentWrites seg).contains (maxRegister field)))) = true := by
    cases field <;> set_option maxRecDepth 100000 in kernel_rfl
  have h := List.all_eq_true.mp hAll pc hSite
  simpa only [hMatch,Option.any_some,hDest,decide_true,Bool.not_true,Bool.false_or,
    Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',List.contains_eq_mem,
    decide_eq_false_iff_not] using h

private def maxEventEntries (field : MaximumField) : List Nat :=
  match field with
  | .current => [4397,5682,6890]
  | .biased | .plain => []

private theorem maxEntryEither (field : MaximumField) {site : Nat}
    (hd : maxScope field (site+1)) :
    maxScope field site ∨ site ∈ maxUpdates field ∨ site ∈ maxEventEntries field := by
  cases field <;>
    simp [maxScope,maxStart,maxStop,maxUpdates,maxEventEntries] at hd ⊢ <;> omega

private theorem maximumExecUpdate {l : Launch} {g : Nat} {s u : TState} {ins : Instr}
    (field : MaximumField) (hSite : s.pc ∈ maxUpdates field)
    (hc : kernel.code[s.pc]? = some ins)
    (hx : execLocalA Assumptions.all l g s ins.op = .ok u) (hFrame : MaximumFrame s) :
    CanonicalMaximum u (maxRegister field) := by
  have hOff : s.pc ∉ Assumptions.swExp2Sites := by
    have hAll : ∀ (f : MaximumField), (maxUpdates f).all
        (fun pc => !(Assumptions.swExp2Sites.contains pc)) = true := by
      intro f
      cases f <;> decide
    simpa using List.all_eq_true.mp (hAll field) _ hSite
  have copy {pc reg : Nat} (he : s.pc = pc) (hCode : kernel.code[pc]? =
      some ⟨none,copyMaximum reg⟩) (hScope : maxScope .current pc) :
      CanonicalMaximum u reg := by
    rw [he,hCode] at hc
    obtain rfl := Option.some.inj hc
    exact copyKeepsMaximum hOff (hFrame .current (he.symm ▸ hScope)) hx
  cases field with
  | current => cases hSite
  | biased =>
    simp only [maxUpdates,List.mem_cons,List.not_mem_nil,or_false] at hSite
    rcases hSite with hs | hs
    · exact copy hs Flow.code_5031 (by decide)
    · exact copy hs Flow.code_6652 (by decide)
  | plain =>
    simp only [maxUpdates,List.mem_cons,List.not_mem_nil,or_false] at hSite
    rcases hSite with hs | hs
    · exact copy hs Flow.code_6660 (by decide)
    · exact copy hs Flow.code_7603 (by decide)

private theorem maxUpdateLocal (field : MaximumField) {pc : Nat} {ins : Instr}
    (h : pc ∈ maxUpdates field) (hc : kernel.code[pc]? = some ins) :
    ins.op.isLocal = true := by
  have localAt {j : Nat} {i : Instr} (hPc : pc = j) (hCode : kernel.code[j]? = some i)
      (hLocal : i.op.isLocal = true) : ins.op.isLocal = true := by
    rw [hPc,hCode] at hc
    obtain rfl := Option.some.inj hc
    exact hLocal
  cases field with
  | current => cases h
  | biased =>
    simp only [maxUpdates,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with h | h
    · exact localAt h Flow.code_5031 rfl
    · exact localAt h Flow.code_6652 rfl
  | plain =>
    simp only [maxUpdates,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with h | h
    · exact localAt h Flow.code_6660 rfl
    · exact localAt h Flow.code_7603 rfl

theorem initialMaximumFrame {s : TState} (hs : s.pc = 3103) : MaximumFrame s := by
  intro field h
  rw [hs] at h
  cases field <;> exact ((by decide : ¬ maxScope _ 3103) h).elim

private theorem maxEntryUnguarded (field : MaximumField) {pc : Nat} {i : Instr}
    (hc : kernel.code[pc]? = some i)
    (h : pc ∈ maxUpdates field ∨ pc ∈ maxEventEntries field) : i.guard = none := by
  have atSite {j : Nat} {ins : Instr} (hPc : pc = j)
      (hj : kernel.code[j]? = some ins) (hGuard : ins.guard = none) : i.guard = none := by
    rw [hPc,hj] at hc
    cases hc
    exact hGuard
  cases field with
  | current =>
    simp [maxEventEntries,maxUpdates] at h
    rcases h with h | h | h
    · exact atSite h Flow.code_4397 rfl
    · exact atSite h Flow.code_5682 rfl
    · exact atSite h Flow.code_6890 rfl
  | biased =>
    simp [maxEventEntries,maxUpdates] at h
    rcases h with h | h
    · exact atSite h Flow.code_5031 rfl
    · exact atSite h Flow.code_6652 rfl
  | plain =>
    simp [maxEventEntries,maxUpdates] at h
    rcases h with h | h
    · exact atSite h Flow.code_6660 rfl
    · exact atSite h Flow.code_7603 rfl

private theorem maxPublicationNonlocal (field : MaximumField) {pc : Nat} {i : Instr}
    (hc : kernel.code[pc]? = some i) (h : pc ∈ maxEventEntries field) :
    i.op.isLocal = false := by
  cases field with
  | biased | plain => cases h
  | current =>
    simp only [maxEventEntries,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with h | h | h
    · rw [h,Flow.code_4397] at hc
      cases hc
      rfl
    · rw [h,Flow.code_5682] at hc
      cases hc
      rfl
    · rw [h,Flow.code_6890] at hc
      cases hc
      rfl

private theorem maxPublicationKeeps {pc : Nat} {i : Instr}
    (hc : kernel.code[pc]? = some i) (h : pc = 4397 ∨ pc = 5682 ∨ pc = 6890) :
    7256 ∉ scoreEventWrites i.op := by
  rcases h with rfl | rfl | rfl
  · rw [Flow.code_4397] at hc
    cases hc
    decide
  · rw [Flow.code_5682] at hc
    cases hc
    decide
  · rw [Flow.code_6890] at hc
    cases hc
    decide

/-- The maximum is tracked between publications, while the carried old maximum remains
available during computation of its replacement. -/
theorem maximumFrameStep {l : Launch} {g : Nat} {s u : TState}
    {ev : Option Event} (hLo : 3103 ≤ s.pc) (hHi : s.pc < 7742) (hSub : s.sub ≤ 3)
    (hFrame : MaximumFrame s) (hStep : WStep kernel Assumptions.all l g s ev u)
    (hPublication : ∀ e, ev = some e →
      s.pc = 4397 ∨ s.pc = 5682 ∨ s.pc = 6890 → CanonicalMaximum s 7256) : MaximumFrame u := by
  intro field hDest
  have hEnter (hPc : u.pc = s.pc+1) := maxEntryEither field (hPc ▸ hDest)
  have keeps {i : Instr} (hc : kernel.code[s.pc]? = some i) (hS : maxScope field s.pc) :
      (maxRegister field ∉ scoreEventWrites i.op ∧
        maxRegister field ∉ writesRegs i.op) ∨ s.pc ∈ maxUpdates field := by
    have h := maxAuditAt field hLo hHi hc
    simp only [maxAudit,Bool.and_eq_true,ite_eq_left hS,Bool.or_eq_true,Bool.not_eq_true',
      List.contains_eq_mem,decide_eq_false_iff_not,decide_eq_true_eq] at h
    exact h.1.2
  rcases hStep with ⟨rfl,ht⟩ | ⟨e,rfl,he⟩
  · obtain ⟨i,hCode,_,hLocal⟩ := tauScoreSource ht
    rcases hLocal with ⟨rfl,hGuard⟩ | ⟨_,hIsLocal,hExec⟩
    · rcases hEnter rfl with hS | hPc
      · exact hFrame field hS
      · rw [maxEntryUnguarded field hCode hPc] at hGuard
        cases hGuard
    rcases scoreExecLocal hExec with hLocal | ⟨m,hSite,hMatch,hSem⟩
    · have hSrc : maxScope field s.pc ∨ s.pc ∈ maxUpdates field ∨
          s.pc ∈ maxEventEntries field := by
        have hPc := hLocal.pc
        have hAudit := maxAuditAt field hLo hHi hCode
        cases hOp : i.op <;> simp only [hOp,nextPc,BrxTarget,or_false] at hPc
        case bra dst uni =>
          simp only [maxAudit,hOp,Bool.and_eq_true,decide_eq_true_eq] at hAudit
          exact .inl (hAudit.2 (hPc ▸ hDest))
        case brx => simp [maxAudit,hOp] at hAudit
        all_goals exact hEnter hPc
      rcases hSrc with hS | hChanged | hPub
      · rcases keeps hCode hS with ⟨_,hFree⟩ | hChange
        · obtain ⟨mx,hMx⟩ := hFrame field hS
          exact ⟨mx,(hLocal.regs _ hFree).trans hMx⟩
        · exact maximumExecUpdate field hChange hCode hExec hFrame
      · exact maximumExecUpdate field hChanged hCode hExec hFrame
      · have hFalse := maxPublicationNonlocal field hCode hPub
        exact (Bool.false_ne_true (hFalse.symm.trans hIsLocal)).elim
    · obtain ⟨hPc,_,_,hKeep⟩ := scoreSegmentFrame hSem
      obtain ⟨hS,hFree⟩ := maximumSegmentKeeps field hSite hMatch (hPc ▸ hDest)
      obtain ⟨mx,hMx⟩ := hFrame field hS
      exact ⟨mx,(hKeep _ hFree).trans hMx⟩
  · obtain ⟨i,hCode,hNonlocal,_⟩ := estep_event_source he
    have hAudit := maxAuditAt field hLo hHi hCode
    simp only [maxAudit,Bool.and_eq_true,hNonlocal,Bool.false_or,Bool.not_eq_true',
      List.contains_eq_mem,decide_eq_false_iff_not] at hAudit
    have hProg := (scoreEventStep hCode hAudit.1.1.1 hSub hAudit.1.1.2 he).1
    have hSrc : maxScope field s.pc ∨ s.pc ∈ maxUpdates field ∨
        s.pc ∈ maxEventEntries field := by
      rcases hProg.pc with ⟨hPc,_⟩ | ⟨hPc,_⟩
      · exact hEnter hPc
      · exact .inl (hPc ▸ hDest)
    rcases hSrc with hS | hLocal | hPub
    · obtain ⟨mx,hMx⟩ := hFrame field hS
      have hKeep := (keeps hCode hS).resolve_right
        (fun h => Bool.false_ne_true (hNonlocal.symm.trans (maxUpdateLocal field h hCode)))
      exact ⟨mx,(scoreEventStep hCode hAudit.1.1.1 hSub hKeep.1 he).2.trans hMx⟩
    · exact (Bool.false_ne_true (hNonlocal.symm.trans (maxUpdateLocal field hLocal hCode))).elim
    · cases field with
      | biased | plain => cases hPub
      | current =>
        have hSites : s.pc = 4397 ∨ s.pc = 5682 ∨ s.pc = 6890 := by
          simpa [maxEventEntries] using hPub
        obtain ⟨mx,hMx⟩ := hPublication e rfl hSites
        exact ⟨mx,(scoreEventStep hCode hAudit.1.1.1 hSub
          (maxPublicationKeeps hCode hSites) he).2.trans hMx⟩

theorem priorMaximumAtPlainLoad {s : TState} (hFrame : MaximumFrame s)
    (hPc : s.pc = 6679) : CanonicalMaximum s 7255 :=
  hFrame .plain (hPc.symm ▸ (by decide : maxScope .plain 6679))

theorem priorMaximumAtBiasWait {s : TState} (hFrame : MaximumFrame s)
    (hPc : s.pc = 5181) : CanonicalMaximum s 7251 :=
  hFrame .biased (hPc.symm ▸ (by decide : maxScope .biased 5181))

end
end PTX.Kernels.TmlFa4Fwd.Thread.Scores
