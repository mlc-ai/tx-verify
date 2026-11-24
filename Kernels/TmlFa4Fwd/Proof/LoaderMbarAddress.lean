-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MbarAddressClosure
public import Kernels.TmlFa4Fwd.Proof.LoaderInputSites
import Kernels.TmlFa4Fwd.Proof.EpilogueWarpReady
import Kernels.TmlFa4Fwd.Proof.OutputAssignedBox
import Kernels.TmlFa4Fwd.Proof.EpiloguePrefixStartup
import Kernels.TmlFa4Fwd.Proof.EpilogueCuts
import Kernels.TmlFa4Fwd.Proof.OutputFrame
import Kernels.TmlFa4Fwd.Proof.MmaLoopEntryBound
import Lemmas.Flow.NotClc
import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopEvents
import Kernels.TmlFa4Fwd.Proof.RoleDispatch
import Kernels.TmlFa4Fwd.Proof.PrologueDispatchTrace
import Kernels.TmlFa4Fwd.Proof.PrologueWarp0Prefix
import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopFlow
import Kernels.TmlFa4Fwd.Proof.LoaderCountExit
import Kernels.TmlFa4Fwd.Proof.Thread.DecodedEventFrame
import Kernels.TmlFa4Fwd.Proof.RegisterHintBody
import Lemmas.Flow.TensorIssue
import Lemmas.Protocol.CpAsync
import Lemmas.Step.CtaBar
import Kernels.TmlFa4Fwd.Flow.Code.Part008
import Kernels.TmlFa4Fwd.Flow.Code.Part010
import Kernels.TmlFa4Fwd.Flow.Code.Part011
import Kernels.TmlFa4Fwd.Flow.Code.Part012
import Kernels.TmlFa4Fwd.Flow.Code.Part014
import Kernels.TmlFa4Fwd.Flow.Code.Part017
import Kernels.TmlFa4Fwd.Flow.Code.Part018
import Kernels.TmlFa4Fwd.Flow.Code.Part021
import Kernels.TmlFa4Fwd.Flow.Code.Part029

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof PTX.EventFrame
open Prologue Mma Epilogue Softmax

noncomputable section

private structure FixedLoaderAdd where
  defPc : Nat
  lastPc : Nat
  reg : Nat
  off : Nat
  deriving DecidableEq

private def fixedLoaderAdds : List FixedLoaderAdd :=
  [⟨515, 519, 1848, 56⟩, ⟨677, 681, 1889, 16⟩, ⟨701, 727, 1114, 320⟩,
   ⟨702, 706, 1897, 336⟩, ⟨728, 732, 1907, 24⟩, ⟨754, 758, 1917, 344⟩,
   ⟨780, 784, 1925, 64⟩, ⟨1144, 1173, 1140, 320⟩, ⟨1145, 1148, 2039, 336⟩,
   ⟨1174, 1177, 2052, 344⟩, ⟨1359, 1383, 1142, 320⟩, ⟨1360, 1363, 2121, 336⟩,
   ⟨1892, 1895, 2305, 24⟩]

private def FixedLoaderAdd.active (f : FixedLoaderAdd) (pc : Nat) : Prop :=
  f.defPc < pc ∧ pc ≤ f.lastPc

private instance (f : FixedLoaderAdd) (pc : Nat) : Decidable (f.active pc) :=
  inferInstanceAs (Decidable (f.defPc < pc ∧ pc ≤ f.lastPc))

private def loaderFixedRoots (l : Launch) (warp : Fin 2) : List (Nat × Value) :=
  [(2535, b32 l.sharedBase), (1062, b32 (14 + warp.val))]

private def loaderFixedFrame (l : Launch) (warp : Fin 2) (s : TState) : Prop :=
  RingShape s ∧ Holds s.regs (loaderFixedRoots l warp) ∧
    ∀ f ∈ fixedLoaderAdds, f.active s.pc → s.regs f.reg = some (b32 (l.sharedBase + f.off))

private def fixedLoaderCode (pc : Nat) (i : Instr) : Bool :=
  fixedLoaderAdds.all (fun f => !decide (f.active pc) || !(loaderRingWrites i.op).contains f.reg) &&
  match i.op with
  | .bra target _ =>
    fixedLoaderAdds.all (fun f => !decide (f.active target) || decide (f.active pc))
  | .brx .. => false
  | _ => true

private theorem fixedLoaderCodeAt {pc : Nat} {i : Instr}
    (hLo : 174 ≤ pc) (hHi : pc < 1901) (hc : kernel.code[pc]? = some i) :
    fixedLoaderCode pc i = true := by
  let code := ((kernel.code.drop 174).take (1901 - 174)).zipIdx 174
  have hAll : code.all (fun (ins, site) => fixedLoaderCode site ins) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  apply List.all_eq_true.mp hAll (i, pc)
  apply List.mem_of_getElem? (i := pc - 174)
  dsimp only [code]
  rw [List.getElem?_zipIdx, List.getElem?_take_of_lt (by omega), List.getElem?_drop,
    Nat.add_sub_of_le hLo, hc]
  rfl

private theorem fixedLoaderDef {f : FixedLoaderAdd} (hf : f ∈ fixedLoaderAdds) :
    kernel.code[f.defPc]? = some ⟨none,
      .int ⟨.add, .int .s 32, false, [some f.reg], [.reg 2535, .imm f.off]⟩⟩ := by
  simp only [fixedLoaderAdds, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  · exact Flow.code_515
  · exact Flow.code_677
  · exact Flow.code_701
  · exact Flow.code_702
  · exact Flow.code_728
  · exact Flow.code_754
  · exact Flow.code_780
  · exact Flow.code_1144
  · exact Flow.code_1145
  · exact Flow.code_1174
  · exact Flow.code_1359
  · exact Flow.code_1360
  · exact Flow.code_1892

private theorem fixedLoaderAdd {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} {s u : TState} {f : FixedLoaderAdd} (hF : f ∈ fixedLoaderAdds) (hPc : s.pc = f.defPc)
    (hf : s.fault = none) (hBase : s.regs 2535 = some (b32 l.sharedBase))
    (ht : Tau kernel [] l g s u) : u.regs f.reg = some (b32 (l.sharedBase + f.off)) := by
  have hChecked : fixedLoaderAdds.all (fun f => f.off ≤ 344) = true := by decide
  have hMax := of_decide_eq_true (List.all_eq_true.mp hChecked f hF)
  have hBound : l.sharedBase + f.off < 2 ^ 32 := by have := hp.shared.2.1; omega
  have hu := Option.some.inj ((tauStep_iff.mpr ht).symm.trans
    (evalSharedAdd hPc hf hBase hBound (fixedLoaderDef hF)))
  subst u
  exact Function.update_self _ _ _

private theorem fixedLoaderAddrStep {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} {warp : Fin 2} {s u : TState} {e : Option Event}
    (hLo : 174 ≤ s.pc) (hHi : s.pc < 1901)
    (hFrame : loaderFixedFrame l warp s) (hw : WStep kernel Assumptions.all l g s e u) :
    174 ≤ u.pc ∧ u.pc ≤ 1901 ∧ loaderFixedFrame l warp u := by
  have hCode (bound : Nat) : ((kernel.code.drop 174).take (1901 - 174)).all
      (fun i => loaderPipelineCutOp 174 1901 bound ((loaderFixedRoots l warp).map Prod.fst)
        i.op) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  obtain ⟨hl, hh, hShape, hRoots⟩ := pipelineCutStep
    (by decide : 174 ≤ 174) (by decide : 1901 ≤ 1901) ⟨hLo, hHi⟩
    (hCode u.pc) hw hFrame.1 hFrame.2.1
  refine ⟨hl, hh.resolve_right (Nat.lt_irrefl _), hShape, hRoots, ?_⟩
  intro f hF hActive
  have hFall (hp : u.pc = s.pc + 1) : s.pc = f.defPc ∨ f.active s.pc := by
    unfold FixedLoaderAdd.active at hActive ⊢
    omega
  have hPrior (hBefore : f.active s.pc) : u.regs f.reg = some (b32 (l.sharedBase + f.off)) := by
    refine (loaderPipelineStepRegs hLo hHi (fun i hc => ?_) hw).trans (hFrame.2.2 f hF hBefore)
    have h := fixedLoaderCodeAt hLo hHi hc
    simp only [fixedLoaderCode, Bool.and_eq_true] at h
    simpa [hBefore] using List.all_eq_true.mp h.1 f hF
  rcases hw with ⟨_, ht⟩ | ⟨ev, _, he⟩
  · have ht' : Tau kernel [] l g s u := by
      unfold Tau at ht ⊢
      rwa [← loaderOutCore (by omega) (by omega)]
    obtain ⟨i, hc, hf, _⟩ := tauScoreSource ht
    by_cases hEq : s.pc = f.defPc
    · exact fixedLoaderAdd hp hF hEq hf hFrame.2.1.1 ht'
    apply hPrior
    rcases tau_core_frame hc ht' with rfl | hLocal
    · exact (hFall rfl).resolve_left hEq
    · have h := hLocal.pc
      have hCode := fixedLoaderCodeAt hLo hHi hc
      simp only [fixedLoaderCode, Bool.and_eq_true] at hCode
      cases ho : i.op <;> simp only [ho, nextPc, BrxTarget, or_false] at h
      case bra target uni =>
        have hAll := hCode.2
        rw [ho] at hAll
        rw [h] at hActive
        simpa [hActive] using List.all_eq_true.mp hAll f hF
      case brx => simp [ho] at hCode
      all_goals exact (hFall h).resolve_left hEq
  · have hNe : s.pc ≠ f.defPc := by
      intro hp
      obtain ⟨i, hc, hl, _⟩ := estep_event_source he
      rw [hp, fixedLoaderDef hF] at hc
      obtain rfl := Option.some.inj hc.symm
      cases hl
    apply hPrior
    have hE : EStep kernel [] l g s ev (some u) := by
      obtain ⟨tm, hOut, hFires⟩ := he
      exact ⟨tm, by rwa [← loaderOutCore (by omega) (by omega)], hFires⟩
    rcases (estep_return_pc hE (fun _ _ _ h => execLocal_frame h)).2 with h | h
    · exact h ▸ hActive
    · exact (hFall h).resolve_left hNe

private theorem fixedLoaderWalk {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} {warp : Fin 2} {s : TState} {events : List Event} {visits : List Visit}
    (hWalk : Walk kernel Assumptions.all l g s events visits) (hLo : 174 ≤ s.pc) (hHi : s.pc ≤ 1901)
    (hFrame : loaderFixedFrame l warp s) {e : Event} (he : e ∈ events) (hEnd : e.pc < 1901) :
    ∃ t o, t.pc = e.pc ∧ loaderFixedFrame l warp t ∧ EStep kernel Assumptions.all l g t e o := by
  induction hWalk with
  | stop => cases he
  | @tau s u events visits ht hw ih =>
    by_cases hExit : s.pc = 1901
    · obtain ⟨_, _, hf, _⟩ := tauScoreSource ht
      have hAt := pipelineAtCut hExit hFrame.1 hFrame.2.1 hf
        ⟨_, Flow.code_1901, rfl⟩
      have hRet := loaderTailEventPcs warp hAt (.tau ht hw) e he
      omega
    obtain ⟨hl, hh, hF'⟩ := fixedLoaderAddrStep hp hLo (by omega) hFrame (.inl ⟨rfl, ht⟩)
    exact ih hl hh hF' he
  | @ev s u ev events visits hs hw ih =>
    rcases List.mem_cons.mp he with rfl | he
    · exact ⟨_, _, (estep_source_pc hs).symm, hFrame, hs⟩
    · by_cases hExit : s.pc = 1901
      · have hf : s.fault = none := by
          obtain ⟨tm, hout, hFire⟩ := hs
          cases h : s.fault
          · rfl
          · simp only [out, h, Out.ev.injEq] at hout
            subst tm
            cases hFire.2
        have hAt := pipelineAtCut hExit hFrame.1 hFrame.2.1 hf ⟨_, Flow.code_1901, rfl⟩
        have hRet := loaderTailEventPcs warp hAt (.ev hs hw) e (List.mem_cons_of_mem _ he)
        omega
      obtain ⟨hl, hh, hF'⟩ := fixedLoaderAddrStep hp hLo (by omega) hFrame (.inr ⟨_, rfl, hs⟩)
      exact ih hl hh hF' he
  | last hs =>
    obtain rfl := List.mem_singleton.mp he
    exact ⟨_, _, (estep_source_pc hs).symm, hFrame, hs⟩

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

private theorem loaderFixedSource {g index : Nat} {e : Event} (he : X.get (g, index) = some e)
    (hLo : 517 ≤ e.pc) (hHi : e.pc < 1901) :
    ∃ warp : Fin 2, ∃ t o, t.pc = e.pc ∧ loaderFixedFrame l warp t ∧
      EStep kernel Assumptions.all l g t e o := by
  have hHint : e.pc ∉ registerHintSites := by
    simp only [registerHintSites, List.mem_cons, List.not_mem_nil, or_false]
    omega
  have hWarp : 14 ≤ warpIndex l g := by
    rcases roleBodyPcOfEvent hp hX he (by omega) hHint with h | h
    · omega
    · split_ifs at h <;> omega
  let warp : Fin 2 := ⟨warpIndex l g - 14, by have := warpIndex_lt hp g; omega⟩
  have hWord : 14 + warp.val = warpIndex l g := Nat.add_sub_of_le hWarp
  have hg := Step.CtaBar.thread_lt_of_get hX he
  obtain ⟨pos, t, o, hIndex, ht, hr⟩ := commonDispatchOfLateEvent hp hX hg he (by omega)
  have hAt : At t 174 (loaderFixedRoots l warp) :=
    ht.mono ⟨ht.2.2.2.2.2.1, hWord.symm ▸ ht.2.2.2.2.1, trivial⟩
  have hF : loaderFixedFrame l warp t := by
    refine ⟨ringShapeOfAt hAt, hAt.2.2.2.2, ?_⟩
    intro f hf ha
    have hDec : fixedLoaderAdds.all (fun f => !decide (f.active 174)) = true := by decide
    have hFalse : ¬ f.active 174 := by simpa using List.all_eq_true.mp hDec f hf
    exact (hFalse (hAt.1 ▸ ha)).elim
  obtain ⟨_, hWalk⟩ := walkFromRun hr
  have hm : e ∈ (X.tr g).drop pos := by
    apply List.mem_of_getElem? (i := index - pos)
    rw [List.getElem?_drop, Nat.add_sub_of_le hIndex]
    exact he
  obtain ⟨t, o, ht, hf, hStep⟩ := fixedLoaderWalk hp hWalk
    (by rw [hAt.1]) (by rw [hAt.1]; decide) hF hm hHi
  exact ⟨warp, t, o, ht, hf, hStep⟩

omit hp hX in
/-- A decoded nonincrementing copy arrival has the verified CTA address. -/
theorem loaderAsyncArrivalResolvedAddress
    {p : Params} {l : Launch} {m : Mem0} {A : List Assumption} (hp : Pre p l m)
    {g pc base delta off : Nat} {t : TState}
    {e : Event} {o : Option TState} {target : Loc}
    (hBase : t.regs base = some (b32 (l.sharedBase + delta)))
    (hOff : initializedMbarOffset (delta + off))
    (hf : Fires pc (eventTmpl A l g t (.cpAsyncArrive true base off false)) e o)
    (hk : e.kind = .asyncArrive target true) :
    target = ⟨.shared, g / l.block, l.sharedBase + (delta + off)⟩ := by
  have hLoc := decodedMbarOffset (g := g) hp hBase hOff
  change Fires pc (cpAsyncTmpl l g t (.cpAsyncArrive true base off false)) e o at hf
  rw [cpAsyncTmpl_arrive_noinc hLoc] at hf
  rw [hf.1] at hk
  exact (Kind.asyncArrive.inj hk).1.symm

/-- The first two loader waits acquire the initial K and Q credits. -/
theorem initialLoaderWaitAddress {g index site parity : Nat} {target : Loc} {ok acq : Bool}
    {scope : MbarScope} (he : X.get (g, index) = some ⟨site, .wait target parity ok acq scope⟩)
    (hSite : site = 517 ∨ site = 679) :
    ∃ off, (off = 16 ∨ off = 56) ∧
      target = ⟨.shared, g / l.block, l.sharedBase + off⟩ := by
  have hLo : 517 ≤ site := by omega
  have hHi : site < 1901 := by omega
  obtain ⟨_, t, o, ht, hFrame, tm, hOut, hFire⟩ := loaderFixedSource hp hX he hLo hHi
  change t.pc = site at ht
  rcases out_ev hOut with ⟨_, rfl⟩ | ⟨ins, hc, rfl⟩
  · cases hFire.1
  rcases hSite with rfl | rfl
  · rw [ht, Flow.code_517] at hc
    obtain rfl := Option.some.inj hc.symm
    have hb := hFrame.2.2 ⟨515, 519, 1848, 56⟩
      (by decide) (ht.symm ▸ (show FixedLoaderAdd.active _ 517 by decide))
    exact ⟨56, .inr rfl,
      pollResolvedMbarAddress hp hb (by unfold initializedMbarOffset; decide) hFire rfl⟩
  · rw [ht, Flow.code_679] at hc
    obtain rfl := Option.some.inj hc.symm
    have hb := hFrame.2.2 ⟨677, 681, 1889, 16⟩
      (by decide) (ht.symm ▸ (show FixedLoaderAdd.active _ 679 by decide))
    exact ⟨16, .inl rfl,
      pollResolvedMbarAddress hp hb (by unfold initializedMbarOffset; decide) hFire rfl⟩

omit hp hX in
/-- Shared offsets of the fixed loader polls. -/
def fixedLoaderWaitOffset : Nat → Nat
  | 517 => 56
  | 679 => 16
  | 704 => 336
  | 730 => 24
  | 756 => 344
  | 782 => 64
  | 1146 => 336
  | 1175 => 344
  | 1361 => 336
  | _ => 24

/-- A fixed loader poll names its verified shared barrier. -/
theorem loaderFixedWaitOffset {g index pc : Nat} {target : Loc} {q : Nat} {ok acq : Bool}
    {scope : MbarScope} (he : X.get (g, index) = some ⟨pc, .wait target q ok acq scope⟩)
    (hSite : pc ∈ [517, 679, 704, 730, 756, 782, 1146, 1175, 1361, 1893]) :
    target = ⟨.shared, g / l.block, l.sharedBase + fixedLoaderWaitOffset pc⟩ := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hSite
  have hLo : 517 ≤ pc := by omega
  have hHi : pc < 1901 := by omega
  obtain ⟨_, t, o, ht, hFrame, hStep⟩ := loaderFixedSource hp hX he hLo hHi
  change t.pc = pc at ht
  obtain ⟨tm, hOut, hFire⟩ := hStep
  rcases out_ev hOut with ⟨f, rfl⟩ | ⟨ins, hc, rfl⟩
  · cases hFire.1
  rcases hSite with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [ht, Flow.code_517] at hc
    obtain rfl := Option.some.inj hc.symm
    have hb := hFrame.2.2 ⟨515, 519, 1848, 56⟩
      (by decide) (ht.symm ▸ (show FixedLoaderAdd.active _ 517 by decide))
    exact pollResolvedMbarAddress hp hb (by unfold initializedMbarOffset; decide) hFire rfl
  · rw [ht, Flow.code_679] at hc
    obtain rfl := Option.some.inj hc.symm
    have hb := hFrame.2.2 ⟨677, 681, 1889, 16⟩
      (by decide) (ht.symm ▸ (show FixedLoaderAdd.active _ 679 by decide))
    exact pollResolvedMbarAddress hp hb (by unfold initializedMbarOffset; decide) hFire rfl
  · rw [ht, Flow.code_704] at hc
    obtain rfl := Option.some.inj hc.symm
    have hb := hFrame.2.2 ⟨702, 706, 1897, 336⟩
      (by decide) (ht.symm ▸ (show FixedLoaderAdd.active _ 704 by decide))
    exact pollResolvedMbarAddress hp hb (by unfold initializedMbarOffset; decide) hFire rfl
  · rw [ht, Flow.code_730] at hc
    obtain rfl := Option.some.inj hc.symm
    have hb := hFrame.2.2 ⟨728, 732, 1907, 24⟩
      (by decide) (ht.symm ▸ (show FixedLoaderAdd.active _ 730 by decide))
    exact pollResolvedMbarAddress hp hb (by unfold initializedMbarOffset; decide) hFire rfl
  · rw [ht, Flow.code_756] at hc
    obtain rfl := Option.some.inj hc.symm
    have hb := hFrame.2.2 ⟨754, 758, 1917, 344⟩
      (by decide) (ht.symm ▸ (show FixedLoaderAdd.active _ 756 by decide))
    exact pollResolvedMbarAddress hp hb (by unfold initializedMbarOffset; decide) hFire rfl
  · rw [ht, Flow.code_782] at hc
    obtain rfl := Option.some.inj hc.symm
    have hb := hFrame.2.2 ⟨780, 784, 1925, 64⟩
      (by decide) (ht.symm ▸ (show FixedLoaderAdd.active _ 782 by decide))
    exact pollResolvedMbarAddress hp hb (by unfold initializedMbarOffset; decide) hFire rfl
  · rw [ht, Flow.code_1146] at hc
    obtain rfl := Option.some.inj hc.symm
    have hb := hFrame.2.2 ⟨1145, 1148, 2039, 336⟩
      (by decide) (ht.symm ▸ (show FixedLoaderAdd.active _ 1146 by decide))
    exact pollResolvedMbarAddress hp hb (by unfold initializedMbarOffset; decide) hFire rfl
  · rw [ht, Flow.code_1175] at hc
    obtain rfl := Option.some.inj hc.symm
    have hb := hFrame.2.2 ⟨1174, 1177, 2052, 344⟩
      (by decide) (ht.symm ▸ (show FixedLoaderAdd.active _ 1175 by decide))
    exact pollResolvedMbarAddress hp hb (by unfold initializedMbarOffset; decide) hFire rfl
  · rw [ht, Flow.code_1361] at hc
    obtain rfl := Option.some.inj hc.symm
    have hb := hFrame.2.2 ⟨1360, 1363, 2121, 336⟩
      (by decide) (ht.symm ▸ (show FixedLoaderAdd.active _ 1361 by decide))
    exact pollResolvedMbarAddress hp hb (by unfold initializedMbarOffset; decide) hFire rfl
  · rw [ht, Flow.code_1893] at hc
    obtain rfl := Option.some.inj hc.symm
    have hb := hFrame.2.2 ⟨1892, 1895, 2305, 24⟩
      (by decide) (ht.symm ▸ (show FixedLoaderAdd.active _ 1893 by decide))
    exact pollResolvedMbarAddress hp hb (by unfold initializedMbarOffset; decide) hFire rfl

/-- A fixed loader poll names its verified shared barrier. -/
theorem loaderFixedWaitAddress {g index pc : Nat} {target : Loc} {q : Nat} {ok acq : Bool}
    {scope : MbarScope} (he : X.get (g, index) = some ⟨pc, .wait target q ok acq scope⟩)
    (hSite : pc ∈ [517, 679, 704, 730, 756, 782, 1146, 1175, 1361, 1893]) :
    ∃ off ∈ [16, 24, 56, 64, 336, 344], target = ⟨.shared, g / l.block, l.sharedBase + off⟩ := by
  refine ⟨fixedLoaderWaitOffset pc, ?_, loaderFixedWaitOffset hp hX he hSite⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hSite
  rcases hSite with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

omit hp hX in
/-- The offset of a loader's fixed expect-transaction instruction. -/
def loaderExpectTxOffset : Nat → Nat
  | 686 => 0
  | 737 | 1900 => 8
  | 711 | 1153 | 1368 => 320
  | _ => 328

/-- Every fixed arrival uses the offset of its decoded expect-transaction instruction. -/
theorem loaderFixedArriveOffset {g index pc : Nat} {target : Loc} {tx n : Nat} {rel : Bool}
    {scope : MbarScope} (he : X.get (g, index) = some ⟨pc, .arrive target tx n rel scope⟩)
    (hSite : pc ∈ [686, 711, 737, 763, 1153, 1182, 1368, 1900]) :
    target = ⟨.shared, g / l.block, l.sharedBase + loaderExpectTxOffset pc⟩ := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hSite
  have hLo : 517 ≤ pc := by omega
  have hHi : pc < 1901 := by omega
  obtain ⟨_, t, o, ht, hFrame, hStep⟩ := loaderFixedSource hp hX he hLo hHi
  change t.pc = pc at ht
  obtain ⟨tm, hOut, hFire⟩ := hStep
  rcases out_ev hOut with ⟨f, rfl⟩ | ⟨ins, hc, rfl⟩
  · cases hFire.1
  rcases hSite with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [ht, Flow.code_686] at hc
    obtain rfl := Option.some.inj hc.symm
    have hb : t.regs 2535 = some (b32 (l.sharedBase + 0)) := hFrame.2.1.1
    exact arriveResolvedMbarAddress hp hb (by unfold initializedMbarOffset; decide) hFire rfl
  · rw [ht, Flow.code_711] at hc
    obtain rfl := Option.some.inj hc.symm
    have hb := hFrame.2.2 ⟨701, 727, 1114, 320⟩
      (by decide) (ht.symm ▸ (show FixedLoaderAdd.active _ 711 by decide))
    exact arriveResolvedMbarAddress hp hb (by unfold initializedMbarOffset; decide) hFire rfl
  · rw [ht, Flow.code_737] at hc
    obtain rfl := Option.some.inj hc.symm
    have hb : t.regs 2535 = some (b32 (l.sharedBase + 0)) := hFrame.2.1.1
    exact arriveResolvedMbarAddress hp hb (by unfold initializedMbarOffset; decide) hFire rfl
  · rw [ht, Flow.code_763] at hc
    obtain rfl := Option.some.inj hc.symm
    have hb : t.regs 2535 = some (b32 (l.sharedBase + 0)) := hFrame.2.1.1
    exact arriveResolvedMbarAddress hp hb (by unfold initializedMbarOffset; decide) hFire rfl
  · rw [ht, Flow.code_1153] at hc
    obtain rfl := Option.some.inj hc.symm
    have hb := hFrame.2.2 ⟨1144, 1173, 1140, 320⟩
      (by decide) (ht.symm ▸ (show FixedLoaderAdd.active _ 1153 by decide))
    exact arriveResolvedMbarAddress hp hb (by unfold initializedMbarOffset; decide) hFire rfl
  · rw [ht, Flow.code_1182] at hc
    obtain rfl := Option.some.inj hc.symm
    have hb : t.regs 2535 = some (b32 (l.sharedBase + 0)) := hFrame.2.1.1
    exact arriveResolvedMbarAddress hp hb (by unfold initializedMbarOffset; decide) hFire rfl
  · rw [ht, Flow.code_1368] at hc
    obtain rfl := Option.some.inj hc.symm
    have hb := hFrame.2.2 ⟨1359, 1383, 1142, 320⟩
      (by decide) (ht.symm ▸ (show FixedLoaderAdd.active _ 1368 by decide))
    exact arriveResolvedMbarAddress hp hb (by unfold initializedMbarOffset; decide) hFire rfl
  · rw [ht, Flow.code_1900] at hc
    obtain rfl := Option.some.inj hc.symm
    have hb : t.regs 2535 = some (b32 (l.sharedBase + 0)) := hFrame.2.1.1
    exact arriveResolvedMbarAddress hp hb (by unfold initializedMbarOffset; decide) hFire rfl

/-- A fixed loader arrive names its verified shared barrier. -/
theorem loaderFixedArriveAddress {g index pc : Nat} {target : Loc} {tx n : Nat} {rel : Bool}
    {scope : MbarScope} (he : X.get (g, index) = some ⟨pc, .arrive target tx n rel scope⟩)
    (hSite : pc ∈ [686, 711, 737, 763, 1153, 1182, 1368, 1900]) :
    ∃ off ∈ [0, 8, 320, 328], target = ⟨.shared, g / l.block, l.sharedBase + off⟩ := by
  refine ⟨loaderExpectTxOffset pc, ?_, loaderFixedArriveOffset hp hX he hSite⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hSite
  rcases hSite with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- The two startup copy publications have distinct fixed offsets. -/
theorem loaderStartupAsyncAddress {g index pc : Nat} {target : Loc}
    (he : X.get (g, index) = some ⟨pc, .asyncArrive target true⟩) (hSite : pc ∈ [674, 904]) :
    target = ⟨.shared, g / l.block, l.sharedBase + (if pc = 674 then 32 else 40)⟩ := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hSite
  have hLo : 517 ≤ pc := by omega
  have hHi : pc < 1901 := by omega
  obtain ⟨_, t, o, ht, hFrame, hStep⟩ := loaderFixedSource hp hX he hLo hHi
  change t.pc = pc at ht
  obtain ⟨tm, hOut, hFire⟩ := hStep
  rcases out_ev hOut with ⟨f, rfl⟩ | ⟨ins, hc, rfl⟩
  · cases hFire.1
  rcases hSite with rfl | rfl
  · rw [ht, Flow.code_674] at hc
    obtain rfl := Option.some.inj hc.symm
    have hb : t.regs 2535 = some (b32 (l.sharedBase + 0)) := hFrame.2.1.1
    exact loaderAsyncArrivalResolvedAddress hp hb
      (by unfold initializedMbarOffset; decide) hFire rfl
  · rw [ht, Flow.code_904] at hc
    obtain rfl := Option.some.inj hc.symm
    have hb : t.regs 2535 = some (b32 (l.sharedBase + 0)) := hFrame.2.1.1
    exact loaderAsyncArrivalResolvedAddress hp hb
      (by unfold initializedMbarOffset; decide) hFire rfl


/-- A fixed loader asyncArrive names its verified shared barrier. -/
theorem loaderFixedAsyncAddress {g index pc : Nat} {target : Loc}
    (he : X.get (g, index) = some ⟨pc, .asyncArrive target true⟩) (hSite : pc ∈ [674, 904]) :
    ∃ off ∈ [32, 40], target = ⟨.shared, g / l.block, l.sharedBase + off⟩ := by
  refine ⟨_, ?_, loaderStartupAsyncAddress hp hX he hSite⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hSite
  rcases hSite with rfl | rfl <;> decide

omit hp hX in
/-- The base displacement used before the tensor instruction adds its own barrier offset. -/
def inputBarrierBase (site : Fin 14) : Nat :=
  if (inputSite site).barrierReg = 2535 then 0 else 320

/-- A tensor input names the completion object of its own decoded subbox. -/
theorem loaderTensorOffset {g index map : Nat} (site : Fin 14) {spec : TensorCopy.Spec}
    (he : X.get (g, index) = some ⟨(inputSite site).pc, .tensorIssue map spec⟩) :
    spec.mbar = ⟨.shared, g / l.block,
      l.sharedBase + (inputBarrierBase site + (inputSite site).barrierOffset)⟩ := by
  have hLo : 517 ≤ (inputSite site).pc := by fin_cases site <;> decide
  have hHi : (inputSite site).pc < 1901 := by fin_cases site <;> decide
  obtain ⟨_, t, o, ht, hFrame, hStep⟩ := loaderFixedSource hp hX he hLo hHi
  change t.pc = (inputSite site).pc at ht
  obtain ⟨tm, hOut, hFire⟩ := hStep
  rcases out_ev hOut with ⟨f, rfl⟩ | ⟨ins, hc, rfl⟩
  · have hKind := congrArg Event.kind hFire.1
    cases hKind
  rw [ht, inputSiteCode site] at hc
  obtain rfl := Option.some.inj hc.symm
  have hP := fires_cpTensor_issue_loc hFire rfl
  change mbarLoc l g t (inputSite site).barrierReg (inputSite site).barrierOffset =
    .ok spec.mbar at hP
  have resolve {delta : Nat}
      (hb : t.regs (inputSite site).barrierReg = some (b32 (l.sharedBase + delta)))
      (hValid : initializedMbarOffset (delta + (inputSite site).barrierOffset))
      (hOffset : delta = inputBarrierBase site) :
      spec.mbar = ⟨.shared, g / l.block,
        l.sharedBase + (inputBarrierBase site + (inputSite site).barrierOffset)⟩ := by
    rw [← hOffset]
    exact Except.ok.inj (hP.symm.trans (decodedMbarOffset (g := g) hp hb hValid))
  fin_cases site
  all_goals first
    | exact resolve (delta := 0) hFrame.2.1.1 (by unfold initializedMbarOffset; decide) rfl
    | apply resolve (delta := 320) _ (by unfold initializedMbarOffset; decide) rfl
      first
      | exact hFrame.2.2 ⟨701, 727, 1114, 320⟩ (by decide) (ht.symm ▸ (by decide))
      | exact hFrame.2.2 ⟨1144, 1173, 1140, 320⟩ (by decide) (ht.symm ▸ (by decide))
      | exact hFrame.2.2 ⟨1359, 1383, 1142, 320⟩ (by decide) (ht.symm ▸ (by decide))

/-- All fourteen unicast TMA inputs resolve to their decoded CTA completion barriers. -/
theorem loaderTensorAddress {g index map : Nat} (site : Fin 14) {spec : TensorCopy.Spec}
    (he : X.get (g, index) = some ⟨(inputSite site).pc, .tensorIssue map spec⟩) :
    ∃ off ∈ [0, 8, 320, 328], spec.mbar = ⟨.shared, g / l.block, l.sharedBase + off⟩ := by
  exact ⟨_, by fin_cases site <;> decide, loaderTensorOffset hp hX site he⟩

end
end PTX.Kernels.TmlFa4Fwd.Loader
