-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderLocal
public import Kernels.TmlFa4Fwd.Proof.LoaderPipelineCut
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
import Kernels.TmlFa4Fwd.Proof.RegisterHintBody
import Kernels.TmlFa4Fwd.Flow.Code.Part029

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow PTX.Proof PTX.EventFrame Prologue
open PTX.Kernels.TmlFa4Fwd.Loader

noncomputable section

/-- A subaccess of the aligned page, row or pointer cell in the owning thread's stack. -/
theorem stackCell {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g off size : Nat} (hg : g < l.threads) (array : Fin 4) (entry : Fin 2)
    (hSize : off + size ≤ if array.val < 2 then 8 else 4) :
    StackAccess l m g
      { loc := ⟨.local, g, l.localBase + kvLocalOffset array entry + off⟩, size := size } := by
  refine ⟨rfl, rfl, fun byte hb => ?_⟩
  change byte < size at hb
  have hBound := kvLocalOffset_bound array entry (byte := off + byte) (by omega)
  have hAlloc := hp.kv_local_allocated hg array entry (byte := off + byte) (by omega)
  dsimp only [Loc.at]
  exact ⟨by omega, by omega, by simpa only [Loc.at, Nat.add_assoc] using hAlloc⟩

namespace LocalAccessCode

def roots (l : Launch) (warp : Fin 2) : List (Nat × Value) :=
  [(2535, b32 l.sharedBase), (1062, b32 (14 + warp.val)), (7292, b64 l.localBase),
    (7293, b64 (l.localBase + 32)), (7294, b64 (l.localBase + 64)), (7295, b64 (l.localBase + 96))]

/-- Carry the stack pointers and a site invariant to an actual pipeline event. -/
theorem walkFrame {l : Launch} {g : Nat} {warp : Fin 2} {s : TState}
    {events : List Event} {visits : List Visit}
    (hw : Walk kernel Assumptions.all l g s events visits) (hLo : 174 ≤ s.pc) (hHi : s.pc ≤ 1901)
    (hShape : RingShape s) (hRoots : Holds s.regs (roots l warp))
    (Inv : TState → Prop) (hInv : Inv s)
    (hStep : ∀ {t u ev}, 174 ≤ t.pc → t.pc < 1901 → Holds t.regs (roots l warp) →
      Inv t → WStep kernel Assumptions.all l g t ev u → Inv u)
    {e : Event} (he : e ∈ events) (hEnd : e.pc < 1901) :
    ∃ t o, t.pc = e.pc ∧ RingShape t ∧ Holds t.regs (roots l warp) ∧
      Inv t ∧ EStep kernel Assumptions.all l g t e o := by
  have tail {x : TState} {es : List Event} {vs : List Visit} (hc : x.pc = 1901)
      (hs : RingShape x) (hR : Holds x.regs (roots l warp)) (hf : x.fault = none)
      (hW : Walk kernel Assumptions.all l g x es vs) (hem : e ∈ es) : False := by
    have hAt := pipelineAtCut hc hs hR hf ⟨_, PTX.Kernels.TmlFa4Fwd.Flow.code_1901, rfl⟩
    have hWarp : At x 1901 [(2535, b32 l.sharedBase), (1062, b32 (14 + warp.val))] :=
      hAt.mono ⟨hR.1, hR.2.1, trivial⟩
    have := Epilogue.loaderTailEventPcs warp hWarp hW e hem
    omega
  have advance {x u : TState} {ev : Option Event}
      (hl : 174 ≤ x.pc) (hh : x.pc < 1901) (hs : RingShape x)
      (hR : Holds x.regs (roots l warp)) (hStep : WStep kernel Assumptions.all l g x ev u) :
      174 ≤ u.pc ∧ u.pc ≤ 1901 ∧ RingShape u ∧ Holds u.regs (roots l warp) := by
    have hAudit : ((kernel.code.drop 174).take (1901 - 174)).all
        (fun i => loaderPipelineCutOp 174 1901 u.pc ((roots l warp).map Prod.fst) i.op) = true := by
      set_option maxRecDepth 100000 in kernel_rfl
    obtain ⟨hl', hh', hs', hR'⟩ :=
      pipelineCutStep (by decide) (by decide) ⟨hl, hh⟩ hAudit hStep hs hR
    exact ⟨hl', hh'.resolve_right (Nat.lt_irrefl _), hs', hR'⟩
  induction hw with
  | stop => cases he
  | @tau t u es vs ht hw ih =>
    by_cases hTail : t.pc = 1901
    · obtain ⟨_, _, hf, _⟩ := Softmax.tauScoreSource ht
      exact (tail hTail hShape hRoots hf (.tau ht hw) he).elim
    obtain ⟨hL, hH, hS, hR⟩ := advance hLo (by omega) hShape hRoots (.inl ⟨rfl, ht⟩)
    exact ih hL hH hS hR (hStep hLo (by omega) hRoots hInv (.inl ⟨rfl, ht⟩)) he
  | @ev t u ev es vs hs hw ih =>
    rcases List.mem_cons.mp he with rfl | hm
    · exact ⟨_, _, (estep_source_pc hs).symm, hShape, hRoots, hInv, hs⟩
    by_cases hTail : t.pc = 1901
    · have hf : t.fault = none := by
        obtain ⟨tm, ho, hFire⟩ := hs
        cases h : t.fault
        · rfl
        · simp only [out, h, Out.ev.injEq] at ho
          subst tm
          cases hFire.2
      exact (tail hTail hShape hRoots hf (.ev hs hw) he).elim
    obtain ⟨hL, hH, hS, hR⟩ := advance hLo (by omega) hShape hRoots (.inr ⟨_, rfl, hs⟩)
    exact ih hL hH hS hR (hStep hLo (by omega) hRoots hInv (.inr ⟨_, rfl, hs⟩)) hm
  | last hs =>
    obtain rfl := List.mem_singleton.mp he
    exact ⟨_, _, (estep_source_pc hs).symm, hShape, hRoots, hInv, hs⟩

theorem eventFrame {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {e : Event} (he : X.get i = some e) (hLo : 506 ≤ e.pc) (hHi : e.pc < 1901)
    (Inv : TState → Prop) (hInit : ∀ t, t.pc = 174 → Inv t)
    (hStep : ∀ warp {t u ev}, 174 ≤ t.pc → t.pc < 1901 → Holds t.regs (roots l warp) →
      Inv t → WStep kernel Assumptions.all l i.1 t ev u → Inv u) :
    ∃ (t : TState) (o : Option TState) (warp : Fin 2), t.pc = e.pc ∧
      RingShape t ∧ Holds t.regs (roots l warp) ∧ Inv t ∧
      EStep kernel Assumptions.all l i.1 t e o := by
  have hHint : e.pc ∉ registerHintSites := by
    simp only [registerHintSites, List.mem_cons, List.not_mem_nil, or_false]
    omega
  have hWarp : 14 ≤ warpIndex l i.1 := by
    rcases roleBodyPcOfEvent hp hX he (by omega) hHint with h | h
    · omega
    · split_ifs at h <;> omega
  let warp : Fin 2 := ⟨warpIndex l i.1 - 14, by have := warpIndex_lt hp i.1; omega⟩
  have hWord : 14 + warp.val = warpIndex l i.1 := Nat.add_sub_of_le hWarp
  have hg := Step.CtaBar.thread_lt_of_get hX he
  obtain ⟨s, _, hn, hs, hr⟩ := nonzeroCommonPrefixOfLateEvent hp hX hg (by omega) he (by omega)
  have hR : Holds s.regs (roots l warp) := by
    refine ⟨hs.2.2.2.2.2.1, hWord.symm ▸ hs.2.2.2.2.1, ?_, ?_, ?_, ?_, trivial⟩
    all_goals
      apply holds_mem hs.2.2.2.2
      simp [nonzeroBarrierFacts, abiFacts]
  obtain ⟨_, hWalk⟩ := Mma.walkFromRun hr
  have hm : e ∈ (X.tr i.1).drop 5 := by
    apply List.mem_of_getElem? (i := i.2 - 5)
    rw [List.getElem?_drop, Nat.add_sub_of_le hn]
    exact he
  obtain ⟨t, o, ht, hShape, hF, hInv, hFire⟩ :=
    walkFrame hWalk (by rw [hs.1]) (by rw [hs.1]; decide)
      (ringShapeOfAt hs) hR Inv (hInit s hs.1) (hStep warp) hm hHi
  exact ⟨t, o, warp, ht, hShape, hF, hInv, hFire⟩

structure PointerLoad where
  pc : Nat
  array : Fin 2
  entry : Fin 2
  low : Nat

def pointerLoads : List PointerLoad :=
  [⟨543, 0, 0, 1853⟩, ⟨609, 0, 1, 1871⟩, ⟨804, 0, 0, 1927⟩, ⟨854, 0, 1, 1945⟩,
   ⟨1003, 1, 0, 1998⟩, ⟨1072, 1, 1, 2019⟩, ⟨1238, 0, 0, 2077⟩, ⟨1292, 0, 1, 2098⟩,
   ⟨1469, 1, 0, 2156⟩, ⟨1537, 1, 1, 2177⟩, ⟨1632, 0, 0, 2198⟩, ⟨1685, 0, 1, 2219⟩]

def PointerLoad.access (s : PointerLoad) : MemAccess :=
  {kind := .load, space := some .local, sem := .weak, elem := .int .b 32, vec := 2,
   addr := ⟨.reg (7292 + s.array.val) 64, Int.ofNat (8 * s.entry.val)⟩,
   dsts := [some s.low, some (s.low + 1)]}

theorem pointerLoadDecoded (s : PointerLoad) (hs : s ∈ pointerLoads) :
    506 ≤ s.pc ∧ s.pc < 1901 ∧ kernel.code[s.pc]? = some ⟨none, .mem s.access⟩ := by
  simp only [pointerLoads, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨by decide, by decide, by set_option maxRecDepth 100000 in kernel_rfl⟩

theorem pointerLoadAccess {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} {t : TState} {warp : Fin 2} {s : PointerLoad}
    (hRoots : Holds t.regs (roots l warp)) {a : Acc}
    (hAcc : accessAcc l g t s.access = .ok a) :
    a = { loc := ⟨.local, g, l.localBase + 32 * s.array.val + 8 * s.entry.val + 4 * t.sub⟩
          size := 4, elem := t.sub } := by
  have hStack := hp.localMemory.2.1
  have hA := s.array.isLt
  have hE := s.entry.isLt
  have hReg : t.regs (7292 + s.array.val) = some (b64 (l.localBase + 32 * s.array.val)) := by
    have hm : (7292 + s.array.val, b64 (l.localBase + 32 * s.array.val)) ∈ roots l warp := by
      obtain ⟨_, array, _, _⟩ := s
      fin_cases array <;> simp [roots]
    exact holds_mem hRoots hm
  have hBits := readBits_b64 (L := l) (g := g) hReg (by omega)
  have hAddr : l.localBase + 32 * s.array.val + 8 * s.entry.val < 2 ^ 64 := by omega
  have hAlign : (l.localBase + 32 * s.array.val + 8 * s.entry.val) % 8 = 0 := by
    have := hp.localMemory.1
    omega
  have hWrap : wrapAddr 64 (BitVec.ofNat 64 (l.localBase + 32 * s.array.val))
      (Int.ofNat (8 * s.entry.val)) = l.localBase + 32 * s.array.val + 8 * s.entry.val := by
    unfold wrapAddr
    rw [show BitVec.ofInt 64 (Int.ofNat (8 * s.entry.val)) =
      BitVec.ofNat 64 (8 * s.entry.val) from rfl]
    rw [← BitVec.ofNat_add, truncBits_ofNat hAddr (by decide), toNat_ofNat_lt hAddr]
  rw [accessAcc_of_weak rfl, accessLoc_local_reg rfl rfl hBits] at hAcc
  have hWrap' : wrapAddr 64 (BitVec.ofNat 64 (l.localBase + 32 * s.array.val))
      (8 * (s.entry.val : Int)) = l.localBase + 32 * s.array.val + 8 * s.entry.val := by
    simpa using hWrap
  simpa [PointerLoad.access, hWrap', hAlign, DType.width, CacheHints.globalOnly, elemAcc, Loc.at,
    bind, Except.bind, pure, Except.pure] using hAcc.symm

end LocalAccessCode

/-- A loader read from a saved 64-bit source pointer, one event per 32-bit element. -/
def PointerReload (X : Execution) (issue : EvId) : Prop :=
  ∃ e, X.get issue = some e ∧ e.pc ∈ LocalAccessCode.pointerLoads.map LocalAccessCode.PointerLoad.pc

/-- Every actual pointer reload element fits its 64-bit cell and its allocated local stack. -/
theorem pointerReloadStackAccess {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {issue : EvId} {a : Acc} {bs : List (Option Byte)} (hr : X.Reads issue a bs)
    (hPointer : PointerReload X issue) :
    StackAccess l m issue.1 a ∧ a.loc.addr % 4 = 0 ∧ a.size = 4 := by
  obtain ⟨pc, he⟩ := hr
  obtain ⟨ev, hv, hm⟩ := hPointer
  have hEv := Option.some.inj (hv.symm.trans he)
  subst ev
  obtain ⟨s, hs, hPc⟩ := List.mem_map.mp hm
  change s.pc = pc at hPc
  subst pc
  obtain ⟨hLo, hHi, hCode⟩ := LocalAccessCode.pointerLoadDecoded s hs
  obtain ⟨t, o, warp, ht, hShape, hRoots, _, hStep⟩ :=
    LocalAccessCode.eventFrame hp hX he hLo hHi (fun _ => True) (by simp) (by intros; trivial)
  obtain ⟨u, hu⟩ : ∃ u, o = some u := by
    cases o with
    | some u => exact ⟨u, rfl⟩
    | none =>
      obtain ⟨_, _, hFire⟩ := hStep
      simpa [Ends] using fires_none_ends hFire
  subst o
  obtain ⟨ins, hIns, _, hFire⟩ := estep_event_source hStep
  change t.pc = s.pc at ht
  rw [ht, hCode] at hIns
  obtain rfl := Option.some.inj hIns.symm
  rw [ht] at hFire
  have hAcc := fires_localLoadAccess rfl rfl rfl hFire
  have hAddr := LocalAccessCode.pointerLoadAccess hp (s := s) hRoots hAcc
  have hSub : t.sub < 2 := Nat.lt_succ_of_le hShape.1.1
  let array : Fin 4 := ⟨s.array.val, by have := s.array.isLt; omega⟩
  have hArray : array.val < 2 := s.array.isLt
  have hWidth : 4 * t.sub + 4 ≤ (if array.val < 2 then 8 else 4) := by simp [hArray]; omega
  have hg := Step.CtaBar.thread_lt_of_get hX he
  have hStack := stackCell hp (off := 4 * t.sub) hg array s.entry hWidth
  rw [hAddr]
  refine ⟨?_, ?_, rfl⟩
  · simpa only [StackAccess, array, kvLocalOffset, hArray, ite_true, Nat.add_assoc]
      using hStack
  · dsimp only
    have := hp.localMemory.1
    omega

end
end PTX.Kernels.TmlFa4Fwd.Thread.Loader
