-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.EpilogueWarpStartup
public import Kernels.TmlFa4Fwd.Proof.PrologueFenceProgress
public import Kernels.TmlFa4Fwd.Proof.SoftmaxWarpZero
public import Kernels.TmlFa4Fwd.Proof.EpilogueDrainSearch
import Kernels.TmlFa4Fwd.Proof.Thread.RegisterProgress
import Kernels.TmlFa4Fwd.Proof.Epilogue
import Kernels.TmlFa4Fwd.Proof.PrologueDispatch
import Lemmas.Step.Read

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Epilogue
open PTX PTX.Flow PTX.Proof Prologue

noncomputable section

private def warp13EntryFrame (p : Params) (l : Launch) (g : Nat) : List (Nat × Value) :=
  [(7228,b32 p.batch),(2535,b32 l.sharedBase),(1178,b32 (l.sharedBase+68608)),
    (2390,b32 (l.sharedBase+208)),(6497,b32 (l.sharedBase+224)),
    (7290,.ptr 64 false (.param (param 10)) 0),(7502,b64 p.cuQBase),(7506,b64 p.cuQBase),
    (1072,b32 (g/l.block)),(1062,b32 13)]

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution}

/-- A maximal output scheduler lane returns from its actual register request with its ABI frame. -/
private theorem warp13EntryOfMaximal (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) (hw : warpIndex l g = 13) :
    ∃ t o, At t 2770 (warp13EntryFrame p l g) ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take 6) (some t) ∧
      Run kernel Assumptions.all l g t ((X.tr g).drop 6) o ∧
      Softmax.beforeFirstScan X g 6 ∧ 6 ≤ (X.tr g).length ∧
      (6 = (X.tr g).length → Step.Released l X g) := by
  have hNonzero : 0 < warpIndex l g := by omega
  obtain ⟨pos, _, _, e, _, _, _, he, _, hAt, _, _, _⟩ :=
    Thread.Register.requestReturn hp hMax hg
  obtain rfl := hAt hNonzero
  have hLen : 5 < (X.tr g).length := len_of_get he
  obtain ⟨s, o, hs, _, hPast, hr⟩ := nonzeroCommonPrefix hp hMax.1 hg hNonzero (by omega)
  let F := nonzeroBarrierFacts p l g
  have hFrame : Holds s.regs F := hs.2.2.2.2
  have hW := holds_lookup hFrame
    (show F.lookup 1062 = some (b32 (warpIndex l g)) by rfl)
  rw [hw] at hW
  have hBase := holds_lookup hFrame (show F.lookup 2535 = some (b32 l.sharedBase) by rfl)
  obtain ⟨t, ht, hPc, hf, hCta, hBuff, hBatch, hSub, hAcc, hKeep⟩ :=
    warp13DispatchWith (A := Assumptions.all) hp g s hg hs.1 hs.2.2.2.1 hW hBase
  have hOut := startupOut (A := Assumptions.all) (.inr (.inr (by rw [hPc]; decide)))
    (entryTemplate l g t hPc hf)
  have hn : Next kernel Assumptions.all l g s t (.setMaxReg false 80 (next t)) := ⟨run_rtg ht,hOut⟩
  obtain ⟨_, u, hGet, ⟨inst,rfl,hU⟩, hTail⟩ := hn.continuing_at_nonempty (pos := 5)
    (by rintro _ ⟨_,_,h⟩; cases h) hr
    (fun hNil => (Nat.not_le_of_lt hLen) (List.drop_eq_nil_iff.mp hNil))
  obtain rfl := Option.some.inj hU
  have hPrefix : Run kernel Assumptions.all l g {} ((X.tr g).take 6) (some (next t)) := by
    rw [List.take_succ_eq_append_getElem hLen, (List.getElem?_eq_some_iff.mp hGet).2]
    exact hPast.snoc hn.steps ⟨_,hOut,inst,rfl,rfl⟩
  have hFacts : Holds (next t).regs (warp13EntryFrame p l g) := by
    change Holds t.regs (warp13EntryFrame p l g)
    refine ⟨hBatch,(hKeep 2535 (by decide)).trans hBase,hBuff,?_,?_,?_,?_,?_,hCta,
      (hKeep 1062 (by decide)).trans hW,trivial⟩
    · exact (hKeep 2390 (by decide)).trans (holds_lookup hFrame (by rfl))
    · exact (hKeep 6497 (by decide)).trans (holds_lookup hFrame (by rfl))
    · exact (hKeep 7290 (by decide)).trans (holds_lookup hFrame (by rfl))
    · exact (hKeep 7502 (by decide)).trans (holds_lookup hFrame (by rfl))
    · exact (hKeep 7506 (by decide)).trans (holds_lookup hFrame (by rfl))
  have hBefore := Softmax.beforeFirstScan_three hp hMax.1 hg (by omega)
  obtain ⟨hFence,hCTA⟩ := nonzeroBarrierArrives hp hMax hg hNonzero
  have hCount := Softmax.beforeFirstScan_advance (Softmax.beforeFirstScan_advance
    (Softmax.beforeFirstScan_advance hBefore hFence rfl rfl) hCTA rfl rfl) hGet rfl rfl
  have hAt : At (next t) 2770 (warp13EntryFrame p l g) :=
    ⟨congrArg (·+1) hPc, hSub.trans hs.2.1,hAcc.trans hs.2.2.1,hf,hFacts⟩
  exact ⟨next t,o,hAt,hPrefix,hTail,hCount,len_of_get hGet,
    Thread.Register.releasedAfterRequest hp hMax hGet rfl⟩


private theorem firstCuQAtMaximal (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) (hLane : laneOf l g ≤ p.batch) {t v : TState} {o : Option TState}
    (hv : v.pc = 2776) (hLocal : Relation.ReflTransGen (Tau kernel Assumptions.all l g) t v)
    (hvOut : out kernel Assumptions.all l g v = .ev (.read
      {loc := globalLoc (p.cuQBase + 4 * laneOf l g), size := 4} (afterLoad v [7217])))
    (hPrefix : Run kernel Assumptions.all l g {} ((X.tr g).take 6) (some t))
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop 6) o) (hBound : 6 ≤ (X.tr g).length)
    (hRelease : 6 = (X.tr g).length → Step.Released l X g) (hProtected : DrainCuQProtected p X) :
    let a : Acc := {loc := globalLoc (p.cuQBase + 4 * laneOf l g), size := 4}
    let bytes := (b32 (p.qOffset (laneOf l g))).toBytes.map some
    X.get (g,6) = some ⟨2776,.rd a bytes⟩ ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take 7) (some (afterLoad v [7217] bytes)) ∧
      Run kernel Assumptions.all l g (afterLoad v [7217] bytes) ((X.tr g).drop 7) o := by
  dsimp only
  let addr : Acc := {loc := globalLoc (p.cuQBase + 4 * laneOf l g), size := 4}
  let value := b32 (p.qOffset (laneOf l g))
  let bytes := value.toBytes.map some
  have hValue : HasValue m addr.loc value := by
    simpa [addr,value,b32,HasValue,Value.bytes] using hp.cuQ _ hLane
  have hLt : 6 < (X.tr g).length := by
    by_contra! hLe
    have hEq := Nat.le_antisymm hBound hLe
    have hStarted : X.tr g ≠ [] := by intro h; rw [h,List.length_nil] at hEq; omega
    rw [List.take_of_length_le hLe] at hPrefix
    let e : Event := ⟨v.pc,.rd addr bytes⟩
    have hRead : NewRead l m X g e (fun _ => none) addr bytes := by
      refine ⟨rfl,?_ ,?_⟩
      · intro k hk c hc
        obtain rfl := Option.some.inj (hc.symm.trans (hValue k hk))
        simp [bytes,Value.toBytes,show k < value.bytes from hk,Execution.initialByte]
      · intro k w dst bs hk hWrite hCover _
        exact hProtected _ hLane k hk w dst bs hWrite hCover
    have hStep : EStep kernel Assumptions.all l g v e (some (afterLoad v [7217] bytes)) :=
      ⟨_,hvOut,bytes,rfl,rfl,rfl⟩
    exact hMax.not_grows (Step.read_counted_extension hMax.1 hg hStarted (hRelease hEq)
      hPrefix hLocal hStep hRead (Assumptions.wf_snoc_initial hMax.1 hRead))
  have hn : Next kernel Assumptions.all l g t v (.read addr (afterLoad v [7217])) :=
    ⟨hLocal,hvOut⟩
  obtain ⟨_,_,hGet,⟨bs,hSize,rfl,hRet⟩,hTail⟩ := hn.continuing_at_nonempty (pos := 6)
    (by rintro _ ⟨_,_,_,h⟩; cases h) hRun
    (fun h => (Nat.not_le_of_lt hLt) (List.drop_eq_nil_iff.mp h))
  obtain rfl := Option.some.inj hRet
  have hMem : X.MemReads (.thread (g,6)) addr bs := .inl ⟨_,hGet⟩
  have hBytes : bs = bytes := hMax.1.launch_value hMem rfl (hProtected _ hLane) hValue
  subst bs
  refine ⟨hv ▸ hGet,?_ ,hTail⟩
  rw [List.take_succ_eq_append_getElem hLt, (List.getElem?_eq_some_iff.mp hGet).2]
  exact hPrefix.snoc hLocal ⟨_,hvOut,bytes,hSize,rfl,rfl⟩

/-- A maximal output scheduler lane reaches the first down shuffle, using its protected launch
word when it is inside the CuQ sentinel and zero otherwise. -/
theorem warp13ShuffleCursorOfMaximal (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) (hw : warpIndex l g = 13) (hProtected : DrainCuQProtected p X) :
    ∃ j t u o, 0 < j ∧ j ≤ (X.tr g).length ∧ Softmax.beforeFirstScan X g j ∧
      (j = (X.tr g).length → Step.Released l X g) ∧
      At u 2777 ([(7228,b32 p.batch),(7217,b32 (firstSchedulerWord p (laneOf l g)))] ++
        schedulerStartupFrame p l g) ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take j) (some t) ∧
      Run kernel Assumptions.all l g t ((X.tr g).drop j) o ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u := by
  obtain ⟨t,o,ht,hPast,hTail,hCount,hBound,hReleased⟩ := warp13EntryOfMaximal hp hMax hg hw
  let keep := warp13EntryFrame p l g
  obtain ⟨u,hLocal,huFault,hu,huLane,huZero,hPart,hClean,hKeep⟩ :=
    enterSchedulerWith (A := Assumptions.all) hp g t ht.1 ht.2.2.2.1 ht.2.2.2.2.1
  have hU : Holds u.regs keep := holdsSchedulerFrame ht.2.2.2.2
    (regs := keep.map Prod.fst)
    (fun r hr => by
      apply hKeep r
      change r ∈ [7228,2535,1178,2390,6497,7290,7502,7506,1072,1062] at hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr ⊢
      omega)
    (fun pair hm => List.mem_map_of_mem (f := Prod.fst) hm)
  have hAdd {s : TState} (h : Holds s.regs keep)
      (hLane : s.regs 1201 = some (b32 (laneOf l g))) :
      Holds s.regs (schedulerStartupFrame p l g) := by
    change Holds s.regs (keep.tail ++ [(1201,b32 (laneOf l g))])
    exact (holds_append _ _ _).2 ⟨h.2,hLane,trivial⟩
  by_cases hSkip : p.batch < laneOf l g
  · rw [ite_eq_left hSkip] at hu
    rw [firstSchedulerWord,ite_eq_left hSkip]
    obtain ⟨hs,ha⟩ := hClean ⟨ht.2.1,ht.2.2.1⟩
    exact ⟨6,t,u,o,by decide,hBound,hCount,hReleased,
      ⟨hu,hs,ha,huFault,hU.1,huZero,hAdd hU huLane⟩,hPast,hTail,run_rtg hLocal⟩
  · rw [ite_eq_right hSkip] at hu
    have hLane := Nat.le_of_not_lt hSkip
    obtain ⟨v,hV,hPc,hFault,hSub,hAcc,hOut,hFrame⟩ :=
      schedulerLaneReadWithFrame (A := Assumptions.all) hp g u hLane hu huFault
        (hPart hLane).1 (hPart hLane).2 huLane (holds_lookup hU (by rfl))
    obtain ⟨he,hPrefix,hRun⟩ := firstCuQAtMaximal hp hMax hg hLane hPc
      ((run_rtg hLocal).trans (run_rtg hV)) hOut hPast hTail hBound hReleased hProtected
    let q := b32 (p.qOffset (laneOf l g))
    let w := afterLoad v [7217] (q.toBytes.map some)
    have hw : w = next (setReg v 7217 q) := by
      dsimp only [w]
      rw [afterLoad_ok hSub hAcc (PTX.Proof.rebuild_scalar (v := q) (show 0 < 4 by decide) rfl)]
      simp only [next,setReg,hSub,hAcc]
    have hKeeps {r : Nat} (hr : r ≠ 7217) (hLocal : r ∉ [7862,7863]) :
        w.regs r = u.regs r := by
      rw [hw]
      change (Function.update v.regs 7217 (some q)) r = _
      exact (Function.update_of_ne hr _ _).trans (hFrame _ hLocal)
    have hSaved : Holds w.regs keep := holdsSchedulerFrame hU
      (regs := [7228,2535,1178,2390,6497,7290,7502,7506,1072,1062])
      (fun r hr => by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
        exact hKeeps (by omega) (by simp; omega))
      (fun pair hm => List.mem_map_of_mem (f := Prod.fst) hm)
    have hW : At w 2777 ((7228,b32 p.batch) :: (7217,q) :: schedulerStartupFrame p l g) := by
      exact ⟨by rw [hw]; exact congrArg (·+1) hPc, by rw [hw]; exact hSub,
        by rw [hw]; exact hAcc, by rw [hw]; exact hFault,hSaved.1,
        by rw [hw]; simp [next,setReg],
        hAdd hSaved ((hKeeps (by decide) (by decide)).trans huLane)⟩
    rw [firstSchedulerWord,ite_eq_right hSkip]
    have hCount' := Softmax.beforeFirstScan_advance hCount he rfl rfl
    exact ⟨7,w,w,o,by decide,len_of_get he,hCount',releasedIfLast he (by intro h; cases h),
      hW,hPrefix,hRun,.refl⟩


end
end PTX.Kernels.TmlFa4Fwd.Epilogue
