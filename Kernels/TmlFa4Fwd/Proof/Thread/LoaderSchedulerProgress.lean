-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.SchedulerWarpProgress
public import Kernels.TmlFa4Fwd.Proof.LoaderCuQ
import Kernels.TmlFa4Fwd.Proof.Thread.RegisterProgress
public import Kernels.TmlFa4Fwd.Proof.PrologueFenceProgress
public import Kernels.TmlFa4Fwd.Proof.EpilogueDrainSearch
import Kernels.TmlFa4Fwd.Proof.SoftmaxWarpZero
import Lemmas.Step.Read

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof Prologue Epilogue

noncomputable section

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g : Nat} (hg : g < l.threads)
include hp hMax hg

private theorem entryOfMaximal (hw : 14 ≤ warpIndex l g) :
    ∃ t o, At t 180 (loaderEntryFacts p l g (warpIndex l g)) ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take 6) (some t) ∧
      Run kernel Assumptions.all l g t ((X.tr g).drop 6) o ∧
      Softmax.beforeFirstScan X g 6 ∧ 6 ≤ (X.tr g).length ∧
      (6 = (X.tr g).length → Step.Released l X g) := by
  have hNZ : 0 < warpIndex l g := by omega
  obtain ⟨pos,_,_,_,_,_,_,he,_,hPos,_,_,_⟩ := Thread.Register.requestReturn hp hMax hg
  obtain rfl := hPos hNZ
  have hLen : 5 < (X.tr g).length := len_of_get he
  obtain ⟨s,o,hs,hTid,hPast,hr⟩ := nonzeroCommonPrefix hp hMax.1 hg hNZ (by omega)
  let warp : Fin 16 := ⟨warpIndex l g, warpIndex_lt hp g⟩
  have hs' : At s 174 (loaderBarrierFacts p l g warp.val) := by
    have h := hs.2.2.2.2
    have hAbi : Holds s.regs (abiFacts p l) := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    apply hs.mono
    rw [loaderBarrierFacts, holds_append]
    exact ⟨⟨h.1,h.2.1,hAbi⟩,hTid,trivial⟩
  obtain ⟨v,hv,hn⟩ := loaderHintNext hp hg warp hw hs'
  obtain ⟨_,_,hGet,⟨inst,rfl,hState⟩,hTail⟩ := hn.continuing_at_nonempty (pos := 5)
    (by rintro _ ⟨_,_,h⟩; cases h) hr
    (fun hNil => (Nat.not_le_of_lt hLen) (List.drop_eq_nil_iff.mp hNil))
  obtain rfl := Option.some.inj hState
  have hPrefix : Run kernel Assumptions.all l g {} ((X.tr g).take 6) (some (next v)) := by
    rw [List.take_succ_eq_append_getElem hLen, (List.getElem?_eq_some_iff.mp hGet).2]
    exact hPast.snoc hn.steps ⟨_,hn.stop,inst,rfl,rfl⟩
  have hBefore := Softmax.beforeFirstScan_three hp hMax.1 hg (by omega)
  obtain ⟨hFence,hCTA⟩ := nonzeroBarrierArrives hp hMax hg hNZ
  have hCount := Softmax.beforeFirstScan_advance (Softmax.beforeFirstScan_advance
    (Softmax.beforeFirstScan_advance hBefore hFence rfl rfl) hCTA rfl rfl) hGet rfl rfl
  exact ⟨next v,o,hv.next,hPrefix,hTail,hCount,len_of_get hGet,
    Thread.Register.releasedAfterRequest hp hMax hGet rfl⟩

private theorem firstReadOfMaximal (hLane : laneOf l g ≤ p.batch) {t v : TState} {o : Option TState}
    (hv : v.pc = 186) (hLocal : Relation.ReflTransGen (Tau kernel Assumptions.all l g) t v)
    (hvOut : out kernel Assumptions.all l g v = .ev (.read
      {loc := globalLoc (p.cuQBase + 4 * laneOf l g), size := 4} (afterLoad v [7159])))
    (hPrefix : Run kernel Assumptions.all l g {} ((X.tr g).take 6) (some t))
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop 6) o) (hBound : 6 ≤ (X.tr g).length)
    (hRelease : 6 = (X.tr g).length → Step.Released l X g) (hProtected : DrainCuQProtected p X) :
    let a : Acc := {loc := globalLoc (p.cuQBase + 4 * laneOf l g), size := 4}
    let bytes := (b32 (p.qOffset (laneOf l g))).toBytes.map some
    X.get (g,6) = some ⟨186,.rd a bytes⟩ ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take 7) (some (afterLoad v [7159] bytes)) ∧
      Run kernel Assumptions.all l g (afterLoad v [7159] bytes) ((X.tr g).drop 7) o := by
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
    have hStep : EStep kernel Assumptions.all l g v e (some (afterLoad v [7159] bytes)) :=
      ⟨_,hvOut,bytes,rfl,rfl,rfl⟩
    exact hMax.not_grows (Step.read_counted_extension hMax.1 hg hStarted (hRelease hEq)
      hPrefix hLocal hStep hRead (Assumptions.wf_snoc_initial hMax.1 hRead))
  have hn : Next kernel Assumptions.all l g t v (.read addr (afterLoad v [7159])) :=
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

private theorem shuffleLaneOfMaximal (hw : 14 ≤ warpIndex l g) (hCuQ : DrainCuQProtected p X) :
    ∃ j t u o, 0 < j ∧ j ≤ (X.tr g).length ∧ Softmax.beforeFirstScan X g j ∧
      (j = (X.tr g).length → Step.Released l X g) ∧
      At u 187 (loaderCuQFacts p l g (warpIndex l g)) ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take j) (some t) ∧
      Run kernel Assumptions.all l g t ((X.tr g).drop j) o ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u := by
  obtain ⟨t,o,ht,hPast,hTail,hCount,hBound,hReleased⟩ := entryOfMaximal hp hMax hg hw
  obtain ⟨u,hLocal,hu⟩ := loaderCuQGate hp ht
  by_cases hLane : laneOf l g ≤ p.batch
  · have huAt : At u 184 ((1073,b32 (laneOf l g)) :: loaderEntryFacts p l g (warpIndex l g)) :=
      ⟨by simpa [Nat.not_lt_of_ge hLane] using hu.1,hu.2.1,hu.2.2.1,hu.2.2.2.1,hu.2.2.2.2.2⟩
    obtain ⟨s,hs,hn⟩ := loaderCuQNext hp hLane huAt
    obtain ⟨he,hPrefix,hRun⟩ := firstReadOfMaximal hp hMax hg hLane hs.1
      (hLocal.trans hn.steps) hn.stop hPast hTail hBound hReleased hCuQ
    let value := b32 (p.qOffset (laneOf l g))
    have hState : afterLoad s [7159] (value.toBytes.map some) = next (setReg s 7159 value) := by
      have hScalar := PTX.Proof.rebuild_scalar (v := value) (show 0 < 4 by decide) rfl
      rw [afterLoad_ok hs.2.1 hs.2.2.1 hScalar]
      simp [next,setReg,hs.2.1,hs.2.2.1]
    rw [hState] at hPrefix hRun
    have hFresh : ∀ x ∈ ((1073,b32 (laneOf l g)) :: loaderEntryFacts p l g (warpIndex l g)),
        x.1 ≠ 7159 := by
      intro pair hm heq
      have hh := List.mem_map_of_mem (f := Prod.fst) hm
      rw [heq] at hh
      exact (of_decide_eq_true rfl : 7159 ∉
        [1073,7170,1072,1062,2535,1,7492,7493,7494,7495,1663,1664,7496,7497,7498,7499,
          7500,7501,7502,7503,7504,7505,7291,7290,7289,7506,7292,7293,7294,7295,1665,1061]) hh
    have hAt : At (next (setReg s 7159 value)) 187 (loaderCuQFacts p l g (warpIndex l g)) := by
      change At _ 187 ((7159,b32 (drainCuQ p (laneOf l g))) ::
        (1073,b32 (laneOf l g)) :: loaderEntryFacts p l g (warpIndex l g))
      rw [drainCuQ,ite_eq_left hLane]
      exact hs.set (v := value) hFresh
    exact ⟨7,_,_,o,by decide,len_of_get he,Softmax.beforeFirstScan_advance hCount he rfl rfl,
      releasedIfLast he (by intro h; cases h),hAt,hPrefix,hRun,.refl⟩
  · have hAt : At u 187 (loaderCuQFacts p l g (warpIndex l g)) := by
      refine ⟨?_,hu.2.1,hu.2.2.1,hu.2.2.2.1,?_⟩
      · simpa [Nat.lt_of_not_ge hLane] using hu.1
      · change Holds u.regs ((7159,b32 (drainCuQ p (laneOf l g))) ::
          (1073,b32 (laneOf l g)) :: loaderEntryFacts p l g (warpIndex l g))
        rw [drainCuQ,ite_eq_right hLane]
        exact hu.2.2.2.2
    exact ⟨6,t,u,o,by decide,hBound,hCount,hReleased,hAt,hPast,hTail,hLocal⟩

/-- Every lane of either loader warp reaches the first down shuffle in a maximal execution. -/
theorem firstShuffleOfMaximal (hw : 14 ≤ warpIndex l g) (hCuQ : DrainCuQProtected p X) :
    ∃ ends, Nonempty (SchedulerWarpReached l X g 187
      (fun lane => loaderCuQFacts p l (warpLane l g lane) (warpIndex l g)) 3 0 ends) := by
  classical
  let thread := warpLane l g
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hC (lane : Nat) (hl : lane < 32) : ∃ j t u o,
      0 < j ∧ j ≤ (X.tr (thread lane)).length ∧ Softmax.beforeFirstScan X (thread lane) j ∧
      (j = (X.tr (thread lane)).length → Step.Released l X (thread lane)) ∧
      At u 187 (loaderCuQFacts p l (thread lane) (warpIndex l g)) ∧
      Run kernel Assumptions.all l (thread lane) {} ((X.tr (thread lane)).take j) (some t) ∧
      Run kernel Assumptions.all l (thread lane) t ((X.tr (thread lane)).drop j) o ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l (thread lane)) t u := by
    have hSame := (Step.sameWarp_lane hBlock hg hl).1
    have hWarp : warpIndex l (thread lane) = warpIndex l g := hSame.2.symm
    obtain ⟨j,t,u,o,hPos,hBound,hCount,hReady,hAt,hPrefix,hTail,hLocal⟩ :=
      shuffleLaneOfMaximal hp hMax hSame.1.2.1 (hWarp.symm ▸ hw) hCuQ
    change At u 187 (loaderCuQFacts p l (thread lane) (warpIndex l (thread lane))) at hAt
    rw [hWarp] at hAt
    exact ⟨j,t,u,o,hPos,hBound,hCount,hReady,hAt,hPrefix,hTail,hLocal⟩
  let _ : Inhabited TState := ⟨{}⟩
  choose! j t u o hPos hBound hCount hReady hAt hPrefix hTail hLocal using hC
  exact ⟨o,⟨⟨⟨j,t,u,⟨fun lane hl => (hCount lane hl).1,fun lane hl => (hCount lane hl).2⟩,
    hTail,hLocal,hAt⟩,hPos,hBound,hReady,hPrefix⟩⟩⟩

end
end PTX.Kernels.TmlFa4Fwd.Loader
