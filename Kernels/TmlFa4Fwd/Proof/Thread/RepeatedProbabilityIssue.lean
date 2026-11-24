-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.OpeningProbabilityWait
public import Kernels.TmlFa4Fwd.Proof.SoftmaxRepeatedExponent
import all Kernels.TmlFa4Fwd.Proof.SoftmaxRepeatedExponent
public import Kernels.TmlFa4Fwd.Proof.CorrectionTripReads
import all Kernels.TmlFa4Fwd.Proof.SoftmaxProbability

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof Correction

/-- The delayed before-store wait issues from the same ready packed-store cursor. -/
theorem repeatedProbabilityLoadWaitOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) (round : Round) (q : Fin 4)
    {F : List (Nat × Value)} (c : OpeningTripCursor l X g (probabilityPc round q) F)
    (sources : List Nat) (hCode : kernel.code[probabilityPc round q]? = some
      ⟨none,.tcSt (probabilityReg round q) (sources.map Opnd.reg) .s32x32b⟩)
    (hDelay : delayedProbability round q = true) :
    let t := {c.ready with sub := 1}
    X.get (g,c.pos) = some ⟨probabilityPc round q,.tc .waitLd⟩ ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take (c.pos+1)) (some t) ∧
      Run kernel Assumptions.all l g t ((X.tr g).drop (c.pos+1)) c.ending := by
  let t := {c.ready with sub := 1}
  have hPc := c.checkpoint.1
  have hDecoded : kernel.code[c.ready.pc]? = some
      ⟨none,.tcSt (probabilityReg round q) (sources.map Opnd.reg) .s32x32b⟩ := by
    rw [hPc]
    exact hCode
  have hHook : Assumptions.all.any (·.tcStWaitLd c.ready.pc) = true := by
    rw [hPc,probabilityWaitHook,hDelay]
  have hWait : out kernel Assumptions.all l g c.ready = .ev (.tc .waitLd t) := by
    rw [out_event c.checkpoint.2.2.2.1 hDecoded rfl rfl,
      eventTmpl_tcSt_wait hHook c.checkpoint.2.1 (by rw [hp.block])]
  obtain ⟨he,hPast,hTail⟩ := probabilityCollectiveOfMaximal hg c.positive c.bounded
    hWait rfl nofun c.recorded c.localSteps c.remaining (fun h => ⟨X,hMax,rfl,c.released h⟩)
  rw [hPc] at he
  exact ⟨he,hPast,hTail⟩

/-- A repeated probability store fires from its actual reached packed words.
On a delayed store the same-PC load wait is recorded, and its peers release the store. -/
theorem repeatedProbabilityIssueOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) (round : Round) (stage : Fin 2) (q : Fin 4)
    {F : List (Nat × Value)} (c : OpeningTripCursor l X g (probabilityPc round q) F)
    (sources : List Nat) (weights : Nat → ℝ) (hLen : sources.length = 16)
    (hCode : kernel.code[probabilityPc round q]? = some
      ⟨none,.tcSt (probabilityReg round q) (sources.map Opnd.reg) .s32x32b⟩)
    (hWord : ∀ i (hi : i < sources.length), c.ready.regs sources[i] =
      some (probabilityWord weights (16*q.val+i)))
    (hAddr : c.ready.regs (probabilityReg round q) =
      some (b32 (probabilityAddress l g stage q)))
    (hWaitPeers : delayedProbability round q = true →
      c.pos+1 = (X.tr g).length → ∀ peer ∈ warpLanes l g, ∃ k,
        X.TcK (peer,k) (((X.tr g).take c.pos).countP isTcColl)) :
    let pos := if delayedProbability round q then c.pos+1 else c.pos
    (delayedProbability round q = true →
      X.get (g,c.pos) = some ⟨probabilityPc round q,.tc .waitLd⟩) ∧
    X.get (g,pos) = some (repeatedStoreEvent l g stage round q weights) ∧
    Run kernel Assumptions.all l g {} ((X.tr g).take (pos+1)) (some (next c.ready)) ∧
    Run kernel Assumptions.all l g (next c.ready) ((X.tr g).drop (pos+1)) c.ending := by
  let pc := probabilityPc round q
  let vals := (List.range' (16*q.val) 16).map (probabilityWord weights)
  let kind := TcKind.st (probabilityAddress l g stage q) vals .s32x32b
  have hRead := readConvertedWords (l := l) (g := g) weights sources (16*q.val) hWord
  rw [hLen] at hRead
  have hBytes : vals.all (·.bytes = 4) = true := by
    apply List.all_eq_true.mpr
    rintro v hv
    obtain ⟨_,_,rfl⟩ := List.mem_map.mp hv
    rfl
  have hCore : tcTmpl l g c.ready (.tcSt (probabilityReg round q)
      (sources.map Opnd.reg) .s32x32b) = .tc kind (next c.ready) :=
    probabilityCore stage q (by rw [hp.block]) hAddr
      (by simpa only [List.length_map] using hLen) hRead hBytes
  have hPc : c.ready.pc = pc := c.checkpoint.1
  have hDecoded : kernel.code[c.ready.pc]? = some
      ⟨none,.tcSt (probabilityReg round q) (sources.map Opnd.reg) .s32x32b⟩ := by
    rw [c.checkpoint.1]
    exact hCode
  have hHook : Assumptions.all.any (·.tcStWaitLd c.ready.pc) =
      delayedProbability round q := by rw [hPc,probabilityWaitHook]
  have hRelease (h : c.pos = (X.tr g).length) :
      ∃ Y, Maximal l kernel Assumptions.all m Y ∧ Y.tr = X.tr ∧ Step.Released l Y g :=
    ⟨X,hMax,rfl,c.released h⟩
  have hEvent (j : Nat) (he : X.get (g,j) = some ⟨pc,.tc kind⟩) :
      X.get (g,j) = some (repeatedStoreEvent l g stage round q weights) := he
  cases hDelay : delayedProbability round q with
  | false =>
    simp only [Bool.false_eq_true,ite_false]
    have hOut : out kernel Assumptions.all l g c.ready = .ev (.tc kind (next c.ready)) := by
      rw [out_event c.checkpoint.2.2.2.1 hDecoded rfl rfl,
        eventTmpl_tcSt_noWait (hHook.trans hDelay),hCore]
    obtain ⟨he,hPast,hTail⟩ := probabilityCollectiveOfMaximal hg c.positive c.bounded
      hOut rfl nofun c.recorded c.localSteps c.remaining hRelease
    exact ⟨False.elim,hEvent _ (hPc ▸ he),hPast,hTail⟩
  | true =>
    simp only [ite_true]
    let t := {c.ready with sub := 1}
    obtain ⟨he',hWaitPast,hWaitTail⟩ :=
      repeatedProbabilityLoadWaitOfMaximal hp hMax hg round q c sources hCode hDelay
    have hReset : {t with sub := 0} = c.ready := by
      have hz := c.checkpoint.2.1
      dsimp only [t]
      generalize c.ready = v at hz ⊢
      cases v
      simp_all
    have hOut : out kernel Assumptions.all l g t = .ev (.tc kind (next c.ready)) := by
      have htFault : t.fault = none := c.checkpoint.2.2.2.1
      have htCode : kernel.code[t.pc]? = _ := hDecoded
      have htHook : Assumptions.all.any (·.tcStWaitLd t.pc) = true := hHook.trans hDelay
      rw [out_event htFault htCode rfl rfl,
        eventTmpl_tcSt_afterWait htHook (show t.sub ≠ 0 from Nat.one_ne_zero),hReset,hCore]
    have hWaitRelease (h : c.pos+1 = (X.tr g).length) :
        ∃ Y, Maximal l kernel Assumptions.all m Y ∧ Y.tr = X.tr ∧ Step.Released l Y g :=
      ⟨X,hMax,rfl,probabilityCollectiveReleased he' (.inl rfl) rfl
        (hWaitPeers hDelay h) h⟩
    obtain ⟨hs,hPast,hTail⟩ := probabilityCollectiveOfMaximal hg (Nat.succ_pos _)
      (len_of_get he') hOut rfl nofun hWaitPast .refl hWaitTail hWaitRelease
    exact ⟨fun _ => he',hEvent _ (hPc ▸ hs),hPast,hTail⟩

end PTX.Kernels.TmlFa4Fwd.Softmax
