-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderPacketSites
public import Lemmas.Execution.EventFrameSource

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof PTX.EventFrame

noncomputable section

/-- An actual issue uses the effective addresses and source length of its decoded copy. -/
theorem packetCopyAccessesWithSize {l : Launch} {g : Nat}
    (site : Fin 6) (group : Fin 16) (upper : Bool)
    {t u : TState} {sp : AsyncCopy.Spec} (hPc : t.pc = packetPlanePc site group upper)
    (hStep : EStep kernel Assumptions.all l g t ⟨t.pc, .copy sp⟩ (some u)) :
    ∃ d a n,
      effAddr l g t .shared (packetDstReg site group) (packetDstOff site group upper) = .ok d ∧
      effAddr l g t .global (packetSrcReg site group) (packetSrcOff upper) = .ok a ∧
      sp.dst = {loc := d, size := 16} ∧ sp.src = {loc := a, size := n} ∧
      cpAsyncSourceSize l g t 16 (.size (.reg (packetSizeReg site group))) = .ok n := by
  have hLo : 174 ≤ t.pc := by
    rw [hPc]
    have hSite := loaderPacketBounds site
    unfold packetPlanePc packetPairPc
    omega
  have hHi : t.pc < 1906 := by
    rw [hPc]
    fin_cases site <;> fin_cases group <;> cases upper <;> decide
  have hCore : EStep kernel [] l g t ⟨t.pc, .copy sp⟩ (some u) := by
    obtain ⟨tmpl, hOut, hFire⟩ := hStep
    exact ⟨tmpl, by rwa [← loaderOutCore hLo hHi], hFire⟩
  obtain ⟨ins, hc, _, hf⟩ := estep_event_source hCore
  rw [hPc, packetFullCode] at hc
  obtain rfl := Option.some.inj hc
  simp only [eventTmpl, packetCopyOpCode, cpAsyncTmpl] at hf
  cases hd : effAddr l g t .shared (packetDstReg site group) (packetDstOff site group upper) with
  | error f => simp [hd, bind, Except.bind, ofExec, Fires] at hf
  | ok d =>
    cases hs : effAddr l g t .global (packetSrcReg site group) (packetSrcOff upper) with
    | error f => simp [hd, hs, bind, Except.bind, ofExec, Fires] at hf
    | ok a =>
      by_cases hAlign : d.addr % 16 = 0 ∧ a.addr % 16 = 0
      · cases hn : cpAsyncSourceSize l g t 16 (.size (.reg (packetSizeReg site group))) with
        | error f => simp [hd, hs, hAlign, hn, bind, Except.bind, ofExec, Fires] at hf
        | ok n =>
          simp [hd, hs, hAlign, hn, bulkPolicy, bind, Except.bind, ofExec, Fires,
            pure, Except.pure] at hf
          obtain ⟨rfl, _⟩ := hf
          exact ⟨d, a, n, rfl, rfl, rfl, rfl, rfl⟩
      · simp [hd, hs, hAlign, bind, Except.bind, ofExec, Fires, throw, throwThe,
          MonadExceptOf.throw] at hf

/-- An actual issue uses the effective addresses and vector width of its decoded copy. -/
theorem packetCopyAccesses {l : Launch} {g : Nat} (site : Fin 6) (group : Fin 16) (upper : Bool)
    {t u : TState} {sp : AsyncCopy.Spec} (hPc : t.pc = packetPlanePc site group upper)
    (hStep : EStep kernel Assumptions.all l g t ⟨t.pc, .copy sp⟩ (some u)) :
    ∃ d a n,
      effAddr l g t .shared (packetDstReg site group) (packetDstOff site group upper) = .ok d ∧
      effAddr l g t .global (packetSrcReg site group) (packetSrcOff upper) = .ok a ∧
      sp.dst = {loc := d, size := 16} ∧ sp.src = {loc := a, size := n} := by
  obtain ⟨d,a,n,hD,hS,hDst,hSrc,_⟩ := packetCopyAccessesWithSize site group upper hPc hStep
  exact ⟨d,a,n,hD,hS,hDst,hSrc⟩

/-- A full selector in the real source register entails a sixteen-byte copy read. -/
theorem packetCopyFullSize {l : Launch} {g : Nat} (site : Fin 6) (group : Fin 16) (upper : Bool)
    {t u : TState} {sp : AsyncCopy.Spec} (hPc : t.pc = packetPlanePc site group upper)
    (hWord : t.regs (packetSizeReg site group) = some (b32 16))
    (hStep : EStep kernel Assumptions.all l g t ⟨t.pc, .copy sp⟩ (some u)) :
    sp.src.size = 16 := by
  obtain ⟨d,a,n,hD,hS,hDst,hSrc,hN⟩ := packetCopyAccessesWithSize site group upper hPc hStep
  have hFull : cpAsyncSourceSize l g t 16 (.size (.reg (packetSizeReg site group))) =
      .ok 16 := by
    simp only [cpAsyncSourceSize]
    rw [readBits_b32 hWord (by decide)]
    rfl
  obtain rfl := Except.ok.inj (hN.symm.trans hFull)
  rw [hSrc]

/-- A verified swizzled register names the precise shared owner and full vector,
including when the copy's source is masked. -/
theorem packetCopyDestination {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g stage lane : Nat} (site : Fin 6) (group : Fin 16) (upper : Bool)
    (hStage : stage + packetStageShift site < 3) {t u : TState} {sp : AsyncCopy.Spec}
    (hPc : t.pc = packetPlanePc site group upper)
    (hDst : t.regs (packetDstReg site group) =
      some (b32 (kvCopyAddress l.sharedBase stage lane (group.val % 2) false)))
    (hStep : EStep kernel Assumptions.all l g t ⟨t.pc, .copy sp⟩ (some u)) :
    let addr := kvCopyAddress l.sharedBase (stage + packetStageShift site) lane group.val upper
    sp.dst = {loc := ⟨.shared, g / l.block, addr⟩, size := 16} := by
  let d := kvCopyAddress l.sharedBase stage lane (group.val % 2) false
  let o := packetDstOff site group upper
  let target := kvCopyAddress l.sharedBase (stage + packetStageShift site) lane group.val upper
  let loc : Loc := ⟨.shared, g / l.block, target⟩
  have hAddress : d + o = target := packetDestSum l.sharedBase stage lane site group upper
  have hRange := kvCopyAddress_range (lane := lane) (upper := upper) hp.shared.1
    hStage group.isLt (show 0 < 16 by decide)
  have hBound : d + o < 2 ^ 32 := by
    rw [hAddress]
    change l.sharedBase + 68608 ≤ target ∧ target + 0 < l.sharedBase + 166912 at hRange
    have := hp.shared.2.1
    omega
  have hDist : effAddr l g t .shared (packetDstReg site group) (o : Int) = .ok loc := by
    rw [effAddr_b32_off hDst hBound]
    change Except.ok (⟨.shared, g / l.block, d + o⟩ : Loc) = .ok loc
    rw [hAddress]
  obtain ⟨q, a, n, hQ, hA, hResult, hSrc⟩ := packetCopyAccesses site group upper hPc hStep
  have he : q = loc := Except.ok.inj (hQ.symm.trans hDist)
  simpa only [he] using hResult

/-- The live source register determines the lower/upper physical source address
of an actual copy. The event retains its separate decoded source-size operand. -/
theorem packetCopySource {l : Launch} {g src : Nat}
    (site : Fin 6) (group : Fin 16) (upper : Bool) {t u : TState} {sp : AsyncCopy.Spec}
    (hPc : t.pc = packetPlanePc site group upper)
    (hWord : t.regs (packetSrcReg site group) = some (b64 src)) (hBound : src < 2 ^ 64)
    (hStep : EStep kernel Assumptions.all l g t ⟨t.pc, .copy sp⟩ (some u)) :
    sp.src.loc = globalLoc ((src + packetSrcOff upper) % 2 ^ 64) := by
  let loc := globalLoc ((src + packetSrcOff upper) % 2 ^ 64)
  have hEff : effAddr l g t .global (packetSrcReg site group) (packetSrcOff upper) = .ok loc := by
    rw [effAddr, readBits_b64 hWord hBound]
    simp only [bind, Except.bind, pure, Except.pure, BitVec.ofInt_natCast, ← BitVec.ofNat_add,
      BitVec.toNat_ofNat, globalLoc, loc]
  obtain ⟨d, a, n, hD, hA, hDst, hResult⟩ := packetCopyAccesses site group upper hPc hStep
  have he : a = loc := Except.ok.inj (hA.symm.trans hEff)
  rw [hResult, he]

end
end PTX.Kernels.TmlFa4Fwd.Loader
