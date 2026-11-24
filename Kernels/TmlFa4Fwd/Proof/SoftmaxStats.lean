-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxSignals
public import Kernels.TmlFa4Fwd.Flow.Code.Part118

import Kernels.TmlFa4Fwd.Proof.SoftmaxProbability

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section

structure StatsStore where
  pc : Nat
  base : Nat
  offset : Nat
  word : Nat

/-- Later rounds write a rescale word, and the terminal round writes sum then max. -/
def statsStore (i : Fin 4) : StatsStore := (#v[
  ⟨5682, 4571, 368, 1362⟩, ⟨6890, 5518, 368, 1492⟩,
  ⟨7614, 5814, 368, 7257⟩, ⟨7615, 5814, 1392, 7256⟩] : Vector StatsStore 4)[i]

private def statsStoreOp (i : Fin 4) : Op :=
  let s := statsStore i
  .mem {
    kind := .store
    space := some (.shared .cta)
    sem := .weak
    elem := .int .b 32
    addr := ⟨.reg s.base 32, s.offset⟩
    srcs := [.reg s.word] }

private theorem statsStoreCode (i : Fin 4) :
    kernel.code[(statsStore i).pc]? = some ⟨none, statsStoreOp i⟩ := by
  fin_cases i
  · exact Flow.code_5682
  · exact Flow.code_6890
  · exact Flow.code_7614
  · exact Flow.code_7615

/-- The row address, with separate per-lane words within both 128-row stages. -/
def statsBase (l : Launch) (g : Nat) (warp : Fin 8) : Nat :=
  l.sharedBase + 4 * (32 * warp.val + laneOf l g)

def statsAcc (l : Launch) (g : Nat) (warp : Fin 8) (i : Fin 4) : Acc :=
  {loc := ⟨.shared, g / l.block, statsBase l g warp + (statsStore i).offset⟩, size := 4}

/-- Decode a statistics store from its retained address and value words. -/
theorem statsStoreOut {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (warp : Fin 8) (i : Fin 4) {g : Nat} {t : TState} {v : Value}
    (ht : At t (statsStore i).pc [((statsStore i).base, b32 (statsBase l g warp)),
      ((statsStore i).word, v)]) (hV : v.bytes = 4) :
    out kernel Assumptions.all l g t = .ev (.write (statsAcc l g warp i) v.toBytes (next t)) := by
  let s := statsStore i
  let a := statsBase l g warp
  let off := s.offset
  have hCode := statsStoreCode i
  rw [← ht.1] at hCode
  have hOff : off ≤ 1392 ∧ off % 4 = 0 := by fin_cases i <;> decide
  have hWarp := warp.isLt
  have hLane : laneOf l g < 32 := Nat.mod_lt _ (by decide)
  have hShared := hp.shared.2.1
  have hAl := hp.shared.1
  have hSmall : a + off < 2 ^ 32 := by unfold a statsBase; omega
  have hBase : a < 2 ^ 32 := by omega
  have hAlign : (a + off) % 4 = 0 := by unfold a statsBase; omega
  have hr : t.regs s.base = some (b32 a) := ht.2.2.2.2.1
  have hw : t.regs s.word = some v := ht.2.2.2.2.2.1
  have hEff : effAddr l g t .shared s.base off = .ok ⟨.shared, g / l.block, a + off⟩ := by
    simp only [effAddr, sharedEffAddr, readReg, hr, b32, readBits, bind, Except.bind,
      pure, Except.pure, truncBits_ofNat hBase (by decide), BitVec.ofInt_natCast,
      ← BitVec.ofNat_add, truncBits_ofNat hSmall (by decide), BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (show a + off < 2 ^ 64 by omega)]
  rw [out_event ht.2.2.2.1 hCode rfl (by fin_cases i <;> rfl)]
  have hTmpl : eventTmpl Assumptions.all l g t (statsStoreOp i) =
      storeTmpl l g t .shared 32 s.base off [.reg s.word] := by
    fin_cases i <;> rfl
  rw [hTmpl]
  have hValue : storeValue 32 v = .ok v := storeValue_of_bytes hV
  rw [show storeTmpl l g t .shared 32 s.base off [.reg s.word] =
      .write (statsAcc l g warp i) v.toBytes (next t) by
    unfold storeTmpl
    rw [hEff]
    simp only [bind, Except.bind, List.length_singleton]
    rw [elemAcc_ok (by decide) hAlign]
    simp [ht.2.1, afterStore, Loc.at, readValue, readReg, hw, pure, Except.pure,
      hValue, statsAcc, a, off, s, next]]

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution}

/-- An actual statistics store writes the bytes in the named source register. -/
theorem statsStoreTracePrefix (hp : Pre p l m) (warp : Fin 8) (i : Fin 4) {g j : Nat} {t : TState}
    {v : Value} {o : Option TState} {F : List (Nat × Value)} (hV : v.bytes = 4)
    (ht : At t (statsStore i).pc F) (hA : ((statsStore i).base, b32 (statsBase l g warp)) ∈ F)
    (hW : ((statsStore i).word, v) ∈ F)
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop j) o) (hMore : (X.tr g).drop j ≠ []) :
    X.get (g, j) = some ⟨(statsStore i).pc, .wr (statsAcc l g warp i) v.toBytes⟩ ∧
      At (next t) ((statsStore i).pc + 1) F ∧
      Run kernel Assumptions.all l g (next t) ((X.tr g).drop (j + 1)) o := by
  have hFacts := ht.2.2.2.2
  have hn : Next kernel Assumptions.all l g t t (.write (statsAcc l g warp i) v.toBytes (next t)) :=
    ⟨.refl, statsStoreOut hp warp i
      (ht.mono ⟨holds_mem hFacts hA, holds_mem hFacts hW, trivial⟩) hV⟩
  obtain ⟨e, u, he, ⟨rfl, hu⟩, hTail⟩ := hn.continuing_at_nonempty (by
    rintro _ ⟨_, hBad⟩
    cases hBad) hRun hMore
  obtain rfl := Option.some.inj hu
  exact ⟨by simpa only [ht.1] using he, ht.next, hTail⟩

def rescaleStore (biased : Bool) : Fin 4 := if biased then 0 else 1

def rescaleRound (biased : Bool) : Round := if biased then .biased else .unbiased

private theorem rescaleStatsAdjacent (biased : Bool) :
    (statsStore (rescaleStore biased)).pc + 1 = statsPc (some (rescaleRound biased)) := by
  cases biased <;> rfl

theorem recordedProbabilitySuffixNonempty {l : Launch} {X : Execution}
    {g j : Nat} {s : TState} {ending : Option TState}
    (hRun : Run kernel Assumptions.all l g s ((X.tr g).drop j) ending)
    (hAvail : ending = none ∨ j < (X.tr g).length) :
    (X.tr g).drop j ≠ [] := by
  intro hEmpty
  rcases hAvail with rfl | hLen
  · rw [hEmpty] at hRun
    cases hRun
  · have h := congrArg List.length hEmpty
    simp only [List.length_drop,List.length_nil] at h
    omega

/-- Each repeated round publishes its rescale before the matching statistics arrival. -/
theorem rescaleStatsPathInPrefix (hp : Pre p l m) (warp : Fin 8) (biased : Bool) {g j : Nat}
    {t : TState} {scale : Value} {ending : Option TState} (hScale : scale.bytes = 4)
    (ht : At t (statsStore (rescaleStore biased)).pc
      [((statsStore (rescaleStore biased)).base, b32 (statsBase l g warp)),
        ((statsStore (rescaleStore biased)).word, scale), (5127, b32 (3 + warp.val))])
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop j) ending)
    (hAvail : ending = none ∨ j+1 < (X.tr g).length) :
    X.get (g, j) = some
      ⟨(statsStore (rescaleStore biased)).pc, .wr (statsAcc l g warp (rescaleStore biased))
        scale.toBytes⟩ ∧
      X.get (g, j + 1) = some
        ⟨statsPc (some (rescaleRound biased)), .bar (3 + warp.val) (some 64) .arrive⟩ ∧
      Run kernel Assumptions.all l g (next (next t)) ((X.tr g).drop (j + 2)) ending ∧
      TraceReach kernel Assumptions.all l g t (((X.tr g).drop j).take 2) (next (next t)) := by
  have hMore := recordedProbabilitySuffixNonempty hRun (hAvail.imp_right (by intro h; omega))
  obtain ⟨he, hu, hTail⟩ := statsStoreTracePrefix hp warp (rescaleStore biased) hScale ht
    (by simp) (by simp) hRun hMore
  have hpc := hu.1.trans (rescaleStatsAdjacent biased)
  obtain ⟨hb, hRest⟩ := statsTracePrefix hp.block (some (rescaleRound biased)) warp hpc
    hu.2.2.2.1 hu.2.2.2.2.2.2.1 hTail (recordedProbabilitySuffixNonempty hTail hAvail)
  refine ⟨he,hb,hRest,?_⟩
  have ho := statsStoreOut hp warp (rescaleStore biased) (g := g)
    (ht.mono ⟨ht.2.2.2.2.1,ht.2.2.2.2.2.1,trivial⟩) hScale
  have hWrite : EStep kernel Assumptions.all l g t
      ⟨(statsStore (rescaleStore biased)).pc,.wr (statsAcc l g warp (rescaleStore biased))
        scale.toBytes⟩ (some (next t)) := by
    refine ⟨_,ho,?_,rfl⟩
    rw [ht.1]
  have hBar : EStep kernel Assumptions.all l g (next t)
      ⟨statsPc (some (rescaleRound biased)),.bar (3+warp.val) (some 64) .arrive⟩
      (some (next (next t))) := by
    refine ⟨_,statsTemplate (g := g) hp.block (some (rescaleRound biased)) warp hpc
      hu.2.2.2.1 hu.2.2.2.2.2.2.1,?_,rfl⟩
    rw [hpc]
  rw [show (2 : Nat) = 1+1 from rfl,List.take_add,List.drop_drop,
    probabilityEventSingleton he,probabilityEventSingleton hb]
  exact .event hWrite (.event hBar (.refl _))

end
end PTX.Kernels.TmlFa4Fwd.Softmax
