-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionStatsSync
public import Kernels.TmlFa4Fwd.Proof.CorrectionOutputSignal
import Kernels.TmlFa4Fwd.Flow.Code.Part124

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Flow PTX.Proof

noncomputable section

private theorem initialSyncCore {l : Launch} {g pc : Nat} {t : TState} {ins : Instr}
    (hPc : t.pc = pc) (hLo : 7985 ≤ pc) (hHi : pc ≤ 7988)
    (hCode : kernel.code[pc]? = some ins) (hCore : Assumptions.coreOp ins.op = true) :
    out kernel Assumptions.all l g t = out kernel [] l g t := by
  apply Assumptions.out_all_eq_nil _ _ _ (hPc.symm ▸ hCode) hCore
  all_goals
    rw [hPc]
    simp only [Assumptions.swExp2Sites, Assumptions.tcLdDataflowSites, Assumptions.delayedTmemSites,
      List.mem_cons, List.not_mem_nil, or_false]
    omega

private theorem syncSuffixNonempty {l : Launch} {X : Execution} {g pos : Nat}
    {t : TState} {o : Option TState} (hr : Run kernel Assumptions.all l g t ((X.tr g).drop pos) o)
    (hFuture : o = none ∨ ∃ j e, pos ≤ j ∧ 7988 < e.pc ∧ X.get (g,j) = some e) :
    (X.tr g).drop pos ≠ [] := by
  intro h
  rcases hFuture with rfl | ⟨j,e,hj,_,he⟩
  · rw [h] at hr
    cases hr
  · have hLen := (List.getElem?_eq_some_iff.mp he).1
    have hDrop := List.drop_eq_nil_iff.mp h
    change j < (X.tr g).length at hLen
    omega

private theorem syncSuffixNext {X : Execution} {g pos : Nat} {o : Option TState} {e : Event}
    (hFuture : o = none ∨ ∃ j e, pos ≤ j ∧ 7988 < e.pc ∧ X.get (g,j) = some e)
    (he : X.get (g,pos) = some e) (hPc : e.pc ≤ 7988) :
    o = none ∨ ∃ j e, pos+1 ≤ j ∧ 7988 < e.pc ∧ X.get (g,j) = some e := by
  rcases hFuture with rfl | ⟨j,f,hj,hf,hGet⟩
  · exact .inl rfl
  have hNe : pos ≠ j := by
    intro h
    subst j
    obtain rfl := Option.some.inj (hGet.symm.trans he)
    omega
  exact .inr ⟨j,f,by omega,hf,hGet⟩

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} {g pos : Nat} {t : TState}

/-- The initial two 64-lane correction rendezvous surround the real release of the
second statistics slot, before the lane branches on the number of KV blocks. -/
theorem observeCorrectionStartSyncPrefix {F : List (Nat × Value)} {result : Option TState}
    (hp : Pre p l m) (ht : At t 7985 F) (hBar0 : (1625, b32 (statsBarrierId l g 0)) ∈ F)
    (hBar1 : (1626, b32 (statsBarrierId l g 1)) ∈ F)
    (hRelease : (1069, b32 (l.sharedBase + 192)) ∈ F)
    (hFresh : ∀ pair ∈ F, pair.1 ≠ 5978 ∧ pair.1 ≠ 8994)
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop pos) result)
    (hFuture : result = none ∨ ∃ j e, pos ≤ j ∧ 7988 < e.pc ∧ X.get (g,j) = some e) :
    ∃ u,
      X.get (g, pos) = some ⟨7985, .bar (statsBarrierId l g 0) (some 64) .sync⟩ ∧
      X.get (g, pos + 1) =
        some ⟨7987, .arrive ⟨.shared, g / l.block, l.sharedBase + 192⟩ 0 1 true .cta⟩ ∧
      X.get (g, pos + 2) = some ⟨7988, .bar (statsBarrierId l g 1) (some 64) .sync⟩ ∧
      At u 7989 F ∧ Run kernel Assumptions.all l g u ((X.tr g).drop (pos + 3)) result := by
  obtain ⟨he0, hs, hS⟩ := observeCorrectionNamedBarrierPrefix hp 0 ht Flow.code_7985
    (initialSyncCore ht.1 (by decide) (by decide) Flow.code_7985 rfl)
    (holds_mem ht.2.2.2.2 hBar0) hr (syncSuffixNonempty hr hFuture)
  have hFuture₁ := syncSuffixNext hFuture he0 (by change 7985 ≤ 7988; decide)
  let v := next (setReg (next t) 5978 (b32 1))
  have hMove : run kernel [] l g 1 (next t) = some v := by
    apply run_local Flow.code_7986 rfl hs
    rw [execLocalA_nil, execLocal_move rfl]
    simp [execMove, readValue, readBits, Value.bytes, b32, bind, Except.bind, pure, Except.pure,
      DType.width, v, truncBits]
  have hModel := initialSyncCore (l := l) (g := g) hs.1 (by decide) (by decide) Flow.code_7986 rfl
  have hMoveAll : run kernel Assumptions.all l g 1 (next t) = some v := by
    simpa only [run, tauStep, hModel] using hMove
  have hv : At v 7987 ((5978, b32 1) :: F) :=
    hs.set (fun rv hm => (hFresh rv hm).1)
  have hLimit := hp.shared.2.1
  have hAlign := hp.shared.1
  have hKeep : ∀ rv ∈ (5978, b32 1) :: F, rv.1 ≠ 8994 := by
    intro rv hm
    rcases List.mem_cons.mp hm with rfl | hm
    · decide
    · exact (hFresh rv hm).2
  have hc : kernel.code[7987]? = some ⟨none,
      .mbarArrive 1069 0 (.imm 0) (.reg 5978) false true .cta (some 8994)⟩ := Flow.code_7987
  have hMore := syncSuffixNonempty hS hFuture₁
  obtain ⟨w, hw, he, hW⟩ := observeCorrectionReleasePrefix
    (base := l.sharedBase + 192) (off := 0) hv
    (initialSyncCore hv.1 (by decide) (by decide) hc rfl) hc
    (holds_mem hv.2.2.2.2 (List.mem_cons_of_mem _ hRelease)) hv.2.2.2.2.1
    (by simp only [Nat.add_zero]; omega) (by simp only [Nat.add_zero]; omega)
    hKeep (hS.after_local_nonempty (run_rtg hMoveAll) hMore) hMore
  have hFuture₂ := syncSuffixNext hFuture₁ he (by change 7987 ≤ 7988; decide)
  have hAt : At w 7988 F := hw.mono hw.2.2.2.2.2
  obtain ⟨he1, hU, hRest⟩ := observeCorrectionNamedBarrierPrefix hp 1 hAt Flow.code_7988
    (initialSyncCore hAt.1 (by decide) (by decide) Flow.code_7988 rfl)
    (holds_mem hAt.2.2.2.2 hBar1) hW (syncSuffixNonempty hW hFuture₂)
  exact ⟨_, he0, by simpa only [Nat.add_zero] using he,
    by simpa only [Nat.add_assoc] using he1, hU, by simpa only [Nat.add_assoc] using hRest⟩

end
end PTX.Kernels.TmlFa4Fwd.Correction
