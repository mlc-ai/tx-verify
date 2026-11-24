-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderPrimingKActive
public import Kernels.TmlFa4Fwd.Proof.OutputFrame
public import Kernels.TmlFa4Fwd.Proof.LoaderProgress
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPrimingPacketGeometry
import Kernels.TmlFa4Fwd.Proof.EpilogueWarpReady
import Kernels.TmlFa4Fwd.Proof.OutputAssignedBox
import Kernels.TmlFa4Fwd.Proof.EpiloguePrefixStartup
import Kernels.TmlFa4Fwd.Proof.EpilogueCuts
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

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader

open PTX PTX.Flow PTX.Proof PTX.EventFrame Epilogue Prologue AsyncCopy
open PTX.Kernels.TmlFa4Fwd.Loader

theorem loaderOutputWrites {p : Params} {X : Execution} (hOutput : OutputFootprint p X)
    {w : Ref} {a : Acc} {data : List Byte} {loc : Loc} (hw : X.MemWrites w a data)
    (hc : a.Covers loc) (hs : loc.space = .global) :
    p.oRegion.Contains loc ∨ p.lseRegion.Contains loc := by
  rcases hOutput w a data loc hw hc hs with ho | ⟨q, hq, head, hh, k, hk, rfl⟩
  · exact .inl ho
  · exact .inr (lseByte_in hq hh hk)

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (hComplete : Complete l X) {g : Nat}
    (hg : g < l.threads) (hWarp : 14 ≤ Prologue.warpIndex l g)
    (hActive : g / l.block < tilePrefix p p.batch * p.heads)
include hp hX hComplete hg hWarp hActive

end

private theorem primingAfterSiteBounds {base lower ceiling : Nat}
    (hLo : base ≤ lower) (hHi : lower ≤ ceiling) (hLimit : ceiling ≤ 1901) (bound : Nat)
    (hTargets : ((kernel.code.drop base).take (1901 - base)).all
      (fun i => loaderPipelineCutOp ceiling 1901 bound [2535, 1062] i.op) = true) :
    ((kernel.code.drop lower).take (1901 - lower)).all
      (fun i => loaderPipelineCutOp lower 1901 bound [2535, 1062] i.op) = true := by
  apply List.all_eq_true.mpr
  intro ins hm
  obtain ⟨i, hi, hAt⟩ := List.mem_iff_getElem.mp hm
  have hIndex : i < 1901 - lower := hi.trans_le (by simp [List.length_take])
  have hGet : kernel.code[lower + i]? = some ins := by
    have h := List.getElem?_eq_getElem hi
    rw [List.getElem?_take_of_lt hIndex, List.getElem?_drop, hAt] at h
    exact h
  have hMember : ins ∈ (kernel.code.drop base).take (1901 - base) := by
    apply List.mem_of_getElem? (i := lower + i - base)
    rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop,
      Nat.add_sub_of_le (by omega : base ≤ lower + i)]
    exact hGet
  have hCheck := List.all_eq_true.mp hTargets ins hMember
  unfold loaderPipelineCutOp at hCheck ⊢
  refine Bool.and_eq_true_iff.mpr ⟨(Bool.and_eq_true_iff.mp hCheck).1, ?_⟩
  have hDest := (Bool.and_eq_true_iff.mp hCheck).2
  cases hOp : ins.op <;> simp only [hOp] at hDest ⊢
  all_goals try exact hDest
  case bra dst uni =>
    obtain ⟨hDst, hBound⟩ := Bool.and_eq_true_iff.mp hDest
    exact Bool.and_eq_true_iff.mpr ⟨decide_eq_true (hHi.trans (of_decide_eq_true hDst)), hBound⟩

private theorem primingCopyAfterBounds {site : Nat}
    (hSite : (550 ≤ site ∧ site ≤ 672) ∨ (810 ≤ site ∧ site ≤ 902)) (bound : Nat) :
    ((kernel.code.drop (site + 1)).take (1901 - (site + 1))).all
      (fun i => loaderPipelineCutOp (site + 1) 1901 bound [2535, 1062] i.op) = true := by
  rcases hSite with hK | hV
  · apply primingAfterSiteBounds (base := 551) (ceiling := 673)
      (by omega) (by omega) (by decide)
    set_option maxRecDepth 100000 in kernel_rfl
  · apply primingAfterSiteBounds (base := 811) (ceiling := 903)
      (by omega) (by omega) (by decide)
    set_option maxRecDepth 100000 in kernel_rfl

private theorem uniquePrimingCopyInWalk {l : Launch} {g : Nat} {s : TState} {es : List Event}
    {vs : List Visit} (warp : Fin 2) {site : Nat}
    (hSite : (550 ≤ site ∧ site ≤ 672) ∨ (810 ≤ site ∧ site ≤ 902))
    (ht : 174 ≤ s.pc ∧ s.pc ≤ 1901) (hShape : RingShape s)
    (hRegs : Holds s.regs [(2535, b32 l.sharedBase), (1062, b32 (14 + warp.val))])
    (hw : Walk kernel Assumptions.all l g s es vs) {i j : Nat} {a b : AsyncCopy.Spec}
    (hi : es[i]? = some ⟨site, .copy a⟩)
    (hj : es[j]? = some ⟨site, .copy b⟩) (hlt : i < j) : False := by
  let F := [(2535, b32 l.sharedBase), (1062, b32 (14 + warp.val))]
  have code (bound : Nat) : ((kernel.code.drop 174).take (1901 - 174)).all
      (fun i => loaderPipelineCutOp 174 1901 bound (F.map Prod.fst) i.op) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  induction hw generalizing i j with
  | stop => simp at hi
  | @tau s u es vs hStep hWalk ih =>
    obtain ⟨_, _, hClean, _⟩ := Softmax.tauScoreSource hStep
    by_cases hEnd : s.pc = 1901
    · have hPc := loaderTailEventPcs warp
        (pipelineAtCut hEnd hShape hRegs hClean ⟨_, Flow.code_1901, rfl⟩)
        (.tau hStep hWalk) _ (List.mem_of_getElem? hi)
      change site = 9205 at hPc
      omega
    · obtain ⟨hLo, hHi, hNextShape, hNextRegs⟩ := pipelineCutStep (F := F)
        (by decide) (by decide) ⟨ht.1, by omega⟩ (code u.pc) (.inl ⟨rfl, hStep⟩)
        hShape hRegs
      exact ih ⟨hLo, by omega⟩ hNextShape hNextRegs hi hj hlt
  | @ev s u ev es vs hStep hWalk ih =>
    have hClean : s.fault = none := by
      obtain ⟨tmpl, hOut, hFire⟩ := hStep
      cases hFault : s.fault with
      | none => rfl
      | some f =>
        simp only [out, hFault, Out.ev.injEq] at hOut
        subst tmpl
        cases hFire.2
    by_cases hEnd : s.pc = 1901
    · have hPc := loaderTailEventPcs warp
        (pipelineAtCut hEnd hShape hRegs hClean ⟨_, Flow.code_1901, rfl⟩)
        (.ev hStep hWalk) _ (List.mem_of_getElem? hi)
      change site = 9205 at hPc
      omega
    · obtain ⟨hLo, hHi, hNextShape, hNextRegs⟩ := pipelineCutStep (F := F)
        (by decide) (by decide) ⟨ht.1, by omega⟩ (code u.pc) (.inr ⟨_, rfl, hStep⟩)
        hShape hRegs
      cases j with
      | zero => omega
      | succ j =>
        cases i with
        | succ i => exact ih ⟨hLo, by omega⟩ hNextShape hNextRegs hi hj (by omega)
        | zero =>
          have hEv : ev = ⟨site, .copy a⟩ := Option.some.inj hi
          have hPc : s.pc = site := (estep_source_pc hStep).symm.trans (congrArg Event.pc hEv)
          have hNext : u.pc = site + 1 := by
            rw [← hPc]
            apply packetEventNext (by omega) (by omega) hStep |>.resolve_right
            intro hBad
            exact Bool.noConfusion <| hBad.2.symm.trans
              (loaderCopyEventSite (by omega) (by omega) hStep (congrArg Event.kind hEv))
          have hFrom := loaderWalkEventRange (lower := site + 1) warp (by omega)
            ⟨hNext.ge, by omega⟩ hNextShape hNextRegs
            (primingCopyAfterBounds hSite)
            hWalk _ (List.mem_of_getElem? hj)
          have : site + 1 ≤ site := hFrom.1
          omega
  | last hStep =>
    have hj' := (List.getElem?_eq_some_iff.mp hj).1
    simp at hj'
    omega

/-- Each decoded copy site of the first K or V packet appears at most once in a lane. -/
theorem uniquePrimingCopy {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) {g i j site : Nat}
    (hWarp : 14 ≤ warpIndex l g) (hSite : (550 ≤ site ∧ site ≤ 672) ∨ (810 ≤ site ∧ site ≤ 902))
    {a b : AsyncCopy.Spec}
    (hi : X.get (g, i) = some ⟨site, .copy a⟩)
    (hj : X.get (g, j) = some ⟨site, .copy b⟩) : i = j := by
  have hg : g < l.threads := event_thread_lt hX hi
  have hNonzero : 0 < warpIndex l g := by omega
  have hLate : 173 < site := by omega
  obtain ⟨s, _, hi', hs, hr⟩ := nonzeroCommonPrefixOfLateEvent hp hX hg hNonzero hi hLate
  obtain ⟨_, _, hj', _, _⟩ := nonzeroCommonPrefixOfLateEvent hp hX hg hNonzero hj hLate
  let warp : Fin 2 := ⟨warpIndex l g - 14, by have := warpIndex_lt hp g; omega⟩
  have hWarp' : 14 + warp.val = warpIndex l g := Nat.add_sub_of_le hWarp
  have hAt : At s 174 [(2535, b32 l.sharedBase), (1062, b32 (14 + warp.val))] :=
    hs.mono ⟨hs.2.2.2.2.2.1, hWarp'.symm ▸ hs.2.2.2.2.1, trivial⟩
  obtain ⟨_, hw⟩ := Mma.walkFromRun hr
  have h1 : ((X.tr g).drop 5)[i - 5]? = some ⟨site, .copy a⟩ := by
    rwa [List.getElem?_drop, Nat.add_sub_of_le hi']
  have h2 : ((X.tr g).drop 5)[j - 5]? = some ⟨site, .copy b⟩ := by
    rwa [List.getElem?_drop, Nat.add_sub_of_le hj']
  have hStart : 174 ≤ s.pc ∧ s.pc ≤ 1901 := by rw [hAt.1]; decide
  let unique {i j : Nat} {a b : AsyncCopy.Spec} :=
    uniquePrimingCopyInWalk warp hSite hStart (ringShapeOfAt hAt) hAt.2.2.2.2 hw
      (i := i) (j := j) (a := a) (b := b)
  rcases Nat.lt_trichotomy i j with h | h | h
  · exact (unique h1 h2 (by omega)).elim
  · exact h
  · exact (unique h2 h1 (by omega)).elim

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (hComplete : Complete l X)
    (hOutput : OutputFootprint p X) {g index : Nat} (group : PublishedCopyGroup l X (g, index))
    {target : Loc} (hIssue : X.AsyncArrive (g, index) target true)
    (hPriming : group.publication.packet = ⟨.priming, .key⟩) (hWarp : 14 ≤ warpIndex l g)
    (hActive : g / l.block < tilePrefix p p.batch * p.heads)
include hp hX hComplete hOutput group hIssue hPriming hWarp hActive

end PTX.Kernels.TmlFa4Fwd.Thread.Loader
