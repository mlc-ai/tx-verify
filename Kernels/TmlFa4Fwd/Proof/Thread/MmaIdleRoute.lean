-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaFallbackSearch
import Kernels.TmlFa4Fwd.Flow.Code.Part032
import Kernels.TmlFa4Fwd.Flow.Code.Part043
import Kernels.TmlFa4Fwd.Proof.Thread.StatisticsAllocationExclusion
import Kernels.TmlFa4Fwd.Proof.MmaReadyReleaseElection
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
import Kernels.TmlFa4Fwd.Proof.Thread.TraceFloor
import Kernels.TmlFa4Fwd.Proof.MmaRoleFrame
import Lemmas.Flow.ReturningPrefix
import Lemmas.Flow.NotTcAny

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof PTX.Assumption Prologue Epilogue Thread Thread.Allocation

noncomputable section

private theorem signedSmall {n : Nat} (hn : n < 2 ^ 31) :
    toSigned 32 (BitVec.ofNat 64 n) = (n : Int) := by
  have h64 : n < 2 ^ 64 := by omega
  have h32 : n < 2 ^ 32 := by omega
  simp only [toSigned, toNat_ofNat_lt h64, Nat.mod_eq_of_lt h32, ite_eq_left hn]

private theorem idleAfterFirstGroup {l : Launch} {g cta batch work : Nat}
    (hCta : cta + 1 < 2 ^ 31) (hBatch : batch ≤ 31) :
    Seg kernel [] l g 7 1985
      [(1072,b32 cta),(7203,b32 batch),(7200,b32 work)] 1992
      [(347,.pred true),(7200,b32 (cta+1)),(7199,b32 batch),
        (1072,b32 cta),(7203,b32 batch),(7194,b32 work)] := by
  intro t ht
  have hCta32 : cta < 2 ^ 32 := by omega
  have hCtaNext32 : cta + 1 < 2 ^ 32 := by omega
  have hBatch32 : batch < 2 ^ 32 := by omega
  have hBatch31 : batch < 2 ^ 31 := by omega
  have hThirty : toSigned 32
      (truncBits 32 (truncBits 32 (truncBits 32 (truncBits 32 0#64) + truncBits 32 31#64))) =
      31 := by decide
  have hOne : truncBits 32 1#64 = (1#64 : BitVec 64) := rfl
  have hAdd : truncBits 32 (BitVec.ofNat 64 cta + truncBits 32 1#64) =
      BitVec.ofNat 64 (cta + 1) := by
    rw [hOne, show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, ← BitVec.ofNat_add]
    exact truncBits_ofNat hCtaNext32 (by decide)
  seg_fp ht using
    simp [b32, hAdd, truncBits_ofNat hCta32 (by decide), truncBits_ofNat hBatch32 (by decide),
      signedSmall hBatch31, hThirty, compare, Option.getD_some, Nat.not_lt_of_ge hBatch,
      show (batch : Int) ≤ 31 by exact_mod_cast hBatch]

private theorem exhaustedFallback {l : Launch} {g cta batch : Nat}
    (hCta : cta + 1 < 2 ^ 31) :
    Seg kernel [] l g 2 2039 [(7200,b32 (cta+1)),(1072,b32 cta),(7199,b32 batch),
      (7203,b32 batch)] 2041 [(360,.pred false),(7199,b32 batch),(7203,b32 batch)] := by
  intro t ht
  have hCta31 : cta < 2 ^ 31 := by omega
  have hCta32 : cta < 2 ^ 32 := by omega
  have hCtaNext32 : cta + 1 < 2 ^ 32 := by omega
  seg_fp ht using
    simp [truncBits_ofNat hCta32 (by decide), truncBits_ofNat hCtaNext32 (by decide),
        signedSmall hCta31, signedSmall hCta, compare, Option.getD_some]

private theorem exhaustedEnterTail {l : Launch} {g batch : Nat}
    (hBatch : batch < 2 ^ 31) :
    Seg kernel [] l g 3 2042 [(7199,b32 batch),(7203,b32 batch)] 2045
      [(361,.pred true),(781,.pred false),(7202,b32 256)] := by
  intro t ht
  have hBatch32 : batch < 2 ^ 32 := by omega
  seg_fp ht using first
    | rfl
    | simp [truncBits_ofNat hBatch32 (by decide), signedSmall hBatch, compare,
        Option.getD_some]

private theorem emptyWorkGate {p : Params} {l : Launch} {m : Mem0} (_hp : Pre p l m)
    {g : Nat} :
    Seg kernel [] l g 2 2106 [(2535,b32 l.sharedBase),(781,.pred false)] 2108
      [(375,.pred true)] := by
  intro t ht
  seg_fp ht using rfl

/-- An exhausted MMA search follows the common no-work path to relinquish. -/
theorem exhaustedMmaIdleNext {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} (hg : g < l.threads) {t : TState}
    (ht : At t 2039 [(7200, b32 (g / l.block + 1)), (1072, b32 (g / l.block)),
      (7199, b32 p.batch), (7203, b32 p.batch), (2535, b32 l.sharedBase)]) :
    ∃ u, u.pc = 2763 ∧ Next kernel Assumptions.all l g t u
      (.tc (.resource .one none .relinquish) (next u)) := by
  have hCta : g / l.block + 1 < 2 ^ 31 := by
    have := NamedBar.cta_lt hg
    have := hp.grid.2.2
    omega
  have hInputs : At t 2039 [(7200, b32 (g / l.block + 1)), (1072, b32 (g / l.block)),
      (7199, b32 p.batch), (7203, b32 p.batch)] := by at_select ht
  obtain ⟨b,hb,hB⟩ := exhaustedFallback (g := g) hCta t hInputs
  have hFallback := localRun (by decide) (by decide) hInputs.1 (by
    set_option maxRecDepth 100000 in kernel_rfl) hb
  obtain ⟨c,hc',hC⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
    Flow.code_2041 false hB hB.2.2.2.2.1 (by simp)
  have hFall := localRun (by decide) (by decide) hB.1 rfl hc'
  have hC' : At c 2042 [(7199,b32 p.batch),(7203,b32 p.batch)] :=
    hC.mono hC.2.2.2.2.2
  obtain ⟨d,hd,hD⟩ := exhaustedEnterTail (g := g) hp.shape.2.1 c hC'
  have hTail := localRun (by decide) (by decide) hC'.1 (by
    set_option maxRecDepth 100000 in kernel_rfl) hd
  obtain ⟨f,hf,hF⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
    Flow.code_2045 true hD hD.2.2.2.2.1 (by simp)
  have hNoWork := localRun (by decide) (by decide) hD.1 rfl hf
  have hBase : f.regs 2535 = some (b32 l.sharedBase) := by
    have transport {x y : TState} {pc len : Nat}
        (hx : x.pc = pc)
        (hW : ((kernel.code.drop pc).take len).all
          (fun ins => !(writesRegs ins.op).contains 2535) = true)
        (hSeq : ((kernel.code.drop pc).take (len-1)).all
          (fun ins => schedulerFallsThrough ins.op) = true)
        (hr : run kernel [] l g len x = some y) : y.regs 2535 = x.regs 2535 :=
      schedulerLocalFrame (regs := [2535]) (by simpa using hW) hSeq
        hr hx.ge (by rw [hx]) (by decide)
    have hd' := transport hInputs.1 (len := 3) (by set_option maxRecDepth 100000 in kernel_rfl)
      (by set_option maxRecDepth 100000 in kernel_rfl) (run_comp hb hc')
    have hf' := transport hC'.1 (len := 4) (by set_option maxRecDepth 100000 in kernel_rfl)
      (by set_option maxRecDepth 100000 in kernel_rfl) (run_comp hd hf)
    exact hf'.trans (hd'.trans (holds_lookup ht.2.2.2.2 rfl))
  have hF' : At f 2106 [(2535,b32 l.sharedBase),(781,.pred false)] :=
    hF.mono ⟨hBase,hF.2.2.2.2.2.1,trivial⟩
  obtain ⟨v,hv,hV⟩ := emptyWorkGate hp (g := g) f hF'
  have hEmpty := localRun (by decide) (by decide) hF'.1 (by
    set_option maxRecDepth 100000 in kernel_rfl) hv
  obtain ⟨u,hu,hU⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
    Flow.code_2108 true hV hV.2.2.2.2.1 (by simp)
  have hExit := localRun (by decide) (by decide) hV.1 rfl hu
  have hOut : out kernel Assumptions.all l g u =
      .ev (.tc (.resource .one none .relinquish) (next u)) := by
    have hBlock : l.block % 32 = 0 := by rw [hp.block]
    rw [out_eq_core (by rw [hU.1]; decide) (by rw [hU.1]; decide),
      out_event hU.2.2.2.1 (by rw [hU.1]; exact Flow.code_2763) rfl rfl]
    simp [eventTmpl, tcTmpl, hBlock, next, pure, Except.pure, ofExec]
  refine ⟨u,hU.1,?_,hOut⟩
  exact ((((run_rtg hFallback).trans (run_rtg hFall)).trans (run_rtg hTail)).trans
    (run_rtg hNoWork)).trans
    ((run_rtg hEmpty).trans (run_rtg hExit))

/-- When the first group exhausts the batch, a CTA above its cutoff takes the
no-work route straight to the allocator relinquish event. -/
theorem firstGroupIdleNext {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} (hg : g < l.threads) (hBatch : p.batch ≤ 31) {t : TState} :
    At t 1985 [(1072,b32 (g/l.block)),(7203,b32 p.batch),
      (7200,b32 (tilePrefix p p.batch * p.heads)), (2535,b32 l.sharedBase)] →
    ∃ u, u.pc = 2763 ∧ Next kernel Assumptions.all l g t u
      (.tc (.resource .one none .relinquish) (next u)) := by
  intro ht
  have hc : g / l.block < l.grid := NamedBar.cta_lt hg
  have hCta : g / l.block + 1 < 2 ^ 31 := by have := hp.grid.2.2; omega
  obtain ⟨s,hs,hS⟩ := idleAfterFirstGroup (g := g) hCta hBatch t
    (ht.mono ⟨ht.2.2.2.2.1, ht.2.2.2.2.2.1, ht.2.2.2.2.2.2.1, trivial⟩)
  have hPath := localRun (by decide) (by decide) ht.1 (by
    set_option maxRecDepth 100000 in kernel_rfl) hs
  obtain ⟨a,ha,hA⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
    Flow.code_1992 true hS hS.2.2.2.2.1 (by simp)
  have hBranch := localRun (by decide) (by decide) hS.1 rfl ha
  have hBase : a.regs 2535 = some (b32 l.sharedBase) :=
    (schedulerLocalFrame (lo := 1985) (len := 8) (regs := [2535]) (by decide +kernel)
      (by decide +kernel) (run_comp hs ha) ht.1.ge (by rw [ht.1]) (by decide)).trans
      (holds_lookup ht.2.2.2.2 rfl)
  have hAt : At a 2039 [(7200, b32 (g / l.block + 1)), (1072, b32 (g / l.block)),
      (7199, b32 p.batch), (7203, b32 p.batch), (2535, b32 l.sharedBase)] :=
    hA.mono ⟨hA.2.2.2.2.2.1, hA.2.2.2.2.2.2.2.1, hA.2.2.2.2.2.2.1,
      hA.2.2.2.2.2.2.2.2.1, hBase, trivial⟩
  obtain ⟨u, hPc, hNext⟩ := exhaustedMmaIdleNext hp hg hAt
  exact ⟨u, hPc, ((run_rtg hPath).trans (run_rtg hBranch)).trans hNext.steps, hNext.stop⟩

/-- A padded CTA whose search visited later groups reaches the same relinquish boundary. -/
theorem laterGroupIdleNextOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) (hw : warpIndex l g = 12)
    (hProtected : DrainCuQProtected p X) (hBatch : 31 < p.batch)
    (hIdle : tilePrefix p p.batch * p.heads ≤ g / l.block) :
    let group := (p.batch - 1) / 31
    let first := 31 * group
    ∃ c : FallbackScanCursor l X g 1988 (11 + 7 * group) (mmaFallbackBackedgeFacts p l g first),
      ∃ u, u.pc = 2763 ∧ Next kernel Assumptions.all l g c.before u
        (.tc (.resource .one none .relinquish) (next u)) := by
  let group := (p.batch - 1) / 31
  let first := 31 * group
  have hPart : (p.batch - 1) % 31 + first = p.batch - 1 := Nat.mod_add_div _ _
  have hRest : (p.batch - 1) % 31 < 31 := Nat.mod_lt _ (by decide)
  have hSize := hp.shape.2.2.2.2.2
  have hAdvance : first + 31 < 2 ^ 31 := by omega
  have hLast : p.batch ≤ first + 31 := by omega
  obtain ⟨c⟩ := idleFinalMmaGroupOfMaximal hp hMax hg hw hProtected hBatch hIdle
  let F := (7194, b32 (mmaFallbackCutoff p first)) :: fallbackAbi p l g
  have hAt : At c.state 1988 (groupScanFacts .select first p.batch (g / l.block) ++ F) :=
    c.checkpoint
  have hFrame : ((kernel.code.drop 1988).take 5).all
      (fun i => [7194, 1180, 7139, 2535, 7502, 7506, 7503].all
        (fun r => !(writesRegs i.op).contains r)) = true := by decide +kernel
  obtain ⟨v, hv, hV⟩ := advanceGroupScanPreserving (F := F) .select hAdvance hp.shape.2.1 hFrame hAt
  simp only [ite_eq_left hLast, Nat.min_eq_right hLast, scanSite] at hV
  obtain ⟨u, hPc, hNext⟩ := exhaustedMmaIdleNext hp hg (by at_select hV)
  exact ⟨c, u, hPc, (c.localSteps.trans (run_rtg hv)).trans hNext.steps, hNext.stop⟩

private theorem initialSchedulerReg {l : Launch} {g r : Nat} {s u : TState} {es : List Event}
    (hr : r ∈ [7203, 2535])
    (hReach : TraceReach kernel Assumptions.all l g s es u)
    (hLo : 1912 ≤ s.pc) (hEnd : u.pc < 1985) : u.regs r = s.regs r := by
  have hLocal {a b : TState} {ev : Option Event}
      (hStart : 1912 ≤ a.pc) (hStop : a.pc < 1985)
      (hStep : WStep kernel Assumptions.all l g a ev b) : b.regs r = a.regs r := by
    apply mmaStepReg (by omega) (by omega) _ hStep
    intro ins hCode
    have hTab : ((kernel.code.drop 1912).take (1985-1912)).all
        (fun i => [7203,2535].all (fun r => !(mmaWrites i.op).contains r)) = true := by
      set_option maxRecDepth 100000 in kernel_rfl
    have hIndex : a.pc - 1912 < 73 := by omega
    have hEntry : ((kernel.code.drop 1912).take 73)[a.pc-1912]? = some ins := by
      rw [List.getElem?_take_of_lt hIndex, List.getElem?_drop, Nat.add_sub_of_le hStart]
      exact hCode
    have hStable := List.all_eq_true.mp hTab ins (List.mem_of_getElem? hEntry)
    simpa using List.all_eq_true.mp hStable r hr
  induction hReach with
  | refl => rfl
  | @tau s v u es hTau hRest ih =>
    have hHi : s.pc < 1985 := by
      by_contra! h
      exact (Nat.not_le_of_lt hEnd) (resourceSuffixFloor .firstGroup (.tau hTau hRest) h)
    have hV : 1912 ≤ v.pc :=
      resourceSuffixFloor .allocationRead (.tau hTau (.refl _)) hLo
    exact (ih hV hEnd).trans (hLocal hLo hHi (.inl ⟨rfl,hTau⟩))
  | @event s v u es e hEvent hRest ih =>
    have hHi : s.pc < 1985 := by
      by_contra! h
      exact (Nat.not_le_of_lt hEnd) (resourceSuffixFloor .firstGroup (.event hEvent hRest) h)
    have hV : 1912 ≤ v.pc :=
      resourceSuffixFloor .allocationRead (.event hEvent (.refl _)) hLo
    exact (ih hV hEnd).trans (hLocal hLo hHi (.inr ⟨_,rfl,hEvent⟩))

private theorem selectedGroupFloor {l : Launch} {g : Nat} {s u : TState}
    {events : List Event} (hTrace : TraceReach kernel Assumptions.all l g s events u)
    (hFloor : 2042 ≤ s.pc) : 2042 ≤ u.pc := by
  have hCode : (kernel.code.drop 2042).all
      (fun i => Thread.staysPastEvent 2042 i.op) = true := by decide +kernel
  have hSegments : Assumptions.swExp2Sites.all (fun site => match cuteExp2.matchAt kernel site with
      | some seg => decide (2042 ≤ seg.stop)
      | none => false) = true := by decide +kernel
  induction hTrace with
  | refl => exact hFloor
  | tau ht _ ih => exact ih (Thread.eventTailStepOfAudit hCode hSegments hFloor (.inl ⟨rfl, ht⟩))
  | event he _ ih =>
    exact ih (Thread.eventTailStepOfAudit hCode hSegments hFloor (.inr ⟨_, rfl, he⟩))

private theorem initialSchedulerNoCollective {l : Launch} {g : Nat} {s u : TState}
    {es : List Event} (hReach : TraceReach kernel Assumptions.all l g s es u)
    (hLo : 1910 ≤ s.pc) (hEnd : u.pc < 2042) : es.countP isTcColl = 0 := by
  induction hReach with
  | refl => rfl
  | @tau s v u es hTau hRest ih =>
    have hV : 1910 ≤ v.pc :=
      resourceSuffixFloor .allocation (.tau hTau (.refl _)) hLo
    exact ih hV hEnd
  | @event s v u es e hEvent hRest ih =>
    have hHi : s.pc < 2042 := by
      by_contra! h
      exact (Nat.not_le_of_lt hEnd) (selectedGroupFloor (.event hEvent hRest) h)
    have hV : 1910 ≤ v.pc :=
      resourceSuffixFloor .allocation (.event hEvent (.refl _)) hLo
    obtain ⟨ins, hCode, _, hFire⟩ := EventFrame.estep_event_source hEvent
    have hTab : ((kernel.code.drop 1910).take (2042 - 1910)).all
        (fun i => !(tcAnyOp i.op)) = true := by decide +kernel
    have hIndex : s.pc - 1910 < 2042 - 1910 := by omega
    have hGet : ((kernel.code.drop 1910).take (2042 - 1910))[s.pc - 1910]? = some ins := by
      rw [List.getElem?_take_of_lt hIndex, List.getElem?_drop, Nat.add_sub_of_le hLo]
      exact hCode
    have hNot : tcAnyOp ins.op = false := by
      have h := List.all_eq_true.mp hTab ins (List.mem_of_getElem? hGet)
      simp only [Bool.not_eq_true'] at h
      exact h
    have hCount : isTcColl e = false := by
      have hNone := fires_notTc hNot hFire
      rcases e with ⟨pc,kind⟩
      cases kind <;> first | rfl | exact (hNone _ rfl).elim
    simp [hCount, ih hV hEnd]

private theorem beforeGroupEvents {l : Launch} {g floor : Nat} {t u : TState}
    (advance : ∀ {a b : TState} {es}, TraceReach kernel Assumptions.all l g a es b →
      floor ≤ a.pc → floor ≤ b.pc)
    {events : List Event} (hReach : TraceReach kernel Assumptions.all l g t events u)
    (hEnd : u.pc < floor) : ∀ e ∈ events, e.pc < floor := by
  induction hReach with
  | refl => simp
  | tau _ _ ih => exact ih hEnd
  | @event s v u es e he hRest ih =>
    intro e' hMem
    rcases List.mem_cons.mp hMem with rfl | hTail
    · by_contra! hHigh
      have hPc := EventFrame.estep_source_pc he
      have hFloor := advance (.event he hRest) (hPc ▸ hHigh)
      exact (Nat.not_le_of_lt hEnd) hFloor
    · exact ih hEnd _ hTail

/-- A ready allocator cursor reaches its real Tensor Memory relinquish event. -/
theorem relinquishAtCursor {l : Launch} {m : Mem0} {X : Execution}
    (hMax : Maximal l kernel Assumptions.all m X) {g pos : Nat} (hg : g < l.threads)
    {t w : TState} {o : Option TState} (hPos : 0 < pos) (hBound : pos ≤ (X.tr g).length)
    (hRelease : pos = (X.tr g).length → Step.Released l X g)
    (hPc : w.pc = 2763)
    (hNext : Next kernel Assumptions.all l g t w (.tc (.resource .one none .relinquish) (next w)))
    (hPastPrefix : Run kernel Assumptions.all l g {} ((X.tr g).take pos) (some t))
    (hTail : Run kernel Assumptions.all l g t ((X.tr g).drop pos) o) :
    X.get (g,pos) = some ⟨2763,.tc (.resource .one none .relinquish)⟩ ∧ w.fault = none ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take (pos+1)) (some (next w)) ∧
      Run kernel Assumptions.all l g (next w) ((X.tr g).drop (pos+1)) o := by
  have hLt : pos < (X.tr g).length := by
    by_contra! hLow
    have hLen : pos = (X.tr g).length := hBound.antisymm hLow
    have hStarted : X.tr g ≠ [] := List.ne_nil_of_length_pos (hPos.trans_le hBound)
    have hPrefix : Run kernel Assumptions.all l g {} (X.tr g) (some t) := by
      simpa [List.take_of_length_le hLow] using hPastPrefix
    exact hMax.not_grows (Step.tccoll_counted_extension hMax.1 hg (.inl hStarted) (hRelease hLen)
      hPrefix hNext.steps ⟨_,hNext.stop,rfl,rfl⟩ rfl
      (hMax.1.tmemPairResult.snoc_not_wr nofun) (hMax.1.tcRead_snoc_tc nofun)
      (Assumptions.wfStep.quiet hMax.1 le_snoc rfl (Execution.noNewRead_snoc rfl)))
  obtain ⟨_, _, hGet, ⟨rfl, hOut⟩, hRest⟩ := hNext.continuing_at_nonempty
    (by rintro _ ⟨_, h⟩; cases h) hTail
    (fun hNil => (Nat.not_le_of_lt hLt) (List.drop_eq_nil_iff.mp hNil))
  obtain rfl := Option.some.inj hOut
  have hEvent : X.get (g,pos) = some ⟨2763,.tc (.resource .one none .relinquish)⟩ := hPc ▸ hGet
  have hPast : Run kernel Assumptions.all l g {} ((X.tr g).take (pos+1)) (some (next w)) := by
    rw [List.take_succ_eq_append_getElem hLt]
    have hEq : (X.tr g)[pos] = ⟨w.pc,.tc (.resource .one none .relinquish)⟩ := by
      change (X.tr g)[pos]? = _ at hGet
      rwa [List.getElem?_eq_getElem hLt, Option.some.injEq] at hGet
    rw [hEq]
    exact hPastPrefix.snoc hNext.steps ⟨_,hNext.stop,rfl,rfl⟩
  have hFault : w.fault = none := by
    cases hf : w.fault with
    | none => rfl
    | some f =>
      have hStep := hNext.stop
      rw [out, hf] at hStep
      cases hStep
  exact ⟨hEvent,hFault,hPast,hRest⟩

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g : Nat} (hg : g < l.threads)
    (hw : warpIndex l g = 12)
include hp hMax hg hw

private theorem idleMmaRelinquishWithExclusion (hProtected : DrainCuQProtected p X)
    (hBatch : p.batch ≤ 31) (hIdle : tilePrefix p p.batch * p.heads ≤ g / l.block) :
    ∃ j v o, X.get (g,j) = some ⟨2763,.tc (.resource .one none .relinquish)⟩ ∧
      X.TcK (g,j) 1 ∧ v.pc = 2764 ∧ v.fault = none ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take (j+1)) (some v) ∧
      Run kernel Assumptions.all l g v ((X.tr g).drop (j+1)) o ∧
      (∀ k e, X.get (g,k) = some e → 1985 ≤ e.pc → e.pc < 2763 → False) := by
  obtain ⟨j, e, t, o, he, hSite, hKind, ht, hPrefix, hTail⟩ :=
    Allocation.firstGroupScanTotalWithSite hp hMax hg hw hProtected
  obtain ⟨u, _, _, _, hU, hStart, _⟩ := schedulerAbiAtDescriptor hp hMax hg hw
  have hLate : 1911 < e.pc := by rw [hSite]; decide
  have hGood : ∀ f, e.kind ≠ .ub f := by rw [hKind]; intro f h; cases h
  obtain ⟨_, _, _, _, hDescLe, _, _, _, _⟩ :=
    descriptorSendBeforeEvent hp hMax.1 he hw hLate hGood
  have hCut : (((X.tr g).take (j+1)).take (descriptorShufflePos (laneOf l g)+1)) =
      (X.tr g).take (descriptorShufflePos (laneOf l g)+1) := by
    rw [List.take_take, Nat.min_eq_left (by omega)]
  have hPrefix' := hPrefix
  rw [← List.take_append_drop (descriptorShufflePos (laneOf l g)+1) ((X.tr g).take (j+1)),
    hCut] at hPrefix'
  have hSegment := hStart.after_returned_prefix hPrefix'
  have hFrame {r : Nat} (hr : r ∈ [7203,2535]) : t.regs r = u.regs r :=
    initialSchedulerReg hr hSegment.returning_reach (by rw [hU.1]; decide) (by rw [ht.1]; decide)
  have hCta : g / l.block < 2^31 := (NamedBar.cta_lt hg).trans hp.grid.2.2
  have ht' : At t 1981 [(7198,b32 (tilePrefix p (min p.batch 31))),
      (7139,b32 p.heads),(1072,b32 (g/l.block))] :=
    ht.mono ⟨ht.2.2.2.2.1,ht.2.2.2.2.2.2.2.1,ht.2.2.2.2.2.2.2.2.1,trivial⟩
  have hTcCount : ((X.tr g).take (j+1)).countP isTcColl = 1 := by
    obtain ⟨k, a, _, hK, _, _, hAt, hAlloc, _⟩ :=
      allocatorRendezvousPrefix hp hMax hg hw
    have hDesc : allocationBarrierPos l g + 2 = descriptorShufflePos (laneOf l g) := by
      unfold allocationBarrierPos descriptorShufflePos
      split <;> decide
    have hLe : k+1 ≤ j+1 := by omega
    have hTake : (((X.tr g).take (j+1)).take (k+1)) = (X.tr g).take (k+1) := by
      rw [List.take_take, Nat.min_eq_left hLe]
    have hSplit : (X.tr g).take (k+1) ++ ((X.tr g).take (j+1)).drop (k+1) =
        (X.tr g).take (j+1) := by rw [← hTake, List.take_append_drop]
    have hSuffix := hAlloc.after_returned_prefix (hSplit.symm ▸ hPrefix)
    have hNone := initialSchedulerNoCollective hSuffix.returning_reach
      (by rw [hAt.1]; decide) (by rw [ht.1]; decide)
    rw [← hSplit, List.countP_append, hNone, hK]
    simpa using allocatorRendezvousCollectiveCount hp hMax hg hw
  obtain ⟨v, hRun, hv, hKeep⟩ := firstGroupRouteWithFrame hp g hCta ht'
  have hLimit : min p.batch 31 = p.batch := Nat.min_eq_left hBatch
  simp only [hLimit, ite_eq_right (Nat.not_lt_of_ge hIdle)] at hv
  have hRegCta := (hKeep 1072 (by decide)).trans ht'.2.2.2.2.2.2.1
  have hRegBatch : v.regs 7203 = some (b32 p.batch) :=
    (hKeep 7203 (by decide)).trans ((hFrame (by decide)).trans
      (holds_mem hU.2.2.2.2 (by simp [entryFacts])))
  have hRegBase : v.regs 2535 = some (b32 l.sharedBase) :=
    (hKeep 2535 (by decide)).trans ((hFrame (by decide)).trans
      (holds_mem hU.2.2.2.2 (by simp [entryFacts,startupFacts])))
  have hV : At v 1985 [(1072,b32 (g/l.block)),(7203,b32 p.batch),
      (7200,b32 (tilePrefix p p.batch * p.heads)),(2535,b32 l.sharedBase)] :=
    hv.mono ⟨hRegCta,hRegBatch,hv.2.2.2.2.1,hRegBase,trivial⟩
  obtain ⟨w, hPc, hn⟩ := firstGroupIdleNext hp hg hBatch hV
  have hNext : Next kernel Assumptions.all l g t w
      (.tc (.resource .one none .relinquish) (next w)) :=
    ⟨(run_rtg hRun).trans hn.steps, hn.stop⟩
  have hRelease := releasedIfLast (l := l) he (by rw [hKind]; intro h; cases h)
  obtain ⟨hEvent,hFault,hPast,hRest⟩ := relinquishAtCursor hMax hg (Nat.succ_pos j)
    (len_of_get he) hRelease hPc hNext hPrefix hTail
  have hNo (k : Nat) (ev : Event) (he' : X.get (g,k) = some ev)
      (hLo : 1985 ≤ ev.pc) (hHi : ev.pc < 2763) : False := by
    rcases lt_trichotomy k (j+1) with hLt' | hEq | hGt
    · have hGet' : ((X.tr g).take (j+1))[k]? = some ev := by
        rw [List.getElem?_take_of_lt hLt']
        exact he'
      have hMem := List.mem_of_getElem? hGet'
      have hEarly := beforeGroupEvents (resourceSuffixFloor .firstGroup) hPrefix.returning_reach
        (show t.pc < 1985 by rw [ht.1]; decide) ev hMem
      change ev.pc < 1985 at hEarly
      omega
    · rw [hEq,hEvent] at he'
      obtain rfl := Option.some.inj he'
      exact (Nat.lt_irrefl _) hHi
    · have hGet' : ((X.tr g).drop (j+1+1))[k-(j+1+1)]? = some ev := by
        rw [List.getElem?_drop, Nat.add_sub_of_le (by omega : j+1+1 ≤ k)]
        exact he'
      obtain ⟨v,_,hReach,hStep⟩ := hRest.before_event hGet'
      have hNextPc : (next w).pc = 2764 := by change w.pc+1=2764; rw [hPc]
      have hLow := resourceSuffixFloor .relinquish hReach hNextPc.ge
      have hEq := EventFrame.estep_source_pc hStep
      change 2764 ≤ v.pc at hLow
      omega
  exact ⟨j+1,next w,o,hEvent,⟨⟨_,hEvent,rfl⟩,hTcCount⟩,
    by change w.pc+1=2764; rw [hPc],hFault,hPast,hRest,hNo⟩

/-- Replay the idle CTA through its second Tensor Memory collective. -/
theorem idleMmaRelinquishPrefix (hProtected : DrainCuQProtected p X) (hBatch : p.batch ≤ 31)
    (hIdle : tilePrefix p p.batch * p.heads ≤ g / l.block) :
    ∃ j v o, X.get (g,j) = some ⟨2763,.tc (.resource .one none .relinquish)⟩ ∧
      X.TcK (g,j) 1 ∧ v.pc = 2764 ∧ v.fault = none ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take (j+1)) (some v) ∧
      Run kernel Assumptions.all l g v ((X.tr g).drop (j+1)) o := by
  obtain ⟨j,t,o,he,hTc,hPc,hFault,hPrefix,hTail,_⟩ :=
    idleMmaRelinquishWithExclusion hp hMax hg hw hProtected hBatch hIdle
  exact ⟨j,t,o,he,hTc,hPc,hFault,hPrefix,hTail⟩

/-- The padded CTA records relinquish after all fallback groups have been scanned. -/
private theorem laterIdleMmaRelinquishWithExclusion (hProtected : DrainCuQProtected p X)
    (hBatch : 31 < p.batch) (hIdle : tilePrefix p p.batch * p.heads ≤ g / l.block) :
    ∃ j v o, X.get (g,j) = some ⟨2763,.tc (.resource .one none .relinquish)⟩ ∧
      X.TcK (g,j) 1 ∧ v.pc = 2764 ∧ v.fault = none ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take (j+1)) (some v) ∧
      Run kernel Assumptions.all l g v ((X.tr g).drop (j+1)) o ∧
      (∀ k e, X.get (g,k) = some e → 2042 ≤ e.pc → e.pc < 2763 → False) := by
  obtain ⟨c, w, hPc, hNext⟩ :=
    laterGroupIdleNextOfMaximal hp hMax hg hw hProtected hBatch hIdle
  obtain ⟨k, _, _, hK, _, _, hAt, hAlloc, _⟩ := allocatorRendezvousPrefix hp hMax hg hw
  have hBefore : c.before.pc < 2042 := by
    by_contra! h
    have hEnd := selectedGroupFloor (TraceReach.of_local c.localSteps) h
    rw [c.checkpoint.1] at hEnd
    omega
  have hKBound : k + 1 ≤ 9 := by
    rw [hK, allocationBarrierPos]
    split <;> decide
  have hPos : 11 ≤ c.pos :=
    (Nat.le_add_right 11 _).trans (c.shuffleCount.ge.trans
      ((List.countP_le_length ..).trans (List.length_take_le ..)))
  have hTake : (((X.tr g).take c.pos).take (k+1)) = (X.tr g).take (k+1) := by
    rw [List.take_take, Nat.min_eq_left (by omega)]
  have hSplit : (X.tr g).take (k+1) ++ ((X.tr g).take c.pos).drop (k+1) =
      (X.tr g).take c.pos := by rw [← hTake, List.take_append_drop]
  have hSuffix := hAlloc.after_returned_prefix (hSplit.symm ▸ c.runPrefix)
  have hNone := initialSchedulerNoCollective hSuffix.returning_reach
    (by rw [hAt.1]; decide) hBefore
  have hTcCount : ((X.tr g).take c.pos).countP isTcColl = 1 := by
    rw [← hSplit, List.countP_append, hNone, hK]
    simpa using allocatorRendezvousCollectiveCount hp hMax hg hw
  obtain ⟨hEvent,hFault,hPast,hRest⟩ := relinquishAtCursor hMax hg
    c.pos_pos c.pos_le c.released hPc hNext c.runPrefix c.continuation
  have hNo (k : Nat) (e : Event) (he : X.get (g,k) = some e)
      (hLo : 2042 ≤ e.pc) (hHi : e.pc < 2763) : False := by
    rcases lt_trichotomy k c.pos with hPrev | hEq | hAfter
    · have hGet : ((X.tr g).take c.pos)[k]? = some e := by
        rw [List.getElem?_take_of_lt hPrev]
        exact he
      have hEarly := beforeGroupEvents selectedGroupFloor c.runPrefix.returning_reach
        hBefore e (List.mem_of_getElem? hGet)
      omega
    · rw [hEq, hEvent] at he
      obtain rfl := Option.some.inj he
      exact (Nat.lt_irrefl _) hHi
    · have hGet : ((X.tr g).drop (c.pos+1))[k-(c.pos+1)]? = some e := by
        rw [List.getElem?_drop, Nat.add_sub_of_le (by omega : c.pos+1 ≤ k)]
        exact he
      obtain ⟨v, _, hReach, hStep⟩ := hRest.before_event hGet
      have hNextPc : (next w).pc = 2764 := by change w.pc+1=2764; rw [hPc]
      have hLater := resourceSuffixFloor .relinquish hReach hNextPc.ge
      have hEventPc := EventFrame.estep_source_pc hStep
      change 2764 ≤ v.pc at hLater
      omega
  exact ⟨c.pos, next w, c.lastState, hEvent, ⟨⟨_,hEvent,rfl⟩,hTcCount⟩,
    by change w.pc+1=2764; rw [hPc], hFault, hPast, hRest, hNo⟩

/-- Every idle MMA warp records the relinquish collective after exhausting its scheduler. -/
theorem idleMmaRelinquishPrefixOfMaximal (hProtected : DrainCuQProtected p X)
    (hIdle : tilePrefix p p.batch * p.heads ≤ g / l.block) :
    ∃ j v o, X.get (g,j) = some ⟨2763,.tc (.resource .one none .relinquish)⟩ ∧
      X.TcK (g,j) 1 ∧ v.pc = 2764 ∧ v.fault = none ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take (j+1)) (some v) ∧
      Run kernel Assumptions.all l g v ((X.tr g).drop (j+1)) o := by
  by_cases hBatch : p.batch ≤ 31
  · exact idleMmaRelinquishPrefix hp hMax hg hw hProtected hBatch hIdle
  · obtain ⟨j,v,o,he,hK,hPc,hFault,hRun,hTail,_⟩ :=
      laterIdleMmaRelinquishWithExclusion hp hMax hg hw hProtected (by omega) hIdle
    exact ⟨j,v,o,he,hK,hPc,hFault,hRun,hTail⟩

/-- The actual MMA lane of a short idle CTA skips the entire allocated work body. -/
theorem idleMmaNoWorkEvent (hCuQ : DrainCuQProtected p X) (hBatch : p.batch ≤ 31)
    (hIdle : tilePrefix p p.batch * p.heads ≤ g / l.block) {j : Nat} {e : Event}
    (he : X.get (g,j) = some e) (hLo : 1985 ≤ e.pc) (hHi : e.pc < 2763) : False := by
  obtain ⟨_,_,_,_,_,_,_,_,_,hNo⟩ :=
    idleMmaRelinquishWithExclusion hp hMax hg hw hCuQ hBatch hIdle
  exact hNo _ e he hLo hHi

/-- An idle MMA lane performs no selected tile work, even after scanning later groups. -/
theorem idleMmaNoTileWorkEvent (hProtected : DrainCuQProtected p X)
    (hIdle : tilePrefix p p.batch * p.heads ≤ g / l.block) {j : Nat} {e : Event}
    (he : X.get (g,j) = some e) (hLo : 2042 ≤ e.pc) (hHi : e.pc < 2763) : False := by
  by_cases hBatch : p.batch ≤ 31
  · exact idleMmaNoWorkEvent hp hMax hg hw hProtected hBatch hIdle he (by omega) hHi
  · obtain ⟨_,_,_,_,_,_,_,_,_,hNo⟩ :=
      laterIdleMmaRelinquishWithExclusion hp hMax hg hw hProtected (by omega) hIdle
    exact hNo _ _ he hLo hHi

end
end PTX.Kernels.TmlFa4Fwd.Mma
