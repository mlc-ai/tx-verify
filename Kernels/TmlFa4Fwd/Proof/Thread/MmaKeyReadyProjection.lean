-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaCacheBroadcasts
import Kernels.TmlFa4Fwd.Proof.Thread.MmaValueSender
import Lemmas.Flow.Final
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
import Kernels.TmlFa4Fwd.Proof.MmaWholePrefix
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaReadyTraversal
import Kernels.TmlFa4Fwd.Proof.Thread.MmaReadyShuffleAlignment
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaReleaseOrdinal
import Kernels.TmlFa4Fwd.Flow.Code.Part036

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Flow PTX.Proof PTX.EventFrame PTX.Assumption
open PTX.Kernels.TmlFa4Fwd.Mma

noncomputable section

private def keyStation : Nat := 2361

private def keyReadyMark (e : Event) : Option Event :=
  if e.pc = keyStation ∨ (readyEvent e).isSome then some e else none

private def keyDescriptorEvent (l : Launch) (slot : Fin 3) (e : Event) : Prop :=
  ∃ recv ok, e = ⟨keyStation,.shfl .idx (b32 (keyDescriptorLow l slot.val)) 0 31 recv ok⟩

private def keyCalls (events : List Event) : Nat :=
  events.countP (readyAtSite 2)

private theorem keyCallsAppend (a b : List Event) : keyCalls (a++b) = keyCalls a + keyCalls b :=
  List.countP_append

/-- A prefix without successful cache-ready events has no recurring key acquire. -/
theorem recurringKeyPollCountErased {events : List Event}
    (hReady : events.filterMap readyEvent = []) : events.countP (readyAtSite 2) = 0 := by
  apply List.countP_eq_zero.mpr
  intro event hm hmKey
  obtain ⟨pc,kind⟩ := event
  cases kind <;> simp only [readyAtSite,Bool.false_eq_true] at hmKey
  case wait loc phase success acquire scope =>
    cases success
    · cases hmKey
    · have hPc := beq_iff_eq.mp hmKey
      change pc = 2352 at hPc
      subst pc
      have hNone := List.filterMap_eq_nil_iff.mp hReady _ hm
      have hSuccess : readyEvent ⟨2352,.wait loc phase true acquire scope⟩ =
          some (loc,phase) := by rfl
      rw [hSuccess] at hNone
      cases hNone

private theorem keyCallsOfNoReady {events : List Event}
    (hReady : events.filterMap readyEvent = []) : keyCalls events = 0 :=
  recurringKeyPollCountErased hReady

private def KeyReadyTrace (l : Launch) (use rank : Nat) (events : List Event) : Prop :=
  ∀ pre e tail, events = pre ++ e :: tail → e.pc = keyStation →
    keyDescriptorEvent l (readyStage (use + (pre.filterMap readyEvent).length - 1)) e ∧
      (use + (pre.filterMap readyEvent).length - 1) % 2 = 0 ∧
      2 ≤ use + (pre.filterMap readyEvent).length - 1 ∧
      use + (pre.filterMap readyEvent).length - 1 = 2 * (rank + keyCalls pre)

private theorem keyTraceAppend {l : Launch} {use rank : Nat} {a b : List Event}
    (hA : ∀ e ∈ a, e.pc ≠ keyStation)
    (hB : KeyReadyTrace l (use + (a.filterMap readyEvent).length) (rank + keyCalls a) b) :
    KeyReadyTrace l use rank (a++b) := by
  induction a generalizing use rank with
  | nil => simpa [keyCalls] using hB
  | cons x xs ih =>
    intro pre e tail hTrace hKey
    cases pre with
    | nil =>
      simp only [List.nil_append,List.cons_append,List.cons.injEq] at hTrace
      exact (hA x (by simp) (hTrace.1 ▸ hKey)).elim
    | cons y ys =>
      simp only [List.cons_append,List.cons.injEq] at hTrace
      obtain ⟨rfl,hRest⟩ := hTrace
      have hCons (rest : List Event) : ((x :: rest).filterMap readyEvent).length =
          ([x].filterMap readyEvent).length + (rest.filterMap readyEvent).length := by
        rw [show x :: rest = [x] ++ rest from rfl,List.filterMap_append,List.length_append]
      have hRank (rest : List Event) : keyCalls (x::rest) = keyCalls [x] + keyCalls rest :=
        keyCallsAppend [x] rest
      rw [hCons xs, hRank xs, ← Nat.add_assoc, ← Nat.add_assoc] at hB
      have hc := ih (fun f hf => hA f (List.mem_cons_of_mem _ hf)) hB ys e tail hRest hKey
      rw [hCons ys, hRank ys, ← Nat.add_assoc, ← Nat.add_assoc]
      exact hc

private theorem noReadyOrKeyOfEmpty {events : List Event}
    (h : events.filterMap keyReadyMark = []) :
    (∀ e ∈ events, e.pc ≠ keyStation) ∧ events.filterMap readyEvent = [] := by
  have hAll := List.filterMap_eq_nil_iff.mp h
  refine ⟨?_,List.filterMap_eq_nil_iff.mpr ?_⟩
  · intro e hm hKey
    simpa [keyReadyMark,hKey] using hAll e hm
  · intro e hm
    cases hr : readyEvent e with
    | none => rfl
    | some ready =>
      have hBad := hAll e hm
      simp [keyReadyMark,hr] at hBad

private theorem keyTraceOfNoKey {l : Launch} {use rank : Nat} {events : List Event}
    (h : ∀ e ∈ events, e.pc ≠ keyStation) : KeyReadyTrace l use rank events := by
  intro pre e tail hList hKey
  exact (h e (hList.symm ▸ List.mem_append_right _ (by simp)) hKey).elim

private theorem emptyKeyTraceOfMark {l : Launch} {use rank : Nat} {events : List Event}
    (h : events.filterMap keyReadyMark = []) : KeyReadyTrace l use rank events :=
  keyTraceOfNoKey (noReadyOrKeyOfEmpty h).1

private theorem atKeyIntervalExit (i : Fin 9) {s : TState}
    {F : List (Nat × Value)} (hp : s.pc ∈ (readyInterval i).exits)
    (hf : s.fault = none) (hs : RoleShape s) (hF : Holds s.regs F) : At s s.pc F := by
  have hNo : ∀ pc ∈ (readyInterval i).exits, pc ≠ 1909 := by
    fin_cases i <;> simp [readyInterval]
  exact ⟨rfl, hs.2.2 (hNo _ hp), hs.2.1, hf, hF⟩

private theorem keyTraceIntervalWith (i : Fin 9) {l : Launch} {g use rank : Nat} {s : TState}
    {F : List (Nat × Value)} {es : List Event} {vs : List Visit}
    (hPc : (readyInterval i).lo ≤ s.pc ∧ s.pc < (readyInterval i).hi)
    (hNo : ∀ pc, (readyInterval i).lo ≤ pc → pc < (readyInterval i).hi → pc ≠ keyStation)
    (hs : At s s.pc F) (hWarp : (1062, b32 12) ∈ F)
    (hKeep : ∀ r ∈ F.map Prod.fst, r = 1062 ∨ r ∈ (readyInterval i).keep)
    (hw : Walk kernel Assumptions.all l g s es vs)
    (after : ∀ {u tail post}, u.pc ∈ (readyInterval i).exits → At u u.pc F →
      post.length < vs.length → Walk kernel Assumptions.all l g u tail post →
      KeyReadyTrace l use rank tail) : KeyReadyTrace l use rank es := by
  have hShape : RoleShape s := ⟨hs.2.1.symm ▸ Nat.zero_le _,hs.2.2.1,fun _ => hs.2.1⟩
  rcases readyIntervalCutWith keyReadyMark i (fun e he => by
    simp [keyReadyMark,hNo _ he.1 he.2,readyEventOutside i he])
    hw hPc ⟨hShape,holds_mem hs.2.2.2.2 hWarp⟩ hs.2.2.2.2 hKeep with h |
      ⟨u,pre,tail,post,hE,hP,hL,hX,hFault,hRole,hF,hWalk⟩
  · exact emptyKeyTraceOfMark h
  · obtain ⟨hKey,hReady⟩ := noReadyOrKeyOfEmpty hP
    rw [hE]
    have hTail := after hX (atKeyIntervalExit i hX hFault hRole.1 hF) hL hWalk
    exact keyTraceAppend hKey (by simpa [hReady,keyCallsOfNoReady hReady] using hTail)

private theorem keyTraceSegment {l : Launch} {g use rank pc nextPc n : Nat} {s : TState}
    {F G : List (Nat × Value)} {es : List Event} {vs : List Visit}
    (hSeg : Seg kernel Assumptions.all l g n pc F nextPc G) (ht : At s pc F)
    (hw : Walk kernel Assumptions.all l g s es vs)
    (after : ∀ {u post}, At u nextPc G → post.length ≤ vs.length →
      Walk kernel Assumptions.all l g u es post → KeyReadyTrace l use rank es) :
    KeyReadyTrace l use rank es := by
  obtain ⟨u,hr,hu⟩ := hSeg s ht
  rcases advanceWalkLocals hr hw with rfl | ⟨post,hLen,_,hWalk⟩
  · exact emptyKeyTraceOfMark rfl
  · exact after hu (by omega) hWalk

private def keyReadyWait : Fin 3 → Fin 14
  | 0 => 1
  | 1 => 3
  | _ => 6

private theorem keyTracePoll {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (i : Fin 3) {g use rank : Nat} {t : TState} {F : List (Nat × Value)}
    {es : List Event} {vs : List Visit}
    (hFresh : ∀ pair ∈ F, pair.1 ≠ (waitSite (keyReadyWait i)).result)
    (hBase : ((waitSite (keyReadyWait i)).base, b32 (readyAddr l use)) ∈ F)
    (hPar : ((waitSite (keyReadyWait i)).phase, b32 (readyWord use)) ∈ F)
    (ht : At t (waitSite (keyReadyWait i)).pc F)
    (hw : Walk kernel Assumptions.all l g t es vs)
    (after : ∀ {u rest post}, post.length < vs.length →
      At u ((waitSite (keyReadyWait i)).pc + 3) F →
      Walk kernel Assumptions.all l g u rest post →
      KeyReadyTrace l (use+1) (rank + if i = 2 then 1 else 0) rest) :
    KeyReadyTrace l use rank es := by
  have hAddr : readyAddr l use < 2 ^ 32 := by
    have h := hp.shared.2.1
    have hSlot := (readyStage use).isLt
    unfold readyAddr
    omega
  have hAlign : readyAddr l use % 8 = 0 := by
    have h := hp.shared.1
    unfold readyAddr
    omega
  let ev := fun ok => Event.mk (waitSite (keyReadyWait i)).pc
    (.wait ⟨.shared, g / l.block, readyAddr l use⟩ (readyWord use) ok true .cta)
  have hKey (ok : Bool) : (ev ok).pc ≠ keyStation := by
    change (waitSite (keyReadyWait i)).pc ≠ keyStation
    fin_cases i <;> decide
  have hSuccess : readyEvent (ev true) =
      some (⟨.shared,g/l.block,readyAddr l use⟩,readyWord use) := by
    have hc : (List.finRange 4).any (fun j => readyHead j == (ev true).pc) = true := by
      change (List.finRange 4).any (fun j => readyHead j == (waitSite (keyReadyWait i)).pc) = true
      fin_cases i <;> decide
    unfold readyEvent
    change (if _ then _ else _) = _
    simp [ev,hc]
  have erase (n : Nat) : (List.replicate n (ev false)).filterMap readyEvent = [] := by
    simp [readyEvent,ev]
  rcases waitWalk (keyReadyWait i) hAddr hAlign (readyWord_lt use) hFresh hBase hPar
      ht hw with ⟨n, hEq⟩ | ⟨n, rest, hEq, hTail⟩
  · change es = List.replicate n (ev false) at hEq
    rw [hEq]
    apply keyTraceOfNoKey
    intro e he
    exact (List.eq_of_mem_replicate he) ▸ hKey false
  · change es = List.replicate n (ev false) ++ ev true :: rest at hEq
    have hOne : ((List.replicate n (ev false) ++ [ev true]).filterMap readyEvent).length = 1 := by
      simp [List.filterMap_append,erase,hSuccess]
    rw [hEq,show ev true :: rest = [ev true] ++ rest from rfl,← List.append_assoc]
    apply keyTraceAppend
    · intro e he
      rcases List.mem_append.mp he with he | he
      · exact (List.eq_of_mem_replicate he) ▸ hKey false
      · exact (List.mem_singleton.mp he).symm ▸ hKey true
    have hKeyCalls : keyCalls (List.replicate n (ev false) ++ [ev true]) =
        if i = 2 then 1 else 0 := by
      rw [keyCallsAppend, keyCallsOfNoReady (erase _), Nat.zero_add]
      fin_cases i <;> rfl
    rw [hOne,hKeyCalls]
    rcases hTail with rfl | ⟨u,post,hL,hu,hWalk⟩
    · exact emptyKeyTraceOfMark rfl
    · exact after hL hu hWalk

set_option maxRecDepth 100000 in
private theorem lateKeyFloor :
    (kernel.code.drop 2534).all (fun i => staysPastEvent 2534 i.op) = true := by kernel_rfl

set_option maxRecDepth 100000 in
private theorem lateKeySegments : Assumptions.swExp2Sites.all (fun site =>
    match cuteExp2.matchAt kernel site with
    | some s => decide (2534 ≤ s.stop)
    | none => false) = true := by kernel_rfl

private theorem noKeyTraceAfter {l : Launch} {g use rank : Nat} {t : TState}
    {es : List Event} {vs : List Visit} (hFloor : 2534 ≤ t.pc)
    (hWalk : Walk kernel Assumptions.all l g t es vs) : KeyReadyTrace l use rank es := by
  apply keyTraceOfNoKey
  intro e he hKey
  have hb := eventTailEvents lateKeyFloor lateKeySegments hWalk hFloor e he
  change e.pc = 2361 at hKey
  omega

private def keyRemainder : ReadyInterval := ⟨2362,2524,[2524],[2535,1192,2572]⟩

set_option maxRecDepth 100000 in
private theorem keyRemainderAudit :
    (((kernel.code.drop 2362).take (2524-2362)).zipIdx 2362).all
      (fun (ins,pos) => keyRemainder.code pos ins) = true := by kernel_rfl

private theorem keyRemainderDecoded {pos : Nat} {ins : Instr}
    (hs : keyRemainder.inside pos) (hc : kernel.code[pos]? = some ins) :
    keyRemainder.code pos ins = true := by
  have hLo : 2362 ≤ pos := hs.1
  have hHi : pos < 2524 := hs.2
  apply List.all_eq_true.mp keyRemainderAudit (ins,pos)
  apply List.mem_of_getElem? (i := pos-2362)
  rw [List.getElem?_zipIdx,List.getElem?_take_of_lt (by omega),List.getElem?_drop,
    Nat.add_sub_of_le hLo,hc]
  rfl

private theorem keyTraceRemainder {l : Launch} {g use rank : Nat} {s : TState}
    {es : List Event} {vs : List Visit}
    (ht : At s 2362 (ringFrame l 1192 2572 use))
    (hw : Walk kernel Assumptions.all l g s es vs)
    (after : ∀ {u tail post}, At u 2524 (ringFrame l 1192 2572 use) →
      post.length < vs.length → Walk kernel Assumptions.all l g u tail post →
      KeyReadyTrace l (use+1) rank tail) : KeyReadyTrace l (use+1) rank es := by
  have hShape : RoleShape s := ⟨ht.2.1.symm ▸ Nat.zero_le _,ht.2.2.1,fun _ => ht.2.1⟩
  have hWarp : s.regs 1062 = some (b32 12) := holds_mem ht.2.2.2.2 (by
    simp [ringFrame,readyFrame])
  have hErase (e : Event) (he : keyRemainder.lo ≤ e.pc ∧ e.pc < keyRemainder.hi) :
      keyReadyMark e = none := by
    have hLo : 2362 ≤ e.pc := he.1
    have hHi : e.pc < 2524 := he.2
    have hNe : e.pc ≠ keyStation := by unfold keyStation; omega
    have hNo := readyEventOutside 5 (e := e) (by
      change 2355 ≤ e.pc ∧ e.pc < 2524
      omega)
    simp [keyReadyMark,hNe,hNo]
  rcases certifiedIntervalCut keyReadyMark keyRemainder (by decide) keyRemainderDecoded
    hErase hw (by rw [ht.1]; decide) ⟨hShape,hWarp⟩ ht.2.2.2.2
    (by simp [ringFrame,readyFrame,keyRemainder]) with h |
      ⟨u,pre,tail,post,hEs,hMark,hLen,hPc,hFault,hRole,hRegs,hWalk⟩
  · exact emptyKeyTraceOfMark h
  · obtain ⟨hKey,hReady⟩ := noReadyOrKeyOfEmpty hMark
    have hu : u.pc = 2524 := by simpa [keyRemainder] using hPc
    have hRun := after ⟨hu,hRole.1.2.2 (by omega),hRole.1.2.1,hFault,hRegs⟩ hLen hWalk
    rw [hEs]
    exact keyTraceAppend hKey (by simpa [hReady,keyCallsOfNoReady hReady] using hRun)

private theorem keySetupFallthrough {op : Op} {pc after : Nat}
    (hf : Epilogue.schedulerFallsThrough op = true)
    (hp : after = nextPc op pc ∨ BrxTarget op after) : after = pc + 1 := by
  cases op <;> simp_all [Epilogue.schedulerFallsThrough,nextPc,BrxTarget]

private theorem keyLowSlot (l : Launch) (use : Nat) :
    keyDescriptorLow l use = keyDescriptorLow l (readyStage use).val := by
  have hSlot : kvSlot (readyStage use).val = kvSlot use := by
    change (use % 3) % 3 = use % 3
    omega
  simp only [keyDescriptorLow,kvStart,hSlot]

private theorem keyAdvanceRun {l : Launch} {g : Nat} {s u : TState}
    (ht : s.pc = 2355) (hr : run kernel [] l g 6 s = some u) :
    run kernel Assumptions.all l g 6 s = some u ∧
      ∀ r ∈ ([1192,2572,2535,1062] : List Nat), u.regs r = s.regs r := by
  let region (p : Nat) : Prop := 2355 ≤ p ∧ p ≤ 2361
  let kept (r : Nat) : Prop := r ∈ ([1192,2572,2535,1062] : List Nat)
  have decoded {pos : Nat} {ins : Instr} (hLo : 2355 ≤ pos) (hHi : pos < 2361)
      (hc : kernel.code[pos]? = some ins) :
      Epilogue.schedulerFallsThrough ins.op = true ∧
        ([1192,2572,2535,1062] : List Nat).all
          (fun r => !(writesRegs ins.op).contains r) = true := by
    have hAll : ((kernel.code.drop 2355).take 6).all (fun i =>
        Epilogue.schedulerFallsThrough i.op &&
          ([1192,2572,2535,1062] : List Nat).all
            (fun r => !(writesRegs i.op).contains r)) = true := by
      set_option maxRecDepth 100000 in kernel_rfl
    have hm : ins ∈ (kernel.code.drop 2355).take 6 := by
      apply List.mem_of_getElem? (i := pos-2355)
      rw [List.getElem?_take_of_lt (by omega),List.getElem?_drop,Nat.add_sub_of_le hLo,hc]
    exact Bool.and_eq_true_iff.mp (List.all_eq_true.mp hAll ins hm)
  obtain ⟨hRun,_,hKeep⟩ := run_core_region (region := region) (kept := kept)
    (fun h => out_eq_core (show 1904 ≤ _ from by have := h.1; omega)
      (show _ < 2768 from by have := h.2; omega)) (by
      intro t v h hTau
      have hLo := h.1
      have hHi := h.2
      obtain ⟨ins,hc⟩ := tau_core_has_code hTau
      by_cases hNow : t.pc = 2361
      · exact (tau_core_not_event (hNow.symm ▸ Flow.code_2361) rfl hTau).elim
      have hCheck := decoded hLo (by omega) hc
      have hNext : v.pc = t.pc+1 := by
        rcases tau_core_frame hc hTau with rfl | hf
        · rfl
        · exact keySetupFallthrough hCheck.1 hf.pc
      refine ⟨by unfold region; omega,fun r hr => tau_core_regs hc hTau ?_⟩
      simpa using (List.all_eq_true.mp hCheck.2 r hr))
    hr (by rw [ht]; decide)
  exact ⟨hRun,hKeep⟩

private theorem keyTraceWindow {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) {g use rank : Nat} {s : TState} {es : List Event} {vs : List Visit}
    (hRank : use = 2 * rank) (hPositive : 0 < rank)
    (ht : At s 2355 (ringFrame l 1192 2572 use)) (hw : Walk kernel Assumptions.all l g s es vs)
    (after : ∀ {u tail post}, At u 2524 (ringFrame l 1192 2572 use) →
      post.length < vs.length → Walk kernel Assumptions.all l g u tail post →
      KeyReadyTrace l (use+1) rank tail) : KeyReadyTrace l (use+1) rank es := by
  have ht' : At s 2355 [(1192,b32 (kvSlot use)),(2535,b32 l.sharedBase),(1062,b32 12)] := by
    exact ht.mono ⟨ht.2.2.2.2.1,ht.2.2.2.2.2.2.1,ht.2.2.2.2.2.2.2.1,trivial⟩
  obtain ⟨t,hr,hAt⟩ := keyDescriptorLocal hp g use s ht'
  obtain ⟨hr',hKeep⟩ := keyAdvanceRun ht.1 hr
  rcases advanceWalkLocals hr' hw with rfl | ⟨post,hlen,_,hWalk⟩
  · exact emptyKeyTraceOfMark rfl
  have hOut : out kernel Assumptions.all l g t =
      .ev (.shfl .idx (b32 (keyDescriptorLow l use)) 0 31 (fun v _ => next (setReg t 2600 v))) := by
    rw [out_eq_core (by rw [hAt.1]; decide) (by rw [hAt.1]; decide),
      out_event hAt.2.2.2.1 (hAt.1.symm ▸ Flow.code_2361) rfl rfl]
    change Out.ev (shflTmpl l g t .idx 2600 none (.reg 2592)
      (.imm 0) (.imm 31) (.imm (-1))) = _
    have hBlock : l.block % 32 = 0 := by rw [hp.block]
    simp [shflTmpl,readValue,readReg,hAt.2.2.2.2.1,hBlock,Value.bytes,b32,readBits,
      pure,Except.pure]
    rfl
  have append {e : Event} {rest : List Event}
      (hDescriptor : keyDescriptorEvent l (readyStage use) e)
      (hTail : KeyReadyTrace l (use+1) rank rest) : KeyReadyTrace l (use+1) rank (e::rest) := by
    intro pre event tail hList hKey
    cases pre with
    | nil =>
      have hEq : e = event := (List.cons.inj hList).1
      subst event
      have hEven : use % 2 = 0 ∧ 2 ≤ use := by constructor <;> omega
      simpa only [List.filterMap_nil,List.length_nil,Nat.add_zero,Nat.add_sub_cancel,
        keyCalls,List.countP_nil] using And.intro hDescriptor ⟨hEven.1,hEven.2,hRank⟩
    | cons first pre =>
      obtain ⟨rfl,hEq⟩ := List.cons.inj hList
      obtain ⟨recv,ok,he⟩ := hDescriptor
      have hErase : readyEvent e = none := he.symm ▸ rfl
      have hNone : keyCalls [e] = 0 := keyCallsOfNoReady (by simp [hErase])
      rw [show e :: pre = [e] ++ pre from rfl,keyCallsAppend,hNone,Nat.zero_add]
      simp only [List.singleton_append,List.filterMap_cons,hErase]
      exact hTail pre event tail hEq hKey
  cases hWalk with
  | stop => exact emptyKeyTraceOfMark rfl
  | tau ht _ => simp [Tau,hOut] at ht
  | last he =>
    obtain ⟨tm,hTmpl,hFire⟩ := he
    obtain rfl := Out.ev.inj (hTmpl.symm.trans hOut)
    simp [Fires] at hFire
  | @ev t u e rest restVisits he hWalk' =>
    obtain ⟨tm,hTmpl,hFire⟩ := he
    obtain rfl := Out.ev.inj (hTmpl.symm.trans hOut)
    obtain ⟨reply,valid,hEvent,hNext⟩ := hFire
    have hU := Option.some.inj hNext
    subst u
    have hDesc : keyDescriptorEvent l (readyStage use) e := by
      refine ⟨reply,valid,?_⟩
      rw [hAt.1,keyLowSlot l use] at hEvent
      exact hEvent
    apply append hDesc
    have hf := ht.2.2.2.2
    have hRegs : Holds t.regs (ringFrame l 1192 2572 use) :=
      ⟨(hKeep 1192 (by simp)).trans hf.1,(hKeep 2572 (by simp)).trans hf.2.1,
        (hKeep 2535 (by simp)).trans hf.2.2.1,(hKeep 1062 (by simp)).trans hf.2.2.2.1,trivial⟩
    have hAt' : At t 2361 (ringFrame l 1192 2572 use) := hAt.mono hRegs
    have hSet := At.set (r := 2600) (v := reply) hAt' (by simp [ringFrame,readyFrame])
    have hu : At (next (setReg t 2600 reply)) 2362 (ringFrame l 1192 2572 use) :=
      hSet.mono hSet.2.2.2.2.2
    exact keyTraceRemainder hu hWalk' (fun h hPost hW => after h (by simp at hlen; omega) hW)

private theorem steadyKeyTrace {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g use rank : Nat} {t : TState} {es : List Event} {vs : List Visit}
    (hRank : use = 2 * rank + 1) (ht : At t 2291 (ringFrame l 7207 7208 use))
    (hw : Walk kernel Assumptions.all l g t es vs) :
    KeyReadyTrace l use rank es := by
  generalize hLen : vs.length = fuel
  induction fuel using Nat.strong_induction_on generalizing use rank t es vs with
  | h fuel ih =>
    apply keyTraceSegment (readyAddress hp g 0 use) ht hw
    intro w₁ v₁ hAt₁ hLen₁ hw₁
    apply keyTracePoll hp 1
      (by simp [keyReadyWait, waitSite, readyAddressSite, ringFrame, readyFrame])
      (by simp [keyReadyWait, waitSite, readyAddressSite])
      (by simp [keyReadyWait, waitSite, readyAddressSite, ringFrame]) hAt₁ hw₁
    intro w₂ es₂ v₂ hLen₂ hAt₂ hw₂
    have hAt₂' : At w₂ (2297 : Nat) (ringFrame l 7207 7208 use) := ⟨hAt₂.1, hAt₂.2.1,
      hAt₂.2.2.1, hAt₂.2.2.2.1, hAt₂.2.2.2.2.2⟩
    apply keyTraceIntervalWith 4 (by rw [hAt₂'.1]; decide)
      (by intro pc hlo hhi; change 2297 ≤ pc at hlo; change pc < 2344 at hhi
          unfold keyStation; omega) ⟨rfl, hAt₂'.2⟩
      (by simp [ringFrame, readyFrame])
      (by simp [ringFrame, readyFrame, readyInterval]) hw₂
    intro w₃ es₃ v₃ hExit₃ hAt₃ hLen₃ hw₃
    have hAt₃' : At w₃ 2344 (ringFrame l 7207 7208 use) :=
      ⟨by simpa [readyInterval] using hExit₃, hAt₃.2⟩
    apply keyTraceSegment (readyAdvanceFramed l g 0 use) hAt₃' hw₃
    intro w₄ v₄ hAt₄ hLen₄ hw₄
    apply keyTraceSegment (readyAddress hp g 1 (use + 1)) hAt₄ hw₄
    intro w₅ v₅ hAt₅ hLen₅ hw₅
    apply keyTracePoll hp 2
      (by simp [keyReadyWait, waitSite, readyAddressSite, ringFrame, readyFrame])
      (by simp [keyReadyWait, waitSite, readyAddressSite])
      (by simp [keyReadyWait, waitSite, readyAddressSite, ringFrame]) hAt₅ hw₅
    intro w₆ es₆ v₆ hLen₆ hAt₆ hw₆
    have hAt₆' : At w₆ 2355 (ringFrame l 1192 2572 (use + 1)) := ⟨hAt₆.1, hAt₆.2.1,
      hAt₆.2.2.1, hAt₆.2.2.2.1, hAt₆.2.2.2.2.2⟩
    apply keyTraceWindow hp (by change use+1 = 2 * (rank+1); omega)
      (by change 0 < rank+1; omega) hAt₆' hw₆
    intro w₇ es₇ v₇ hAt₇' hLen₇ hw₇
    apply keyTraceSegment (readyAdvanceFramed l g 1 (use + 1)) hAt₇' hw₇
    intro w₈ v₈ hAt₈ hLen₈ hw₈
    apply keyTraceIntervalWith 6 (by rw [hAt₈.1]; decide)
      (by intro pc hlo hhi; change 2529 ≤ pc at hlo; change pc < 2534 at hhi
          unfold keyStation; omega) ⟨rfl, hAt₈.2⟩
      (by simp [ringFrame, readyFrame, readyAdvanceSite])
      (by simp [ringFrame, readyFrame, readyAdvanceSite, readyInterval]) hw₈
    intro w₉ es₉ v₉ hExit₉ hAt₉ hLen₉ hw₉
    have hExit : w₉.pc = 2291 ∨ w₉.pc = 2534 := by simpa [readyInterval] using hExit₉
    rcases hExit with hPc | hPc
    · exact ih v₉.length (by omega)
        (by change use+1+1 = 2 * (rank+1)+1; omega) ⟨hPc, hAt₉.2⟩ hw₉ rfl
    · exact noKeyTraceAfter hPc.ge hw₉

private theorem afterFirstKeyTrace {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} {t : TState} {es : List Event} {vs : List Visit}
    (ht : At t 2148 (readyFrame l)) (hw : Walk kernel Assumptions.all l g t es vs) :
    KeyReadyTrace l 1 0 es := by
  apply keyTraceIntervalWith 2 (by rw [ht.1]; decide)
      (by intro pc hlo hhi; change 2148 ≤ pc at hlo; change pc < 2280 at hhi
          unfold keyStation; omega) ⟨rfl, ht.2⟩
    (by simp [readyFrame])
    (by simp [readyFrame, readyInterval]) hw
  intro u tail post hExit hu _ hw'
  have hu' : At u 2280 (readyFrame l) := ⟨by simpa [readyInterval] using hExit, hu.2⟩
  apply keyTraceSegment (readySeedShort l g) hu' hw'
  intro v visits hv _ hw''
  apply keyTraceIntervalWith 3 (by rw [hv.1]; decide)
      (by intro pc hlo hhi; change 2284 ≤ pc at hlo; change pc < 2287 at hhi
          unfold keyStation; omega) ⟨rfl, hv.2⟩
    (by simp [ringFrame, readyFrame])
      (by simp [ringFrame, readyFrame, readyInterval]) hw''
  intro w rest wVisits hExit hwAt _ hWalk
  have hPc : w.pc = 2287 ∨ w.pc = 2534 := by simpa [readyInterval] using hExit
  rcases hPc with hSteady | hTail
  · have hSeed : At w 2287 (readyFrame l) :=
      ⟨hSteady, hwAt.2.1, hwAt.2.2.1, hwAt.2.2.2.1, hwAt.2.2.2.2.2.2⟩
    apply keyTraceSegment (readySeedSteady l g) hSeed hWalk
    intro z post hz _ hW
    exact steadyKeyTrace hp (by decide) hz hW
  · exact noKeyTraceAfter hTail.ge hWalk

private theorem keyTraceFromEntry {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} {t : TState} {es : List Event} {vs : List Visit}
    (ht : At t 1908 (readyFrame l)) (hw : Walk kernel Assumptions.all l g t es vs) :
    KeyReadyTrace l 0 0 es := by
  apply keyTraceIntervalWith 0 (by rw [ht.1]; decide)
      (by intro pc hlo hhi; change 1908 ≤ pc at hlo; change pc < 2140 at hhi
          unfold keyStation; omega) ⟨rfl, ht.2⟩
    (by simp [readyFrame])
    (by simp [readyFrame, readyInterval]) hw
  intro u tail post hExit hu _ hw'
  have hPc : u.pc = 2140 ∨ u.pc = 2763 := by simpa [readyInterval] using hExit
  rcases hPc with hInit | hSkip
  · apply keyTraceSegment (readyInitialPhase l g) ⟨hInit, hu.2⟩ hw'
    intro v visits hv _ hw''
    apply keyTraceIntervalWith 1 (by rw [hv.1]; decide)
      (by intro pc hlo hhi; change 2141 ≤ pc at hlo; change pc < 2144 at hhi
          unfold keyStation; omega) ⟨rfl, hv.2⟩
      (by simp [readyFrame])
      (by simp [readyFrame, readyInterval]) hw''
    intro w rest wVisits hExit hwAt _ hw'''
    have hwAt' : At w 2144 ((2536, b32 0) :: readyFrame l) :=
      ⟨by simpa [readyInterval] using hExit, hwAt.2⟩
    apply keyTraceSegment (readyInitialAddress hp g) hwAt' hw'''
    intro z zVisits hz _ hzWalk
    apply keyTracePoll hp 0
      (by simp [keyReadyWait, waitSite, readyFrame])
      (by simp [keyReadyWait, waitSite, readyAddr, readyStage, MbarRing.Index.slot])
      (by simp [keyReadyWait, waitSite, readyWord, MbarRing.Index.round]) hz hzWalk
    intro f suffix fVisits _ hf hWalk
    have hf' : At f 2148 (readyFrame l) :=
      ⟨hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1, hf.2.2.2.2.2.2⟩
    exact afterFirstKeyTrace hp hf' hWalk
  · exact noKeyTraceAfter (by omega) hw'

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g index : Nat} {sent recv : Value} {b c : Nat}
    {ok : Bool} (hWarp : Prologue.warpIndex l g = 12)
    (he : X.get (g,index) = some ⟨2361,.shfl .idx sent b c recv ok⟩)
include hp hX hWarp he

/-- The recurring key shuffle uses twice its successful key acquire count. -/
theorem actualKeyDescriptorSentForReadyOrdinal :
    let d := Thread.Mma.atPrefix l X g index
    let use := d.kvAcquires 0 + d.kvAcquires 1 + d.kvAcquires 2 - 1
    sent = b32 (keyDescriptorLow l use) ∧ b = 0 ∧ c = 31 ∧ use % 2 = 0 ∧
      2 ≤ use ∧ use = 2 * Thread.Mma.readyOccurrence X g index .loopKey := by
  let e : Event := ⟨2361,.shfl .idx sent b c recv ok⟩
  have hGet : X.get (g,index) = some e := he
  have hg := event_thread_lt hX he
  obtain ⟨s,visits,hIndex,hAt,hWalk,_,_,inst,hHint⟩ :=
    mmaRoleWalkOfDemand hp hX hGet hWarp (.inl (by decide : 1907 < 2361))
  have hFrame : At s 1908 (readyFrame l) := hAt.mono ⟨hAt.2.2.2.2.2.1,
    hAt.2.2.2.2.1,trivial⟩
  have hTrace := keyTraceFromEntry hp hFrame hWalk
  let suffix := (X.tr g).drop 6
  let k := index-6
  have hSuffix : suffix[k]? = some e := by
    dsimp only [suffix,k]
    rwa [List.getElem?_drop,Nat.add_sub_of_le hIndex]
  have hSplit : suffix = suffix.take k ++ e :: suffix.drop (k+1) := by
    conv_lhs => rw [← List.take_append_drop k suffix]
    have hDrop : (suffix.drop k)[0]? = some e := by
      rwa [List.getElem?_drop,Nat.add_zero]
    cases h : suffix.drop k with
    | nil => simp [h] at hDrop
    | cons first rest =>
      obtain rfl : first = e := Option.some.inj (by simpa [h] using hDrop)
      have hRest : suffix.drop (k+1) = rest := by
        rw [← List.drop_drop,h]
        rfl
      rw [hRest]
  obtain ⟨⟨reply,valid,hE⟩,hEven,hPositive,hRank⟩ := hTrace (suffix.take k) e _ hSplit rfl
  have hPrefix : ((X.tr g).take 6).filterMap readyEvent = [] := by
    apply List.filterMap_eq_nil_iff.mpr
    intro prior hm
    obtain ⟨j,hj,rfl⟩ := List.getElem_of_mem hm
    have hjTrace := hj
    rw [List.length_take] at hjTrace
    rw [List.getElem_take]
    have hJLen : j < (X.tr g).length := by omega
    have hpGet : X.get (g,j) = some (X.tr g)[j] := List.getElem?_eq_getElem hJLen
    cases hMark : readyEvent (X.tr g)[j] with
    | none => rfl
    | some pair =>
      have hPc : ∃ i : Fin 4, (X.tr g)[j].pc = readyHead i := by
        unfold readyEvent at hMark
        split at hMark
        · split at hMark
          · rename_i hSite
            obtain ⟨i,_,hCode⟩ := List.any_eq_true.mp hSite
            exact ⟨i,(beq_iff_eq.mp hCode).symm⟩
          · cases hMark
        · cases hMark
      obtain ⟨i,hSite⟩ := hPc
      have hLate : 173 < (X.tr g)[j].pc := by rw [hSite]; fin_cases i <;> decide
      obtain ⟨_,_,hJ,_,_⟩ := Prologue.nonzeroCommonPrefixOfLateEvent hp hX hg
        (by rw [hWarp]; decide) hpGet hLate
      obtain rfl : j = 5 := by omega
      have hEq := Option.some.inj (hpGet.symm.trans hHint)
      rw [hEq] at hMark
      cases hMark
  have hLen : ((X.tr g).take 6).length ≤ index := (List.length_take_le ..).trans hIndex
  have hTake : ((X.tr g).take 6).take index = (X.tr g).take 6 :=
    List.take_of_length_le hLen
  have hCount : ((suffix.take k).filterMap readyEvent).length =
      (((X.tr g).take index).filterMap readyEvent).length := by
    have hPrefixLen : ((X.tr g).take 6).length = 6 := by
      rw [List.length_take, Nat.min_eq_left]
      exact hIndex.trans (len_of_get he).le
    conv_rhs => rw [← List.take_append_drop 6 (X.tr g),List.take_append]
    rw [hTake,hPrefixLen,List.filterMap_append,hPrefix,List.nil_append]
  have hUse := Thread.Mma.readyUsesAtPrefix hp hX hg hWarp index
  have hKeyCount : keyCalls (suffix.take k) = keyCalls ((X.tr g).take index) := by
    have hPrefixLen : ((X.tr g).take 6).length = 6 := by
      rw [List.length_take, Nat.min_eq_left]
      exact hIndex.trans (len_of_get he).le
    conv_rhs => rw [← List.take_append_drop 6 (X.tr g),List.take_append]
    rw [hTake,hPrefixLen,keyCallsAppend,keyCallsOfNoReady hPrefix,Nat.zero_add]
  rw [hCount,hUse,Nat.zero_add] at hE hEven hPositive hRank
  rw [hKeyCount,Nat.zero_add] at hRank
  have hWords := Kind.shfl.inj (congrArg Event.kind hE)
  exact ⟨hWords.2.1.trans (congrArg b32 (keyLowSlot l _).symm),hWords.2.2.1,
    hWords.2.2.2.1,hEven,hPositive,hRank⟩

/-- A recurring key descriptor selects a positive even ring use. -/
theorem actualKeyDescriptorSentForPositiveEvenReadyUse :
    let d := Thread.Mma.atPrefix l X g index
    let use := d.kvAcquires 0 + d.kvAcquires 1 + d.kvAcquires 2 - 1
    sent = b32 (keyDescriptorLow l use) ∧ b = 0 ∧ c = 31 ∧ use % 2 = 0 ∧ 2 ≤ use := by
  obtain ⟨hSent,hLane,hClamp,hEven,hPositive,_⟩ :=
    actualKeyDescriptorSentForReadyOrdinal hp hX hWarp he
  exact ⟨hSent,hLane,hClamp,hEven,hPositive⟩

/-- The actual sender's key descriptor selects the most recent and even ring use. -/
theorem actualKeyDescriptorSentForReadyUseWithParity :
    let d := Thread.Mma.atPrefix l X g index
    let use := d.kvAcquires 0 + d.kvAcquires 1 + d.kvAcquires 2 - 1
    sent = b32 (keyDescriptorLow l use) ∧ b = 0 ∧ c = 31 ∧ use % 2 = 0 := by
  obtain ⟨hSent,hLane,hClamp,hEven,_⟩ :=
    actualKeyDescriptorSentForPositiveEvenReadyUse hp hX hWarp he
  exact ⟨hSent,hLane,hClamp,hEven⟩

/-- The actual sender's key descriptor selects the most recently acquired ring use. -/
theorem actualKeyDescriptorSentForReadyUse :
    let d := Thread.Mma.atPrefix l X g index
    let use := d.kvAcquires 0 + d.kvAcquires 1 + d.kvAcquires 2 - 1
    sent = b32 (keyDescriptorLow l use) ∧ b = 0 ∧ c = 31 := by
  obtain ⟨hSent,hIndex,hClamp,_⟩ := actualKeyDescriptorSentForReadyUseWithParity hp hX hWarp he
  exact ⟨hSent,hIndex,hClamp⟩

/-- The received key descriptor uses the receiving lane's most recent successful ready
acquire. The lane-zero sender's matching shuffle has the same ready cursor. -/
theorem actualKeyDescriptorReceivedForReadyUse :
    let d := Thread.Mma.atPrefix l X g index
    let use := d.kvAcquires 0+d.kvAcquires 1+d.kvAcquires 2-1
    recv = b32 (keyDescriptorLow l use) := by
  obtain ⟨_,rfl,rfl⟩ := actualKeyDescriptorSentForReadyUse hp hX hWarp he
  let rank := ((X.tr g).take index).countP Execution.isShfl
  let peer := g-laneOf l g
  have hRank : X.ShflK (g,index) rank := ⟨⟨_,_,_,_,_,_,_,he⟩,rfl⟩
  obtain ⟨j,x,y,reply,valid,hPeerRank,hPeer⟩ :=
    cacheDescriptorShuffleSource hp hX 2 hWarp he hRank
  have hSame : SameWarp l g peer :=
    (laneZero_sameWarp (by rw [hp.block]; decide) (event_thread_lt hX he)).1
  have hPeerWarp := hSame.2.symm.trans hWarp
  have hEq := Thread.Mma.readyUsesAtMatchedShuffle hp hX hSame hRank hPeerRank
    he hPeer (site := 2361) rfl rfl (by decide) (by intro r; fin_cases r <;> decide) hWarp hPeerWarp
  have hSent := (actualKeyDescriptorSentForReadyUse hp hX hPeerWarp hPeer).1
  dsimp only at hEq hSent ⊢
  rw [hEq]
  exact hSent

end
end PTX.Kernels.TmlFa4Fwd.Thread
