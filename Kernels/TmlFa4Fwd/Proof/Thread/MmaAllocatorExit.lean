-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaAllocationFrame
import Kernels.TmlFa4Fwd.Proof.MmaPvPrefixCut
import Kernels.TmlFa4Fwd.Proof.MmaTail
import Kernels.TmlFa4Fwd.Proof.MmaResources
import Kernels.TmlFa4Fwd.Proof.TerminalSite
import Lemmas.Flow.Final
import Lemmas.Order.DependencyWitness

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Flow PTX.Proof Mma Prologue

private theorem exitWalkRun {l : Launch} {g : Nat} {t : TState} {events : List Event}
    {visits : List Visit} (hw : Walk kernel Assumptions.all l g t events visits)
    {site : Nat} (hExit : (⟨site, .exit⟩ : Event) ∈ events) :
    Run kernel Assumptions.all l g t events none := by
  induction hw with
  | stop => cases hExit
  | tau ht _ ih =>
    cases ih hExit with
    | step h hh hTail => exact .step (.head ht h) hh hTail
    | last h hh => exact .last (.head ht h) hh
  | ev he _ ih =>
    rcases List.mem_cons.mp hExit with rfl | hTail
    · obtain ⟨_, _, hf⟩ := he
      cases fires_end_none hf (.inr rfl)
    · exact .step .refl he (ih hTail)
  | last he => exact .last .refl he

private theorem resourceWalkClean {l : Launch} {g : Nat} {t : TState} {events : List Event}
    {visits : List Visit} (hw : Walk kernel Assumptions.all l g t events visits)
    {e : Event} (hEvent : e ∈ events) (hClean : ∀ bad, e.kind ≠ .ub bad) :
    t.fault = none := by
  cases hFault : t.fault with
  | none => rfl
  | some f =>
    have hOut : out kernel Assumptions.all l g t = .ev (.ub f) := by simp [out, hFault]
    cases hw with
    | stop => cases hEvent
    | tau ht _ => rw [Tau, hOut] at ht; cases ht
    | ev he _ =>
      obtain ⟨m, hm, hf⟩ := he
      rw [hOut] at hm
      obtain rfl := Out.ev.inj hm
      cases hf.2
    | last he =>
      obtain rfl := List.mem_singleton.mp hEvent
      obtain ⟨m, hm, hf⟩ := he
      rw [hOut] at hm
      obtain rfl := Out.ev.inj hm
      exact (hClean _ (congrArg Event.kind hf.1)).elim

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution}

private theorem mmaResourceTailBefore (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g index : Nat} {e : Event}
    (hWarp : warpIndex l g = 12) (he : X.get (g, index) = some e) (hLate : 2763 ≤ e.pc)
    (hClean : ∀ f, e.kind ≠ .ub f) :
    ∃ v start events visits, At v 2763 [(1179, b32 0)] ∧
      (X.tr g).drop start = events ∧ start ≤ index ∧
      Walk kernel Assumptions.all l g v events visits ∧ e ∈ events := by
  obtain ⟨hIndex, u, _, hu, hRun⟩ :=
    mmaStartAfterAllocation hp hX he hWarp (by omega)
  let start := allocationBarrierPos l g + 2
  have hMember : e ∈ (X.tr g).drop start := by
    apply List.mem_of_getElem? (i := index-start)
    rwa [List.getElem?_drop, Nat.add_sub_of_le hIndex]
  obtain ⟨_, hWalk⟩ := walkFromRun hRun
  have hAudit : ((kernel.code.drop 1912).take (2763-1912)).all
      (pvCutCode 1912 2763 [1179]) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  obtain ⟨v, pre, tail, visits, hTrace, hv, hShape, hValue, hWalkTail, hEvent, hPre⟩ :=
    pvWalkCut (F := [(1179, b32 0)]) (by decide) (by decide) hAudit hWalk
      ⟨hu.1.ge, by rw [hu.1]; decide⟩
      ⟨⟨hu.2.1.symm ▸ Nat.zero_le _, hu.2.2.1, fun _ => hu.2.1⟩, hu.2.2.2.2.2.1⟩
      ⟨hu.2.2.2.2.1, trivial⟩ hMember hLate
  have hAt : At v 2763 [(1179, b32 0)] :=
    ⟨hv, hShape.1.2.2 (by rw [hv]; decide), hShape.1.2.1,
      resourceWalkClean hWalkTail hEvent hClean, hValue⟩
  have hTail : (X.tr g).drop (start + pre.length) = tail := by
    rw [← List.drop_drop, hTrace, List.drop_append_length]
  have hBefore : start + pre.length ≤ index := by
    by_contra! h
    have hGet : (pre ++ tail)[index - start]? = some e := by
      rw [← hTrace, List.getElem?_drop, Nat.add_sub_of_le hIndex]
      exact he
    rw [List.getElem?_append_left (by omega)] at hGet
    have hEarly := hPre e (List.mem_of_getElem? hGet)
    omega
  exact ⟨v, start + pre.length, tail, visits, hAt, hTail, hBefore, hWalkTail, hEvent⟩

/-- Each actual warp-12 exit is preceded by the deallocation of its full column-zero tile. -/
theorem mmaDeallocBeforeExit (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g index site : Nat} (hWarp : warpIndex l g = 12) (he : X.get (g, index) = some ⟨site, .exit⟩) :
    ∃ j < index, X.get (g, j) = some ⟨2766, .tc (.resource .one none (.dealloc 0 512))⟩ := by
  obtain rfl := actualExitPc hX he
  obtain ⟨v, start, tail, visits, hAt, hTail, _, hWalkTail, hExit⟩ :=
    mmaResourceTailBefore hp hX hWarp he (show 2763 ≤ 9205 by decide) (by intro _ h; cases h)
  obtain ⟨_, _, hFree, _⟩ :=
    tailResourceTrace hp (pos := start) (by decide) hAt
      (hTail.symm ▸ exitWalkRun hWalkTail hExit)
  have hg := event_thread_lt hX he
  obtain ⟨_, original⟩ := hX.thr g hg
  have hLast := PTX.Flow.Run.end_last original he (.inr rfl)
  have hFreeIn : start + 2 < (X.tr g).length := PTX.len_of_get hFree
  have hNe : start + 2 ≠ index := by
    intro h
    rw [h, he] at hFree
    cases hFree
  exact ⟨start + 2, by omega, hFree⟩

private theorem walkReturningHead {l : Launch} {g : Nat} {s u : TState}
    {events : List Event} {visits : List Visit} {expected : Event} {tmpl : Tmpl}
    (h : Walk kernel Assumptions.all l g s events visits) (hNonempty : events ≠ [])
    (hOut : out kernel Assumptions.all l g s = .ev tmpl)
    (hExact : ∀ e o, Fires s.pc tmpl e o → e = expected ∧ o = some u) :
    ∃ tail vs, events = expected :: tail ∧ Walk kernel Assumptions.all l g u tail vs := by
  cases h with
  | stop => exact (hNonempty rfl).elim
  | tau ht _ => rw [Tau, hOut] at ht; cases ht
  | ev he hTail =>
    obtain ⟨_, hTmpl, hFire⟩ := he
    obtain rfl := Out.ev.inj (hTmpl.symm.trans hOut)
    obtain ⟨rfl, hAfter⟩ := hExact _ _ hFire
    obtain rfl := Option.some.inj hAfter
    exact ⟨_, _, rfl, hTail⟩
  | last he =>
    obtain ⟨_, hTmpl, hFire⟩ := he
    obtain rfl := Out.ev.inj (hTmpl.symm.trans hOut)
    cases (hExact _ _ hFire).2

private theorem finalBarrierPrefix {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} {s : TState} {es : List Event} {vs : List Visit}
    (hs : At s 2763 [(1179, b32 0)]) (hw : Walk kernel Assumptions.all l g s es vs)
    {target : Event} (hTarget : target ∈ es) (hPc : target.pc = 2766) :
    ∃ tail, es = ⟨2763, .tc (.resource .one none .relinquish)⟩ ::
      ⟨2764, .bar 2 (some 416) .sync⟩ :: tail := by
  let a := next s
  have ha : At a 2764 [(1179, b32 0)] := hs.next
  have hRel : out kernel Assumptions.all l g s =
      .ev (.tc (.resource .one none .relinquish) a) := by
    rw [out_eq_core (by rw [hs.1]; decide) (by rw [hs.1]; decide),
      out_event hs.2.2.2.1 (by rw [hs.1]; exact Flow.code_2763) rfl rfl]
    change Out.ev (tcTmpl l g s (.tcRelinquish .one)) = _
    have hBlock : l.block % 32 = 0 := by rw [hp.block]
    simp [tcTmpl, hBlock, ofExec, a, pure, Except.pure]
  have hBar : out kernel Assumptions.all l g a = .ev (.bar 2 (next a) (some 416) .sync) := by
    rw [out_eq_core (by rw [ha.1]; decide) (by rw [ha.1]; decide),
      out_event ha.2.2.2.1 (by rw [ha.1]; exact Flow.code_2764) rfl rfl]
    change Out.ev (barTmpl l g a (.imm 2) (some (.imm 416)) .sync) = _
    have hId : readBits l g a 32 (.imm 2) = .ok (BitVec.ofNat 64 2) := rfl
    have hN : readBits l g a 32 (.imm 416) = .ok (BitVec.ofNat 64 416) := rfl
    simp only [barTmpl, hId, hN, hp.block]
    rfl
  obtain ⟨tail, visits, hEq, hRestWalk⟩ := walkReturningHead hw
    (by rintro rfl; cases hTarget) hRel (fun e o h => by simpa only [Fires, hs.1] using h)
  subst es
  have hRest : target ∈ tail := (List.mem_cons.mp hTarget).resolve_left (by rintro rfl; cases hPc)
  obtain ⟨rest, _, hTail, _⟩ := walkReturningHead hRestWalk (by rintro rfl; cases hRest) hBar
    (fun e o h => by simpa only [Fires, ha.1] using h)
  exact ⟨rest, congrArg (_ :: ·) hTail⟩

/-- Each deallocation has already relinquished its allocation permit. -/
theorem mmaRelinquishBeforeDealloc (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g index base columns : Nat} {group : CtaGroup} {dst : Option Loc} (hWarp : warpIndex l g = 12)
    (he : X.get (g,index) = some ⟨2766, .tc (.resource group dst (.dealloc base columns))⟩) :
    ∃ i < index, X.get (g,i) = some ⟨2763, .tc (.resource .one none .relinquish)⟩ := by
  obtain ⟨s, start, es, _, hs, hDrop, hStart, hw, hTarget⟩ :=
    mmaResourceTailBefore hp hX hWarp he (show 2763 ≤ 2766 by decide) (by intro _ h; cases h)
  obtain ⟨tail, hEvents⟩ := finalBarrierPrefix hp hs hw hTarget rfl
  have hGet : X.get (g,start) = some ⟨2763, .tc (.resource .one none .relinquish)⟩ := by
    change (X.tr g)[start]? = _
    rw [← Nat.add_zero start, ← List.getElem?_drop, hDrop, hEvents]
    rfl
  have hNe : start ≠ index := by
    intro h
    rw [h, he] at hGet
    cases hGet
  exact ⟨start, by omega, hGet⟩

/-- An actual release attempt has returned from the final allocation rendezvous.
Its barrier generation is distinct from the one that publishes the allocation. -/
theorem deallocationFollowsFinalSync (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {d : EvId} {site base columns : Nat} {group : CtaGroup} {dst : Option Loc}
    (hd : X.get d = some ⟨site, .tc (.resource group dst (.dealloc base columns))⟩) :
    ∃ j < d.2, ∃ key, key % 16 = 2 ∧ key ≠ 2 ∧ CtaBarK l X (d.1, j) key ∧
      CtaBarDone l X (d.1 / l.block) key ∧ X.IsBarrier (d.1, j) 2 (some 416) 2764 := by
  obtain ⟨g, index⟩ := d
  rcases (actualResourceRequest hX hd).2 with ⟨_, h⟩ | ⟨_, h⟩ | ⟨rfl, _, _⟩ <;> try cases h
  have hRole := roleBodyPcOfEvent hp hX hd
    (show 173 < 2766 by decide) (show 2766 ∉ registerHintSites by decide)
  have hWarp : warpIndex l g = 12 := by
    change roleBodyPc (warpIndex l g) 2766 at hRole
    unfold roleBodyPc at hRole
    rcases hRole with h | h
    · omega
    · split_ifs at h <;> omega
  obtain ⟨s, start, es, _, hs, hDrop, hStart, hw, hTarget⟩ :=
    mmaResourceTailBefore hp hX hWarp hd (show 2763 ≤ 2766 by decide) (by intro _ h; cases h)
  obtain ⟨tail, hEvents⟩ := finalBarrierPrefix hp hs hw hTarget rfl
  have hAt : (start + 1) + 1 ≤ index := by
    have he : es[index-start]? =
        some ⟨2766, .tc (.resource group dst (.dealloc base columns))⟩ := by
      rw [← hDrop, List.getElem?_drop, Nat.add_sub_of_le hStart]
      exact hd
    rw [hEvents] at he
    cases hj : index-start with
    | zero => simp [hj] at he
    | succ j =>
      cases j with
      | zero => simp [hj] at he
      | succ j => omega
  have hBar : X.IsBarrier (g, start+1) 2 (some 416) 2764 := by
    change (X.tr g)[start+1]? = _
    rw [show (X.tr g)[start+1]? = ((X.tr g).drop start)[1]? by rw [List.getElem?_drop],
      hDrop, hEvents]
    rfl
  have hLen : index < (X.tr g).length := (List.getElem?_eq_some_iff.mp hd).1
  have hReturned : (start + 1) + 1 < (X.tr g).length := by omega
  obtain ⟨key, hKey, hDone⟩ := ctaBarDone_of_returned hX hBar hReturned
  have hId : key % 16 = 2 := by
    obtain ⟨count, other, hSync⟩ := hKey.2.1
    have he := Event.mk.inj (Option.some.inj (hSync.symm.trans hBar))
    exact (Kind.bar.inj he.2).1
  have hNot : key ≠ 2 := by
    intro he
    subst key
    obtain ⟨_, other, hSite, h⟩ := allocationGenerationZeroSource hp hX hKey.2.2
    have hEq := (Event.mk.inj (Option.some.inj (h.symm.trans hBar))).1
    subst other
    exact (by decide : 2764 ∉ allocationEntrySites) hSite
  exact ⟨start+1, by omega, key, hId, hNot, hKey, hDone, hBar⟩

end PTX.Kernels.TmlFa4Fwd.Thread
