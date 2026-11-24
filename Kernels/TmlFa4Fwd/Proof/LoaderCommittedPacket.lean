-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderPacketFlow
public import Kernels.TmlFa4Fwd.Proof.GlobalWrites
public import Lemmas.Flow.Final

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof PTX.EventFrame

noncomputable section

private def packetBodyTmpl : Tmpl → Prop
  | .asyncCommit _ | .wait .. => False
  | _ => True

private theorem packetBodyTmplOfExec {x : Exec Tmpl} (h : AllOk packetBodyTmpl x) :
    packetBodyTmpl (ofExec x) := by
  cases x with
  | error => trivial
  | ok m => exact h

/-- No barrier wait or commit occurs within a copy packet's body. -/
def PacketBodyKind (kind : Kind) : Prop :=
  kind ≠ .asyncCommit ∧ ∀ loc parity ok acquire scope, kind ≠ .wait loc parity ok acquire scope

private theorem packetBodyTmplFires {pc : Nat} {tmpl : Tmpl} {e : Event}
    {o : Option TState} (h : packetBodyTmpl tmpl) (hf : Fires pc tmpl e o) :
    PacketBodyKind e.kind := by
  unfold PacketBodyKind
  cases tmpl <;> simp only [packetBodyTmpl, Fires] at h hf
  all_goals aesop

private def packetBodyOp (op : Op) : Bool :=
  op.isLocal || (match op with
  | .cpAsync .. => true
  | .warp w => match w.kind with | .shfl _ => true | _ => false
  | .mem a => a.rule == some .threadAccess && a.kind == .load && a.sem == .weak && !a.nc
  | _ => false)

private theorem packetBodyCode (site : Fin 6) :
    ((kernel.code.drop (copyPacketFirst site)).take
      (copyCommitPc site - copyPacketFirst site)).all (fun ins => packetBodyOp ins.op) = true := by
  fin_cases site <;> (set_option maxRecDepth 100000 in kernel_rfl)

private theorem packetBodyTemplate {l : Launch} {g : Nat} {t : TState} {op : Op}
    (hOp : packetBodyOp op = true) (hEvent : op.isLocal = false) :
    packetBodyTmpl (eventTmpl [] l g t op) := by
  unfold packetBodyOp at hOp
  simp only [hEvent, Bool.false_or] at hOp
  cases op <;> simp only [Bool.false_eq_true] at hOp
  case cpAsync =>
    simp only [eventTmpl, cpAsyncTmpl]
    apply packetBodyTmplOfExec
    repeat' first
      | apply allOk_bind; intro _
      | apply allOk_ite
      | exact True.intro
  case warp w =>
    cases hw : w.kind <;> simp only [hw, Bool.false_eq_true] at hOp
    simp only [eventTmpl, warpTmpl, hw]
    split <;> try contradiction
    all_goals try unfold shflTmpl
    all_goals repeat' first
      | exact True.intro
      | split
  case mem a =>
    simp only [Bool.and_eq_true, beq_iff_eq] at hOp
    obtain ⟨⟨⟨hr, hk⟩, hs⟩, hn⟩ := hOp
    simp only [eventTmpl, memTmpl, hr]
    split <;> try contradiction
    all_goals try simp only [hk, hs, ↓reduceIte, accessTmpl, loadTmpl]
    all_goals repeat' first
      | exact True.intro
      | split

private theorem packetBodyHasNoBackedges (site : Fin 6) :
    loaderBackEdges.all (fun (source, _) =>
      !(copyPacketFirst site ≤ source && source < copyCommitPc site)) = true := by
  fin_cases site <;> decide

private theorem packetBodyTauPc {l : Launch} {g : Nat} {s u : TState} {site : Fin 6}
    (hLo : copyPacketFirst site ≤ s.pc) (hHi : s.pc < copyCommitPc site)
    (ht : Tau kernel Assumptions.all l g s u) : copyPacketFirst site ≤ u.pc := by
  have hBounds := loaderPacketBounds site
  by_contra hu
  have hBack : u.pc ≤ s.pc := by omega
  have hMembership := loaderTauBackEdge (by omega) (by omega) hBack ht
  have hCode := List.all_eq_true.mp (packetBodyHasNoBackedges site) _ hMembership
  simp [hLo, hHi] at hCode

private theorem packetBodyCore {l : Launch} {g : Nat} {s : TState} {e : Event}
    {u : Option TState} (hLo : 174 ≤ s.pc) (hHi : s.pc < 1906)
    (h : EStep kernel Assumptions.all l g s e u) : EStep kernel [] l g s e u := by
  obtain ⟨m, hm, hf⟩ := h
  exact ⟨m, by rwa [← loaderOutCore hLo hHi], hf⟩

private theorem packetBodyEventPc {l : Launch} {g : Nat} {s u : TState} {e : Event}
    {site : Fin 6} (hLo : copyPacketFirst site ≤ s.pc) (hHi : s.pc < copyCommitPc site)
    (he : EStep kernel Assumptions.all l g s e (some u)) : copyPacketFirst site ≤ u.pc := by
  have hBounds := loaderPacketBounds site
  have hCore := packetBodyCore (by omega) (by omega) he
  rcases (estep_return_pc hCore (fun _ _ _ h => execLocal_frame h)).2 with hp | hp <;> omega

private theorem packetBodyEvent {l : Launch} {g : Nat} {t u : TState} {e : Event}
    {site : Fin 6} (hLo : copyPacketFirst site ≤ t.pc) (hHi : t.pc < copyCommitPc site)
    (he : EStep kernel Assumptions.all l g t e (some u)) : PacketBodyKind e.kind := by
  have hBounds := loaderPacketBounds site
  obtain ⟨ins, hc, hLocal, hFire⟩ :=
    estep_event_source (packetBodyCore (by omega) (by omega) he)
  have hLookup : ((kernel.code.drop (copyPacketFirst site)).take
      (copyCommitPc site - copyPacketFirst site))[t.pc - copyPacketFirst site]? = some ins := by
    rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_sub_of_le hLo]
    exact hc
  have hCode := List.all_eq_true.mp (packetBodyCode site) ins (List.mem_of_getElem? hLookup)
  exact packetBodyTmplFires (packetBodyTemplate hCode hLocal) hFire

/-- Neither an ordinary commit nor a barrier wait splits an actual packet body. -/
theorem loaderPacketEventsBodyKind {l : Launch} {g : Nat} {t : TState}
    {events : List Event} {visits : List Visit} {site : Fin 6}
    (hw : Walk kernel Assumptions.all l g t events visits) (hLo : copyPacketFirst site ≤ t.pc) :
    ∀ e ∈ (visits.takeWhile (fun v => v.pc < copyCommitPc site)).filterMap Visit.ev,
      PacketBodyKind e.kind := by
  induction hw with
  | stop => simp
  | @last s e he =>
    obtain ⟨_, _, hFire⟩ := he
    have hEnd := fires_none_ends hFire
    have hNot : PacketBodyKind e.kind := by
      constructor
      · rintro hk
        simp [Ends, hk] at hEnd
      · intro loc parity ok acq scope hk
        simp [Ends, hk] at hEnd
    by_cases hHi : s.pc < copyCommitPc site <;> simp [visit, hHi, hNot]
  | @tau s u es vs ht _ ih =>
    by_cases hHi : s.pc < copyCommitPc site
    · simpa [visit, hHi] using ih (packetBodyTauPc hLo hHi ht)
    · simp [visit, hHi]
  | @ev s u e es vs he _ ih =>
    by_cases hHi : s.pc < copyCommitPc site
    · have hNext := ih (packetBodyEventPc hLo hHi he)
      have hHead := packetBodyEvent hLo hHi he
      intro e' he'
      simp only [List.takeWhile_cons, visit, hHi, decide_true, ↓reduceIte,
        List.filterMap_cons, List.mem_cons] at he'
      rcases he' with rfl | he'
      · exact hHead
      · exact hNext e' he'
    · simp [visit, hHi]

/-- No ordinary commit splits the actual instruction window of a K/V packet. -/
theorem loaderPacketEventsNoCommit {l : Launch} {g : Nat} {t : TState}
    {events : List Event} {visits : List Visit} {site : Fin 6}
    (hw : Walk kernel Assumptions.all l g t events visits) (hLo : copyPacketFirst site ≤ t.pc) :
    ∀ e ∈ (visits.takeWhile (fun v => v.pc < copyCommitPc site)).filterMap Visit.ev,
      e.kind ≠ .asyncCommit :=
  fun e he => (loaderPacketEventsBodyKind hw hLo e he).1

/-- Any two ordered issues in the actual packet prefix are in the same ordinary
copy group of the execution, even when the thread had earlier committed packets. -/
theorem loaderPacketSameGroup {l : Launch} {m : Mem0} {X : Execution} {g begin : Nat}
    (hX : Consistent l kernel Assumptions.all m X)
    {t : TState} {events : List Event} {visits : List Visit} (site : Fin 6)
    (hw : Walk kernel Assumptions.all l g t events visits)
    (hLo : copyPacketFirst site ≤ t.pc)
    (hTrace : events <+: (X.tr g).drop begin)
    {i j : Nat} {e f : Event} {a b : AsyncCopy.Spec}
    (hi : ((visits.takeWhile (fun v => v.pc < copyCommitPc site)).filterMap Visit.ev)[i]? = some e)
    (hj : ((visits.takeWhile (fun v => v.pc < copyCommitPc site)).filterMap Visit.ev)[j]? = some f)
    (he : e.kind = .copy a) (hf : f.kind = .copy b) (hOrder : i < j) :
    SameAsyncGroup X (g, begin + i) (g, begin + j) := by
  let packet := (visits.takeWhile (fun v => v.pc < copyCommitPc site)).filterMap Visit.ev
  have hPacket : packet <+: events := by
    obtain ⟨rest, hRest⟩ := List.takeWhile_prefix (fun v : Visit => v.pc < copyCommitPc site)
      (l := visits)
    refine ⟨rest.filterMap Visit.ev, ?_⟩
    rw [hw.events, ← hRest, List.filterMap_append]
  obtain ⟨tail, hTail⟩ := hPacket.trans hTrace
  have hGet {pos : Nat} {event : Event} (hPos : packet[pos]? = some event) :
      X.get (g, begin + pos) = some event := by
    have hLen := (List.getElem?_eq_some_iff.mp hPos).1
    change (X.tr g)[begin + pos]? = some event
    rw [← List.getElem?_drop, ← hTail, List.getElem?_append_left hLen, hPos]
  have hCopy {pos : Nat} {event : Event} {s : AsyncCopy.Spec}
      (hPos : packet[pos]? = some event) (hKind : event.kind = .copy s) :
      X.Copy (g, begin + pos) s := by
    refine ⟨event.pc, ?_⟩
    have hEvent := hGet hPos
    cases event with
    | mk pc kind =>
      change kind = .copy s at hKind
      subst kind
      exact hEvent
  have hA := hCopy hi he
  have hB := hCopy hj hf
  refine ⟨⟨a, hA, (actualCopyShape hX hA).completion⟩,
    ⟨b, hB, (actualCopyShape hX hB).completion⟩, rfl, by omega, ?_⟩
  intro k pc hki hkj hCommit
  have hjLen : j < packet.length := (List.getElem?_eq_some_iff.mp hj).1
  have hkLen : k - begin < packet.length := by omega
  let no := packet[k - begin]
  have hk : packet[k - begin]? = some no := List.getElem?_eq_getElem hkLen
  have hObserved := hGet hk
  rw [show begin + (k - begin) = k by omega, hCommit] at hObserved
  have hKind := congrArg Event.kind (Option.some.inj hObserved)
  have hNoCommit := loaderPacketEventsNoCommit hw hLo no (List.getElem_mem _)
  exact hNoCommit hKind.symm

end
end PTX.Kernels.TmlFa4Fwd.Loader
