-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Progress.WtMono
public import Kernels.InklingRelDecode.Proof.Progress.WfBarAll
public import Kernels.InklingRelDecode.Proof.Progress.Fire
public import Kernels.InklingRelDecode.Proof.Interface.LedgerInv

@[expose] public section

/-!
# The state after an event is later: the `after` clauses of `Remaining`

`RegWaitFacts.after`, `TcWaitFacts.after` and `BarTime.after` say that the state after a register
request, a warp-collective `tcgen05` event or a `bar.sync` is later than the state before it, or the
machine has stopped. All three are the one fact `time_after` about an event that is counted (not a
failed poll), is not a read and is not undefined behaviour: the virtual time rises along every
counted step of the machines (`WtMono.lean`), except at the dispatch (the load of the role byte),
whose event is a read.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Progress.Wt
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX.Kernels.InklingRelDecode.Proof.Progress

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The load of the role byte is a read: its state's kind. -/
theorem nextKind_ldRole (P : Loader.Pro) :
    nextKind (.w (.worker ⟨.ldRole, P⟩)) = .read := by
  change (match kernel.code[Flow.load_203]? with
    | some ins => opKindSub ins.op 0
    | none => NextKind.other) = .read
  decide +kernel

/-- **The event of a state at the load of the role byte is a read or undefined behaviour.** -/
theorem not_dispatch (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) {g k : Nat} {e : Event} {s : TSt}
    (he : X.get (g, k) = some e) (hσ : St Q L X g k = some (some s))
    (hnr : ∀ a bs, e.kind ≠ .rd a bs) (hnub : ∀ f, e.kind ≠ .ub f) :
    ∀ P, s ≠ .w (.worker ⟨.ldRole, P⟩) := by
  intro P hs
  subst hs
  obtain ⟨t, ins, o, hat, hinv, hc, hf⟩ := Frame.fired_site hS hX he hσ
  have hc' : kernel.code[TSt.pc (.w (.worker ⟨.ldRole, P⟩))]? = some ins := hc
  have hat' : (threadCode L g Q).AtD (.w (.worker ⟨.ldRole, P⟩)) t := hat
  have hf' : Fires (TSt.pc (.w (.worker ⟨.ldRole, P⟩))) (eventTmpl asms L g t ins.op) e o := hf
  have hk := kind_ne_other (hS g (Frame.lt_of_get hX he)) hinv hc'
  rcases tmpl_kind hat' hc' hk with ⟨f, hub⟩ | hkt
  · rw [hub] at hf'
    obtain ⟨rfl, -⟩ := hf'
    exact hnub f rfl
  · rw [nextKind_ldRole] at hkt
    obtain ⟨a, kk, hm⟩ := hkt
    rw [hm] at hf'
    obtain ⟨bs, -, rfl, -⟩ := hf'
    exact hnr a bs rfl

/-- **A counted step of a thread's machine that is not the dispatch raises the time.** -/
theorem time_lt_of_next {g : Nat} {d d' : TSt} {e : Event} (hI : (threadCode L g Q).inv d)
    (hne : ∀ P, d ≠ .w (.worker ⟨.ldRole, P⟩)) (hnb : ∀ P, d ≠ .w (.worker ⟨.bad1, P⟩))
    (h : (threadCode L g Q).next d e = some (some d')) (hc : e.counts = true) :
    time g d < time g d' := by
  cases d with
  | d s =>
    obtain ⟨a, ha, rfl⟩ := Bound.map_inv (show (DComp.next L g Q s e).map (Option.map TSt.d) =
      some (some d') from h)
    exact dcompT_lt hI.2 ha hc
  | w s =>
    obtain ⟨a, ha, rfl⟩ := Bound.map_inv (show (WComp.next L g s e).map (Option.map TSt.w) =
      some (some d') from h)
    exact wcompT_lt hI.2 (fun P hs => hne P (by rw [hs])) (fun P hs => hnb P (by rw [hs])) ha hc

/-- **No thread is at the second barrier of the bad-role path**: the role byte protocol
(`RoleReads`) excludes the states a role byte above 3 leads to. -/
theorem not_bad (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) (hR : RoleReads L X) {g k : Nat} {e : Event}
    {s : TSt} (he : X.get (g, k) = some e) (hσ : St Q L X g k = some (some s)) :
    ∀ P, s ≠ .w (.worker ⟨.bad1, P⟩) := by
  intro P hs
  have hk : k ≤ (X.tr g).length := by
    have : (X.tr g)[k]? = some e := he
    exact (List.getElem?_eq_some_iff.mp this).1.le
  have h := (phase_inv hpre hX hS hR k s hk hσ).1
  subst hs
  simp [tTo, Ledger.wTo] at h

variable (hpre : Pre Q L mem0) (hR : RoleReads L X) (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) (htr : Frame.Tracked (code L Q) X)
include hpre hR hX hS htr

/-- **The state after a counted event that is neither a read nor undefined behaviour is later**,
or the machine has stopped. -/
theorem time_after {g k : Nat} {e : Event} {d : TSt} (he : X.get (g, k) = some e)
    (hσ : St Q L X g k = some (some d)) (hc : e.counts = true) (hnr : ∀ a bs, e.kind ≠ .rd a bs)
    (hnub : ∀ f, e.kind ≠ .ub f) :
    (∃ d', St Q L X g (k + 1) = some (some d') ∧ time g d < time g d') ∨
      St Q L X g (k + 1) = none := by
  have hg := Frame.lt_of_get hX he
  have he' : (X.tr g)[k]? = some e := he
  have hs : St Q L X g (k + 1) = (threadCode L g Q).toMachine.next (some d) e := by
    show Frame.stateAt (code L Q) X g (k + 1) = _
    rw [Frame.stateAt_succ he']
    have : Frame.stateAt (code L Q) X g k = some (some d) := hσ
    rw [this]
    rfl
  obtain ⟨t, ins, o, -, hinv, -, -⟩ := Frame.fired_site hS hX he hσ
  have hne := not_dispatch hX hS he hσ hnr hnub
  have hnb := not_bad hpre hX hS hR he hσ
  have hn : (threadCode L g Q).toMachine.next (some d) e = (threadCode L g Q).next d e := rfl
  rw [hn] at hs
  rcases hx : (threadCode L g Q).next d e with _ | _ | d'
  · exact .inr (hs.trans hx)
  · exact absurd (hs.trans hx) (htr g (k + 1) hg)
  · exact .inl ⟨d', hs.trans hx, time_lt_of_next hinv hne hnb hx hc⟩

/-- **`RegWaitFacts.after`**: after a register request the thread is at a later state, or its
machine has stopped. -/
theorem reg_after {g k pc n inst : Nat} {inc : Bool} {d : TSt} (_ : g < L.threads)
    (he : X.get (g, k) = some ⟨pc, .setMaxReg inc n inst⟩) (hσ : St Q L X g k = some (some d)) :
    (∃ d', St Q L X g (k + 1) = some (some d') ∧ time g d < time g d') ∨
      St Q L X g (k + 1) = none :=
  time_after hpre hR hX hS htr he hσ rfl (fun _ _ h => by cases h) (fun _ h => by cases h)

/-- **`BarTime.after`**: after a `bar.sync` the thread is at a later state, or its machine has
stopped. -/
theorem bar_after {g k pc id : Nat} {cnt : Option Nat} {d : TSt} (_ : g < L.threads)
    (he : X.get (g, k) = some ⟨pc, .bar id cnt .sync⟩) (hσ : St Q L X g k = some (some d)) :
    (∃ d', St Q L X g (k + 1) = some (some d') ∧ time g d < time g d') ∨
      St Q L X g (k + 1) = none :=
  time_after hpre hR hX hS htr he hσ rfl (fun _ _ h => by cases h) (fun _ h => by cases h)

/-- **`TcWaitFacts.after`**: after a warp-collective `tcgen05` event the thread is at a later
state, or its machine has stopped. -/
theorem tc_after {g j k : Nat} {d : TSt} (_ : g < L.threads) (hk : X.TcK (g, j) k)
    (hσ : St Q L X g j = some (some d)) :
    (∃ d', St Q L X g (j + 1) = some (some d') ∧ time g d < time g d') ∨
      St Q L X g (j + 1) = none := by
  obtain ⟨ev, hev, hcoll⟩ := hk.1
  obtain ⟨pc, kd⟩ := ev
  cases kd <;> simp only [isTcColl] at hcoll <;>
    first
    | exact absurd hcoll (by decide)
    | exact time_after hpre hR hX hS htr hev hσ rfl (fun _ _ h => by cases h)
        (fun _ h => by cases h)

end

end PTX.Kernels.InklingRelDecode.Proof.Progress.Wt
