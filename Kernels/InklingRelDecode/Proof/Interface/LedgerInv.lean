-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.LedgerEvents

@[expose] public section

/-!
# The counts of register requests and barrier-1 events along a thread

The number of register requests (`rqN`) and of barrier-1 events (`b1N`) of a thread before its
`k`-th event are functions of the abstract state before it and of the number `t` of rounds of the
dispatch loop the thread has made: `rqN = r + 3 t` and `b1N = b + 3 t` where `(r, b)` is the
state's phase (`tPh`). The default partition makes one round (`t = 0`); a worker is in a role
only in its first round, and its exit is after a first round.

The last two facts come from the loads of the role byte, whose values are the protocol's
(`RoleReads`): the first load of a worker returns the index of one of its roles (0, 1 or 2, not
the exit), and a later load returns the exit (3). With them `phase_inv` is the induction along
the thread's events and `ledger_facts` the statements the register ledger is made of.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Ledger

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The number of register requests of thread `g` before its event `k`. -/
def rqN (X : Execution) (g k : Nat) : Nat :=
  ((X.tr g).take k).countP SetMaxNReg.isRequest

/-- The number of barrier-1 events of thread `g` before its event `k`. -/
def b1N (X : Execution) (g k : Nat) : Nat :=
  ((X.tr g).take k).countP (Execution.isBarId 1)

/-- The kind of a state: 3 in the default partition, else the worker kind (0 the common start and
the dispatch loop, 1 a role, 2 the exit). -/
def tKind : TSt → Nat
  | .d _ => 3
  | .w s => wKind s

/-- The state is an entry of a role (a state the worker machine never is at). -/
def tTo : TSt → Bool
  | .d _ => false
  | .w s => wTo s

/-- **The role byte protocol.** The first load of the role byte of a worker (after one barrier-1
event) returns the index of a role other than the exit, and that index is the warp's role
(`warpRole`: the idle role for warps 4 and 5, the loader for warp 6, the MMA role for warp 7); a
later load (after at least four) returns the exit. -/
def RoleReads (L : Launch) (X : Execution) : Prop :=
  ∀ g k a bs, g < L.threads → 128 ≤ g % L.block →
    X.get (g, k) = some ⟨Worker.Site.ldRole.pc, .rd a bs⟩ →
      (b1N X g k = 1 → ∃ i < 3, roleIdx bs = some i) ∧ (4 ≤ b1N X g k → roleIdx bs = some 3) ∧
      (b1N X g k = 1 → roleIdx bs = some (warpRole (g % L.block / 32)))

/-- The state before event `k` of thread `g` has the counts of its phase and `t` rounds. -/
def PhaseAt (X : Execution) (g k : Nat) (s : TSt) : Prop :=
  tTo s = false ∧
  ∃ t, rqN X g k = (tPh s).1 + 3 * t ∧ b1N X g k = (tPh s).2 + 3 * t ∧
    (tKind s = 3 → t = 0) ∧ (tKind s = 1 → t = 0) ∧ (tKind s = 2 → 1 ≤ t) ∧ t ≤ 1

theorem countP_take_succ (p : Event → Bool) {l : List Event} {k : Nat} {e : Event}
    (he : l[k]? = some e) :
    (l.take (k + 1)).countP p = (l.take k).countP p + (if p e = true then 1 else 0) := by
  rw [List.take_add_one, he]
  simp [List.countP_append]

theorem ldRoleSt_form {s : WComp.WSt} (h : ldRoleSt s = true) :
    ∃ P, s = .worker ⟨.ldRole, P⟩ := by
  cases s with
  | worker w =>
    obtain ⟨site, P⟩ := w
    simp only [ldRoleSt, decide_eq_true_eq] at h
    subst h
    exact ⟨P, rfl⟩
  | _ => simp [ldRoleSt] at h

/-- **The event at a load of the role byte** is the load, of a worker thread of the launch. -/
theorem ldRole_event (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) {g k : Nat} {e : Event}
    {P : Loader.Pro} {a : Acc} {bs : List (Option Byte)}
    (he : X.get (g, k) = some e)
    (hσ : St Q L X g k = some (some (.w (.worker ⟨.ldRole, P⟩)))) (hk : e.kind = .rd a bs) :
    X.get (g, k) = some ⟨Worker.Site.ldRole.pc, .rd a bs⟩ ∧ g < L.threads ∧
      128 ≤ g % L.block := by
  have hpc := Frame.event_pc hS hX he hσ
  obtain ⟨t, ins, o, -, hinv, -, -⟩ := Frame.fired_site hS hX he hσ
  have hw : ¬ IsDefault L g := hinv.1
  refine ⟨?_, Frame.lt_of_get hX he, ?_⟩
  · obtain ⟨pc, kd⟩ := e
    simp only at hk hpc
    subst hk
    rw [he]
    exact congrArg some (by rw [hpc]; rfl)
  · unfold IsDefault at hw
    omega

theorem rInc_eq {o : Option (Bool × Nat)} : rInc o = if o.isSome = true then 1 else 0 := rfl

/-- **The counts along a thread**: at every state a thread's machine is at before an event, the
counts of requests and barrier-1 events are the state's phase plus `t` rounds. -/
theorem phase_inv (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) (hR : RoleReads L X) {g : Nat} :
    ∀ k s, k ≤ (X.tr g).length → St Q L X g k = some (some s) → PhaseAt X g k s := by
  intro k
  induction k with
  | zero =>
    intro s _ hs
    have hs : Frame.stateAt (code L Q) X g 0 = some (some s) := hs
    rw [Frame.stateAt_zero] at hs
    have hs' : s = (threadCode L g Q).init := (Option.some.inj (Option.some.inj hs)).symm
    subst hs'
    have h0 : tPh (threadCode L g Q).init = (0, 0) ∧ tKind (threadCode L g Q).init ≠ 1 ∧
        tKind (threadCode L g Q).init ≠ 2 ∧ tTo (threadCode L g Q).init = false := by
      by_cases hd : g % L.block < 128
      · have he : (threadCode L g Q).init = .d (.dstart (DStart.D.start L g)) := by
          show (if g % L.block < 128 then TSt.d (DComp.code L g Q).init
            else .w (WComp.code L g Q).init) = _
          simp only [hd, ite_true]
        rw [he]
        simp [tPh, tKind, dPh, tTo]
      · have he : (threadCode L g Q).init =
            .w (.worker (Worker.D.start (Worker.startPro Q))) := by
          show (if g % L.block < 128 then TSt.d (DComp.code L g Q).init
            else .w (WComp.code L g Q).init) = _
          simp only [hd, ite_false]
        rw [he]
        simp [tPh, tKind, wPh, wKind, Worker.D.start, tTo, wTo]
    obtain ⟨h1, h2, h3, h4'⟩ := h0
    refine ⟨h4', 0, ?_, ?_, ?_, ?_, ?_, by omega⟩
    · simp [rqN, h1]
    · simp [b1N, h1]
    · intro h
      rfl
    · intro h
      exact absurd h h2
    · intro h
      exact absurd h h3
  | succ k ih =>
    intro s' hk hs'
    have hs'' : Frame.stateAt (code L Q) X g (k + 1) = some (some s') := hs'
    obtain ⟨e, he⟩ : ∃ e, (X.tr g)[k]? = some e := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    rw [Frame.stateAt_succ he] at hs''
    cases hσ : Frame.stateAt (code L Q) X g k with
    | none => rw [hσ] at hs''; simp at hs''
    | some o =>
      cases o with
      | none => rw [hσ] at hs''; simp [Flow.Code.toMachine] at hs''
      | some s =>
        rw [hσ] at hs''
        simp only [Option.bind_some] at hs''
        have hn : (threadCode L g Q).next s e = some (some s') := hs''
        obtain ⟨hto, t, h1, h2, h3, h4, h5, h6⟩ := ih s (by omega) hσ
        have hget : X.get (g, k) = some e := he
        obtain ⟨hreq, -⟩ := event_req hX hS hget hσ
        have hb := event_b1 hpre hX hS hget hσ
        have hrq : rqN X g (k + 1) = rqN X g k + rInc (tReq s) := by
          unfold rqN
          rw [countP_take_succ _ he]
          by_cases hr : SetMaxNReg.isRequest e = true
          · have h2 := hreq.mp hr
            simp [hr, h2, rInc_eq]
          · have h2 : ¬ (tReq s).isSome = true := fun h => hr (hreq.mpr h)
            simp [hr, h2, rInc_eq]
        have hb1 : b1N X g (k + 1) = b1N X g k + bInc (tB1 s) := by
          unfold b1N
          rw [countP_take_succ _ he, hb]
          rfl
        cases s with
        | d s0 =>
          obtain ⟨a, ha, rfl⟩ := Ledger.mapInv (show (DComp.next L g Q s0 e).map
            (Option.map TSt.d) = some (some s') from hn)
          obtain ⟨p1, p2⟩ := d_next_ph ha
          have ht0 : t = 0 := h3 rfl
          subst ht0
          have e1 : tPh (TSt.d a) = dPh a := rfl
          have e2 : tPh (TSt.d s0) = dPh s0 := rfl
          have e3 : tReq (TSt.d s0) = dReq s0 := rfl
          have e4 : tB1 (TSt.d s0) = dB1 s0 := rfl
          rw [e2] at h1 h2
          rw [e3] at hrq
          rw [e4] at hb1
          refine ⟨rfl, 0, ?_, ?_, fun _ => rfl, fun h => ?_, fun h => ?_, by omega⟩
          · rw [hrq, e1, h1]
            omega
          · rw [hb1, e1, h2]
            omega
          · simp [tKind] at h
          · simp [tKind] at h
        | w s0 =>
          obtain ⟨a, ha, rfl⟩ := Ledger.mapInv (show (WComp.next L g s0 e).map
            (Option.map TSt.w) = some (some s') from hn)
          have hs0 : wTo s0 = false := hto
          obtain ⟨p1, p2, k1, k2, k3, k4⟩ := w_next ha hs0
          have hle := wKind_le a
          have hle0 := wKind_le s0
          have hwr := wrap_le s0
          have e1 : tPh (TSt.w a) = wPh a := rfl
          have e2 : tPh (TSt.w s0) = wPh s0 := rfl
          have e3 : tReq (TSt.w s0) = wReqS s0 := rfl
          have e4 : tB1 (TSt.w s0) = wB1S s0 := rfl
          have e5 : tKind (TSt.w s0) = wKind s0 := rfl
          rw [e2] at h1 h2
          rw [e3] at hrq
          rw [e4] at hb1
          rw [e5] at h4 h5
          have hrole : RoleByte s0 e := by
            intro hl a bs hk i hi
            obtain ⟨P, rfl⟩ := ldRoleSt_form hl
            obtain ⟨hev, hg, hw⟩ := ldRole_event hX hS hget hσ hk
            have hph : (wPh (.worker ⟨.ldRole, P⟩)).2 = 1 := rfl
            rcases (by omega : b1N X g k = 1 ∨ b1N X g k = 4) with hb | hb
            · obtain ⟨j, hj, hj'⟩ := (hR g k a bs hg hw hev).1 hb
              rw [hj'] at hi
              simp only [Option.some.injEq] at hi
              omega
            · have := (hR g k a bs hg hw hev).2.1 (by omega)
              rw [this] at hi
              simp only [Option.some.injEq] at hi
              omega
          refine ⟨w_next_noTo ha hs0 hrole, t + wrap s0, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · rw [hrq, e1, h1]
            omega
          · rw [hb1, e1, h2]
            omega
          · intro h
            have : wKind a = 3 := h
            omega
          · intro h1k
            have h1k' : wKind a = 1 := h1k
            by_cases hl : ldRoleSt s0 = true
            · obtain ⟨P, rfl⟩ := ldRoleSt_form hl
              obtain ⟨a', bs, hk, hdisj, -⟩ := dispatch_role ha
              obtain ⟨hev, hg, hw⟩ := ldRole_event hX hS hget hσ hk
              have hwr0 : wrap (.worker ⟨.ldRole, P⟩) = 0 := rfl
              rw [hwr0]
              by_contra hne
              have hb4 : 4 ≤ b1N X g k := by
                have : (wPh (.worker ⟨.ldRole, P⟩)).2 = 1 := rfl
                omega
              have h3 := (hR g k a' bs hg hw hev).2.1 hb4
              rcases hdisj with ⟨-, hk2⟩ | ⟨i, hi, hi3, -⟩ | ⟨i, hi, hi4, -⟩
              · omega
              · rw [h3] at hi
                simp only [Option.some.injEq] at hi
                omega
              · have := hrole hl a' bs hk i hi
                omega
            · have hl' : ldRoleSt s0 = false := by simpa using hl
              rcases (by omega : wKind s0 = 0 ∨ wKind s0 = 1 ∨ wKind s0 = 2) with hk0 | hk0 | hk0
              · have := k4 hk0 hl'
                omega
              · by_cases hw : wrap s0 = 0
                · have := h4 hk0
                  omega
                · have := k2 (by omega)
                  omega
              · have := k3 hk0
                omega
          · intro h2k
            have h2k' : wKind a = 2 := h2k
            by_cases hl : ldRoleSt s0 = true
            · obtain ⟨P, rfl⟩ := ldRoleSt_form hl
              obtain ⟨a', bs, hk, hdisj, -⟩ := dispatch_role ha
              obtain ⟨hev, hg, hw⟩ := ldRole_event hX hS hget hσ hk
              have hwr0 : wrap (.worker ⟨.ldRole, P⟩) = 0 := rfl
              rw [hwr0]
              by_contra hne
              have hb1' : b1N X g k = 1 := by
                have : (wPh (.worker ⟨.ldRole, P⟩)).2 = 1 := rfl
                omega
              obtain ⟨i, hi, hi3⟩ := (hR g k a' bs hg hw hev).1 hb1'
              rcases hdisj with ⟨h3, -⟩ | ⟨i', hi', hi3', hk1⟩ | ⟨i', hi', hi4', -⟩
              · rw [h3] at hi3
                simp only [Option.some.injEq] at hi3
                omega
              · omega
              · have := hrole hl a' bs hk i' hi'
                omega
            · have hl' : ldRoleSt s0 = false := by simpa using hl
              rcases (by omega : wKind s0 = 0 ∨ wKind s0 = 1 ∨ wKind s0 = 2) with hk0 | hk0 | hk0
              · have := k4 hk0 hl'
                omega
              · by_cases hw : wrap s0 = 0
                · have := k1 hk0 hw
                  omega
                · have := k2 (by omega)
                  omega
              · have := h5 hk0
                have := wrap_of_kind (s := s0) (by omega)
                omega
          · by_cases hw : wrap s0 = 0
            · omega
            · have hk1 : wKind s0 = 1 := by
                by_contra hne
                exact hw (wrap_of_kind hne)
              have := h4 hk1
              omega

/-- **The role byte a worker reads at the dispatch is its warp's or the exit** (`RoleReads`, with
the barrier-1 count of the dispatch: one in the first round, four in the later one). -/
theorem roleOfWarp_at (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) (hR : RoleReads L X) {g k : Nat}
    {s : WComp.WSt} {e : Event} (he : (X.tr g)[k]? = some e)
    (hσ : St Q L X g k = some (some (.w s))) : RoleOfWarp (WComp.warpOf L g) s e := by
  intro hl
  obtain ⟨P, rfl⟩ := ldRoleSt_form hl
  have he' : X.get (g, k) = some e := he
  have hk : k ≤ (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1.le
  obtain ⟨t, ins, o, -, hinv, -, -⟩ := Frame.fired_site hS hX he' hσ
  have hwi : Worker.Inv L g ⟨.ldRole, P⟩ := hinv.2
  have h4 := hwi.warp
  have h8 : WComp.warpOf L g < 8 := by
    have := hwi.tid
    simp only [WComp.warpOf, Worker.warpOf] at h4 ⊢
    omega
  refine ⟨h4, h8, fun a bs hkd i hi hi3 => ?_⟩
  obtain ⟨hget, hg, h128⟩ := ldRole_event hX hS he' hσ hkd
  obtain ⟨-, t', -, h2, -, -, -, h6⟩ := phase_inv hpre hX hS hR k _ hk hσ
  simp only [tPh, Ledger.wPh] at h2
  rcases (by omega : b1N X g k = 1 ∨ 4 ≤ b1N X g k) with h1 | h4'
  · have := (hR g k a bs hg h128 hget).2.2 h1
    rw [hi] at this
    exact Option.some.inj this
  · have := (hR g k a bs hg h128 hget).2.1 h4'
    rw [hi] at this
    have := Option.some.inj this
    omega

/-- **The role of a thread is its warp's**: the idle role is warp 4's and 5's, the loader is warp
6's and the MMA role is warp 7's. The machine follows every role byte on every warp; the role
byte protocol (`RoleReads`) gives each warp its own role. -/
theorem roleWarp_of_reads (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) (hR : RoleReads L X) :
    RoleWarps Q L X := by
  intro g k
  induction k with
  | zero =>
    intro s _ hs
    have hs : Frame.stateAt (code L Q) X g 0 = some (some s) := hs
    rw [Frame.stateAt_zero] at hs
    have hs' : s = (threadCode L g Q).init := (Option.some.inj (Option.some.inj hs)).symm
    subst hs'
    show RoleWarp L g (if g % L.block < 128 then .d (DComp.code L g Q).init
      else .w (WComp.code L g Q).init)
    split_ifs <;> simp [RoleWarp, roleWarp]
  | succ k ih =>
    intro s' hk hs'
    have hs'' : Frame.stateAt (code L Q) X g (k + 1) = some (some s') := hs'
    obtain ⟨e, he⟩ : ∃ e, (X.tr g)[k]? = some e := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    rw [Frame.stateAt_succ he] at hs''
    cases hσ : Frame.stateAt (code L Q) X g k with
    | none => rw [hσ] at hs''; simp at hs''
    | some o =>
      cases o with
      | none => rw [hσ] at hs''; simp [Flow.Code.toMachine] at hs''
      | some s =>
        rw [hσ] at hs''
        simp only [Option.bind_some] at hs''
        have hn : (threadCode L g Q).next s e = some (some s') := hs''
        have ih' := ih (by omega) hσ
        cases s with
        | d s0 =>
          obtain ⟨a, ha, rfl⟩ := Ledger.mapInv (show (DComp.next L g Q s0 e).map
            (Option.map TSt.d) = some (some s') from hn)
          trivial
        | w s0 =>
          obtain ⟨a, ha, rfl⟩ := Ledger.mapInv (show (WComp.next L g s0 e).map
            (Option.map TSt.w) = some (some s') from hn)
          exact w_next_roleWarp ha ih' (roleOfWarp_at hpre hX hS hR he hσ)

/-- **The role of a thread is its warp's**, from the roles by warp of the thread facts
(`ThreadFacts.roleWarp`, `roleWarp_of_reads`). -/
theorem roleWarp_inv (hW : RoleWarps Q L X) {g : Nat} :
    ∀ k s, k ≤ (X.tr g).length → St Q L X g k = some (some s) → RoleWarp L g s :=
  fun _ _ hk hσ => hW hk hσ

end
end PTX.Kernels.InklingRelDecode.Proof.Interface
