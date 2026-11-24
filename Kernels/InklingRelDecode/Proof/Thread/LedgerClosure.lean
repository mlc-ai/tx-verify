-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.LedgerTables

@[expose] public section

/-!
# The successors of the machines keep the phase

`dPh`, `wPh` (`LedgerTables.lean`) are the counts of register requests and barrier-1 events before
a state in the first round. Every successor's phase is the state's plus the state's own
instruction's increment (`rInc`, `bInc`), except that a worker role's tail leads to the dispatch
loop's head, which is the next round: `(3,3)` is `(0,0)` one round on.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Ledger
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

/-- A successor of `none` or `some none` under `Option.map` stays so. -/
theorem mapInv {α β : Type} {f : α → β} {x : Option (Option α)} {b : β}
    (h : x.map (Option.map f) = some (some b)) : ∃ a, x = some (some a) ∧ f a = b := by
  cases x with
  | none => simp at h
  | some o =>
    cases o with
    | none => simp at h
    | some a => exact ⟨a, rfl, by simpa using h⟩

/-! ### The prologue -/

/-- A prologue successor is not the first site. -/
theorem pro_next_ne {L : Launch} {g : Nat} {d d' : ProA.D} {e : Event}
    (h : ProA.next L g d e = some (some d')) : d'.site ≠ ProA.Site.sMax := by
  obtain ⟨s, dt⟩ := d
  cases s <;> simp only [ProA.next] at h <;> (repeat' split at h) <;>
    first
    | (simp at h; done)
    | (simp only [Option.some.injEq] at h; subst h; (try simp only [ProA.qSite])
       (repeat' split) <;> decide)

/-! ### The softmax region -/

theorem sm_toBar20_site {d d' : Sm.D} (h : Sm.toBar20 d = some (some d')) :
    d'.site = .bar20 := by
  unfold Sm.toBar20 at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    rfl
  · simp at h

/-- **The region's first two sites are entered only in turn**: `setMaxReg` leads to `bar0`, and no
other site's successor is `setMaxReg` or `bar0`. -/
theorem sm_next_site {L : Launch} {g : Nat} {d d' : Sm.D} {e : Event}
    (h : Sm.next L g d e = some (some d')) :
    (d.site = .setMaxReg → d'.site = .bar0) ∧
      (d.site ≠ .setMaxReg → d'.site ≠ .setMaxReg ∧ d'.site ≠ .bar0) := by
  obtain ⟨s, e0, i, m, l, cw, cv, w, v, sv, pf, stg⟩ := d
  cases s <;>
    first
    | (simp only [Sm.next, Sm.afterSetup, Sm.afterArrive, Sm.D.afterSum, Sm.D.afterMax,
         Sm.D.afterMaxT] at h
       (repeat' split at h)
       all_goals (try simp only [Option.some.injEq, reduceCtorEq] at h)
       all_goals (try (have := sm_toBar20_site h))
       all_goals (try obtain ⟨-, rfl⟩ := h)
       all_goals simp_all)

/-! ### The epilogue -/

/-- **An epilogue step keeps the phase.** -/
theorem epi_next_ph {d d' : Epi.D} {e : Event} (h : Epi.next d e = some (some d')) :
    (dPh (.epi d')).1 = (dPh (.epi d)).1 + rInc (epiReq d.site) ∧
      (dPh (.epi d')).2 = (dPh (.epi d)).2 + bInc (epiB1 d.site) := by
  obtain ⟨s, pr, o, sk⟩ := d
  cases s <;> simp only [Epi.next] at h <;> (repeat' split at h) <;>
    simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
    (simp only [dPh, Epi.D.stores, Epi.stNext, epiReq, epiB1, rInc, bInc]
     (try split_ifs) <;> simp)

/-! ### The default-partition thread -/

/-- **A step of the default-partition machine keeps the phase**, and the default partition's
phases are one round (no wrap). -/
theorem d_next_ph {L : Launch} {g : Nat} {Q : Params} {s s' : DComp.St} {e : Event}
    (h : DComp.next L g Q s e = some (some s')) :
    (dPh s').1 = (dPh s).1 + rInc (dReq s) ∧ (dPh s').2 = (dPh s).2 + bInc (dB1 s) := by
  cases s with
  | dstart d =>
    simp only [DComp.next, DComp.dstartNext] at h
    obtain ⟨a, ha, hf⟩ := mapInv h
    obtain ⟨site, tm⟩ := d
    cases site <;> simp only [DStart.next] at ha <;> (repeat' split at ha) <;>
      simp only [Option.some.injEq, reduceCtorEq] at ha <;> (try subst ha) <;>
      (try subst hf) <;> simp_all [dPh, dReq, dB1, dstartReq, rInc, bInc, ProA.D.start]
  | pro d =>
    obtain ⟨st, dt⟩ := d
    by_cases hb : st = ProA.Site.bar18
    · subst hb
      simp only [DComp.next, DComp.proNext, ite_true] at h
      split at h
      · simp only [Option.some.injEq] at h
        subst h
        simp [dPh, dReq, dB1, proReq, proB1, rInc, bInc, SmEntry.d0]
      · simp at h
    · simp only [DComp.next, DComp.proNext, hb, ite_false] at h
      obtain ⟨a, ha, rfl⟩ := mapInv h
      have := pro_next_ne ha
      cases st <;> simp_all [dPh, dReq, dB1, proReq, proB1, rInc, bInc]
  | sm d =>
    simp only [DComp.next, DComp.smNext] at h
    split at h
    · rename_i hl
      simp only [DComp.exitNext] at h
      split at h
      · simp only [Option.some.injEq] at h
        subst h
        obtain ⟨st, e0, i, m, l, cw, cv, w, v, sv, pf, stg⟩ := d
        cases st <;>
          simp_all [DComp.leaves, dPh, dReq, dB1, smReq, smB1, rInc, bInc, Epi.D.start,
            Epi.D.startSk, Epi.D.entry] <;> (try split_ifs) <;> (try simp)
      · simp at h
    · obtain ⟨a, ha, rfl⟩ := mapInv h
      obtain ⟨h1, h2⟩ := sm_next_site ha
      obtain ⟨st, e0, i, m, l, cw, cv, w, v, sv, pf, stg⟩ := d
      obtain ⟨st', e0', i', m', l', cw', cv', w', v', sv', pf', stg'⟩ := a
      simp only at h1 h2
      cases st <;> cases st' <;> simp_all [dPh, dReq, dB1, smReq, smB1, rInc, bInc]
  | epi d =>
    simp only [DComp.next] at h
    obtain ⟨a, ha, rfl⟩ := mapInv h
    exact epi_next_ph ha

/-! ### The worker roles -/

/-- The loader's steps keep the phase (a site's successor is a site of the same stretch: the
setup, the loop, the tail). -/
theorem loader_next_ph {L : Launch} {g : Nat} {P : Loader.Pro} {d d' : Loader.D} {e : Event}
    (h : Loader.next L g d e = some (some d')) :
    (wPh (.loader d' P)).1 = (wPh (.loader d P)).1 + rInc (loaderReq d.site) ∧
      (wPh (.loader d' P)).2 = (wPh (.loader d P)).2 + bInc (loaderB1 d.site) := by
  obtain ⟨s, pro, i, n, p0, p1, ln⟩ := d
  cases s <;> simp only [Loader.next, Loader.afterIter, Loader.readI, Loader.readN] at h <;>
    (repeat' split at h) <;>
    simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
    simp [wPh, loaderReq, loaderB1, rInc, bInc]

/-- The MMA role's steps keep the phase. -/
theorem mma_next_ph {L : Launch} {g : Nat} {P : Loader.Pro} {d d' : Mma.D} {e : Event}
    (h : Mma.next L g d e = some (some d')) :
    (wPh (.mma d' P)).1 = (wPh (.mma d P)).1 + rInc (mmaReq d.site) ∧
      (wPh (.mma d' P)).2 = (wPh (.mma d P)).2 + bInc (mmaB1 d.site) := by
  obtain ⟨s, i, n, tm, pro⟩ := d
  cases s <;>
    simp only [Mma.next, Mma.afterQk, Mma.iterNext, Mma.qkNext, Mma.pvNext, Mma.start] at h <;>
    (repeat' split at h) <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
    simp [wPh, mmaReq, mmaB1, rInc, bInc]

/-! ### The worker thread -/

/-- The kind of a worker state: 0 in the common start and the dispatch loop, 1 in a role, 2 in
the exit. -/
def wKind : WComp.WSt → Nat
  | .worker _ => 0
  | .idle _ | .loader .. | .mma .. => 1
  | .exit _ => 2

/-- One at the tails of the roles, which return to the dispatch loop's head: one round on. -/
def wrap : WComp.WSt → Nat
  | .idle d => if d.site = .inc then 1 else 0
  | .loader d _ => if d.site = .setMaxInc then 1 else 0
  | .mma d _ => if d.site = .setMaxRegInc then 1 else 0
  | _ => 0

/-- The role index a load of the role byte returns. -/
def roleIdx (bs : List (Option Byte)) : Option Nat :=
  match rebuild 3 bs with
  | .error _ => none
  | .ok v =>
    match extendLoaded (MemExt.zero 32) 8 v with
    | .ok (.bits 32 x) => some x.toNat
    | _ => none

theorem roleSite_cases {i : Nat} {s : Worker.Site} (h : Worker.roleSite i = some s) :
    (i = 0 ∧ s = .toLoader) ∨ (i = 1 ∧ s = .toMma) ∨ (i = 2 ∧ s = .toIdle) ∨
      (i = 3 ∧ s = .toExit) := by
  rcases i with _ | _ | _ | _ | i <;> simp_all [Worker.roleSite]

/-- The worker states the ledger's rounds do not have: the entries of the roles (`toIdle`,
`toLoader`, `toMma`, `toExit`), which the machine is never at since the dispatch goes straight
into the role's first state, and the bad sites `bad0`, `bad1` (a role byte above 3), whose round
has one request and three barrier-1 events where the table's round has three requests: the
machine is at them only for a role byte above 3 (`dispatch_role`), which the protocol of the role
bytes (`RoleReads`) excludes. -/
def wTo : WComp.WSt → Bool
  | .worker w =>
    decide (w.site = .toIdle ∨ w.site = .toLoader ∨ w.site = .toMma ∨ w.site = .toExit ∨
      w.site = .bad0 ∨ w.site = .bad1)
  | _ => false

/-- An index the role table does not have is at least 4. -/
theorem roleSite_none {i : Nat} (h : Worker.roleSite i = none) : 4 ≤ i := by
  rcases i with _ | _ | _ | _ | i <;> simp_all [Worker.roleSite]

/-- A role's first state: kind and phase; or, for the bad site (a role byte above 3), the worker
state at `bad0`, whose kind is 0. -/
theorem roleStart_cases {L : Launch} {g : Nat} {P : Loader.Pro} {s : Worker.Site}
    {s' : WComp.WSt} (h : WComp.roleStart L g P s = some (some s')) :
    (s = .toLoader ∧ wKind s' = 1 ∧ wPh s' = (1, 1)) ∨
      (s = .toMma ∧ wKind s' = 1 ∧ wPh s' = (1, 1)) ∨
      (s = .toIdle ∧ wKind s' = 1 ∧ wPh s' = (1, 1)) ∨
      (s = .toExit ∧ wKind s' = 2 ∧ wPh s' = (1, 1)) ∨
      (s = .bad0 ∧ wTo s' = true ∧ wPh s' = (1, 1)) := by
  cases s <;> simp only [WComp.roleStart] at h <;> (repeat' split at h) <;>
    simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
    simp [wKind, wPh, wTo, Loader.D.start, Worker.Idle.D.start]

/-- The zero-extension of a loaded byte is below 256. -/
theorem extend_zero_lt {v : Value} {x : BitVec 64}
    (h : extendLoaded (MemExt.zero 32) 8 v = .ok (.bits 32 x)) : x.toNat < 256 := by
  unfold extendLoaded at h
  cases hb : v.bitPattern with
  | none => simp [hb, throw, throwThe, MonadExceptOf.throw] at h
  | some n =>
    simp only [hb, pure, Except.pure, Except.ok.injEq, MemExt.extendBits, Value.bits.injEq,
      true_and] at h
    subst h
    simp only [truncBits, BitVec.toNat_ofNat]
    have h1 : n % 2 ^ 8 < 256 := Nat.mod_lt _ (by decide)
    omega

/-- **The dispatch's successor** is the role the byte indexes: the exit for 3, a role below 3;
for an index above 3 (a byte the protocol excludes) it is the bad site `bad0`, which the ledger's
rounds do not have (`wTo`). -/
theorem dispatch_role {L : Launch} {g : Nat} {P : Loader.Pro} {e : Event} {s' : WComp.WSt}
    (h : WComp.next L g (.worker ⟨.ldRole, P⟩) e = some (some s')) :
    ∃ a bs, e.kind = .rd a bs ∧
      ((roleIdx bs = some 3 ∧ wKind s' = 2) ∨ (∃ i, roleIdx bs = some i ∧ i < 3 ∧ wKind s' = 1) ∨
        (∃ i, roleIdx bs = some i ∧ 4 ≤ i ∧ wTo s' = true)) ∧
      wPh s' = (1, 1) := by
  simp only [WComp.next, WComp.dispatch, Worker.next] at h
  cases hk : e.kind with
  | rd a bs =>
    rw [hk] at h
    refine ⟨a, bs, rfl, ?_⟩
    simp only [Worker.dispatch] at h
    unfold roleIdx
    cases hr : rebuild 3 bs with
    | error err => simp [hr] at h
    | ok v =>
      simp only [hr] at h ⊢
      cases hx : extendLoaded (MemExt.zero 32) 8 v with
      | error err => simp [hx] at h
      | ok val =>
        simp only [hx] at h ⊢
        cases val with
        | bits w x =>
          by_cases hw : w = 32
          · subst hw
            have hxl := extend_zero_lt hx
            have htr : (truncBits 32 x).toNat = x.toNat := by
              simp only [truncBits, BitVec.toNat_ofNat]
              omega
            simp only [htr] at h
            cases hs : Worker.roleSite x.toNat with
            | none =>
              simp only [hs, Option.getD_none] at h
              have h4 := roleSite_none hs
              rcases roleStart_cases h with
                  ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, k, p⟩
              · simp at h1
              · simp at h1
              · simp at h1
              · simp at h1
              · exact ⟨Or.inr (Or.inr ⟨x.toNat, rfl, h4, k⟩), p⟩
            | some s =>
              simp only [hs, Option.getD_some] at h
              rcases roleStart_cases h with
                  ⟨rfl, k, p⟩ | ⟨rfl, k, p⟩ | ⟨rfl, k, p⟩ | ⟨rfl, k, p⟩ | ⟨rfl, k, p⟩ <;>
                rcases roleSite_cases hs with ⟨hi, hs'⟩ | ⟨hi, hs'⟩ | ⟨hi, hs'⟩ | ⟨hi, hs'⟩ <;>
                simp_all
          · simp [hw] at h
        | _ => simp at h
  | _ => rw [hk] at h; simp at h

theorem wKind_le (s : WComp.WSt) : wKind s ≤ 2 := by
  cases s <;> simp [wKind]

theorem wrap_le (s : WComp.WSt) : wrap s ≤ 1 := by
  cases s <;> simp [wrap] <;> split_ifs <;> omega

theorem wrap_of_kind {s : WComp.WSt} (h : wKind s ≠ 1) : wrap s = 0 := by
  cases s <;> simp_all [wKind, wrap]

/-- The worker states at the load of the role byte. -/
def ldRoleSt : WComp.WSt → Bool
  | .worker w => decide (w.site = .ldRole)
  | _ => false

theorem wTo_of_kind {s : WComp.WSt} (h : wKind s ≠ 0) : wTo s = false := by
  cases s <;> simp_all [wKind, wTo]

/-- The role byte the dispatch reads is below 4: the event of a state at the load of the role
byte, if it is a read, returns an index below 4. -/
def RoleByte (s : WComp.WSt) (e : Event) : Prop :=
  ldRoleSt s = true → ∀ a bs, e.kind = .rd a bs → ∀ i, roleIdx bs = some i → i < 4

/-- **No step of the worker machine reaches an entry of a role or a bad site**, from a state that
is none of them, if the role byte the dispatch reads is below 4 (`RoleByte`): the bad sites are
reached only by a larger byte, and are left only to the loop head. -/
theorem w_next_noTo {L : Launch} {g : Nat} {s s' : WComp.WSt} {e : Event}
    (h : WComp.next L g s e = some (some s')) (hs : wTo s = false) (hb : RoleByte s e) :
    wTo s' = false := by
  cases s with
  | worker w =>
    obtain ⟨site, P⟩ := w
    by_cases hl : site = .ldRole
    · subst hl
      obtain ⟨a, bs, hk, hd, -⟩ := dispatch_role h
      have hb' := hb rfl a bs hk
      rcases hd with ⟨-, h2⟩ | ⟨i, -, -, h2⟩ | ⟨i, hi, hi4, -⟩
      · exact wTo_of_kind (by omega)
      · exact wTo_of_kind (by omega)
      · have := hb' i hi
        omega
    · have h' : (Worker.next L g ⟨site, P⟩ e).map (Option.map WComp.WSt.worker) =
          some (some s') := by
        cases site <;> first | exact absurd rfl hl | exact h
      obtain ⟨a, ha, rfl⟩ := mapInv h'
      obtain ⟨st, P'⟩ := a
      cases site <;> simp only [Worker.next] at ha <;> (repeat' split at ha) <;>
        (try simp only [Option.some.injEq, reduceCtorEq, Worker.D.mk.injEq] at ha) <;>
        (try obtain ⟨rfl, rfl⟩ := ha) <;> simp_all [wTo]
  | idle d =>
    obtain ⟨site, P⟩ := d
    cases site <;> simp only [WComp.next] at h
    all_goals first
      | (obtain ⟨a, ha, rfl⟩ := mapInv h
         simp [wTo])
      | (simp only [Option.some.injEq] at h
         subst h
         simp [wTo])
  | loader d P =>
    obtain ⟨d0, pro, i, n, p0, p1, ln⟩ := d
    cases d0 <;> simp only [WComp.next] at h
    all_goals first
      | (obtain ⟨a, ha, rfl⟩ := mapInv h
         simp [wTo])
      | (simp only [Option.some.injEq] at h
         subst h
         simp [wTo])
  | mma d P =>
    obtain ⟨d0, i, n, tm, pro⟩ := d
    cases d0 <;> simp only [WComp.next] at h
    all_goals first
      | (obtain ⟨a, ha, rfl⟩ := mapInv h
         simp [wTo])
      | (simp only [Option.some.injEq] at h
         subst h
         simp [wTo])
  | exit x =>
    obtain ⟨site, P⟩ := x
    cases site <;> simp only [WComp.next] at h
    · simp only [Option.some.injEq] at h
      subst h
      simp [wTo]
    · simp at h

/-- **A step of the worker machine keeps the phase** up to the round: the phase of the successor
plus a round (`(3,3)`) at the roles' tails is the state's plus its instruction's increment. The
kinds: a role stays in its role until its tail, the tail leads to the loop's head, the exit stays,
and the common start and the loop stay in the worker kind except at the load of the role byte.
The state is no bad site (`wTo`): the bad site `bad1` leads to the loop head, which is not in the
phase of its round. -/
theorem w_next {L : Launch} {g : Nat} {s s' : WComp.WSt} {e : Event}
    (h : WComp.next L g s e = some (some s')) (hs : wTo s = false) :
    (wPh s').1 + 3 * wrap s = (wPh s).1 + rInc (wReqS s) ∧
      (wPh s').2 + 3 * wrap s = (wPh s).2 + bInc (wB1S s) ∧
      (wKind s = 1 → wrap s = 0 → wKind s' = 1) ∧ (wrap s = 1 → wKind s' = 0) ∧
      (wKind s = 2 → wKind s' = 2) ∧ (wKind s = 0 → ldRoleSt s = false → wKind s' = 0) := by
  cases s with
  | worker w =>
    obtain ⟨site, P⟩ := w
    by_cases hl : site = .ldRole
    · subst hl
      obtain ⟨a, bs, -, -, hp⟩ := dispatch_role h
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hp]; simp [wPh, wReqS, wReq, rInc, wrap]
      · rw [hp]; simp [wPh, wB1S, wB1, bInc, wrap]
      all_goals simp [wKind, wrap, ldRoleSt]
    · have h' : (Worker.next L g ⟨site, P⟩ e).map (Option.map WComp.WSt.worker) =
          some (some s') := by
        cases site <;> first | exact absurd rfl hl | exact h
      obtain ⟨a, ha, rfl⟩ := mapInv h'
      obtain ⟨st, P'⟩ := a
      cases site <;> simp only [Worker.next] at ha <;> (repeat' split at ha) <;>
        (try simp only [Option.some.injEq, reduceCtorEq, Worker.D.mk.injEq] at ha) <;>
        (try obtain ⟨rfl, rfl⟩ := ha) <;> simp_all [wPh, wReqS, wB1S, wReq, wB1, rInc, bInc, wrap,
          wKind, ldRoleSt, wTo]
  | idle d =>
    obtain ⟨site, P⟩ := d
    cases site <;> simp only [WComp.next] at h
    all_goals first
      | (obtain ⟨a, ha, rfl⟩ := mapInv h
         obtain ⟨st, P'⟩ := a
         simp only [Worker.Idle.next, Option.some.injEq, Worker.Idle.D.mk.injEq] at ha
         obtain ⟨rfl, rfl⟩ := ha
         simp [wPh, wReqS, wB1S, idleReq, idleB1, rInc, bInc, wrap, wKind, ldRoleSt])
      | (simp only [Option.some.injEq] at h
         subst h
         simp [wPh, wReqS, wB1S, idleReq, idleB1, rInc, bInc, wrap, wKind, ldRoleSt])
  | loader d P =>
    obtain ⟨d0, pro, i, n, p0, p1, ln⟩ := d
    cases d0 <;> simp only [WComp.next] at h
    all_goals first
      | (obtain ⟨a, ha, rfl⟩ := mapInv h
         have h1 := loader_next_ph (P := P) ha
         simp only [loaderReq, loaderB1, rInc, bInc] at h1
         simp_all [wPh, wReqS, wB1S, loaderReq, loaderB1, rInc, bInc, wrap, wKind, ldRoleSt])
      | (simp only [Option.some.injEq] at h
         subst h
         simp [wPh, wReqS, wB1S, loaderReq, loaderB1, rInc, bInc, wrap, wKind, ldRoleSt])
  | mma d P =>
    obtain ⟨d0, i, n, tm, pro⟩ := d
    cases d0 <;> simp only [WComp.next] at h
    all_goals first
      | (obtain ⟨a, ha, rfl⟩ := mapInv h
         have h1 := mma_next_ph (P := P) ha
         simp only [mmaReq, mmaB1, rInc, bInc] at h1
         simp_all [wPh, wReqS, wB1S, mmaReq, mmaB1, rInc, bInc, wrap, wKind, ldRoleSt])
      | (simp only [Option.some.injEq] at h
         subst h
         simp [wPh, wReqS, wB1S, mmaReq, mmaB1, rInc, bInc, wrap, wKind, ldRoleSt])
  | exit x =>
    obtain ⟨site, P⟩ := x
    cases site <;> simp only [WComp.next] at h
    · simp only [Option.some.injEq] at h
      subst h
      simp [wPh, wReqS, wB1S, rInc, bInc, wrap, wKind, ldRoleSt]
    · simp at h

/-! ### What the tables say about the requests and the barriers -/

/-- **The default partition's requests are `inc 256`.** -/
theorem d_req_inc {s : DComp.St} {i : Bool} {n : Nat} (h : dReq s = some (i, n)) :
    i = true ∧ n = 256 := by
  cases s with
  | dstart d => cases hs : d.site <;> simp_all [dReq, dstartReq]
  | pro d => cases hs : d.site <;> simp_all [dReq, proReq]
  | sm d => cases hs : d.site <;> simp_all [dReq, smReq]
  | epi d => cases hs : d.site <;> simp_all [dReq, epiReq]

/-- **A worker's request is the role's `dec 24` exactly at phase 1**, else `inc 256`. -/
theorem w_req_sched {s : WComp.WSt} {i : Bool} {n : Nat} (h : wReqS s = some (i, n)) :
    (i, n) = if (wPh s).1 = 1 then (false, 24) else (true, 256) := by
  cases s with
  | worker w => cases hs : w.site <;> simp_all [wReqS, wReq, wPh]
  | idle d => cases hs : d.site <;> simp_all [wReqS, idleReq, wPh]
  | loader d P => cases hs : d.site <;> simp_all [wReqS, loaderReq, wPh]
  | mma d P => cases hs : d.site <;> simp_all [wReqS, mmaReq, wPh]
  | exit x => simp [wReqS] at h

/-- **A request site that follows a request and is no loop head**: the phases of the default
partition's requests, and of the roles'. A request that is not the first has the barriers before
it that the pairing needs: after one barrier-1 event at phase `(1,1)`, after three at `(2,3)`. -/
theorem d_req_phase {s : DComp.St} {i : Bool} {n : Nat} (h : dReq s = some (i, n)) :
    dPh s = (0, 0) ∨ dPh s = (1, 1) ∨ dPh s = (2, 3) := by
  cases s with
  | dstart d => cases hs : d.site <;> simp_all [dReq, dstartReq, dPh]
  | pro d => cases hs : d.site <;> simp_all [dReq, proReq, dPh]
  | sm d => cases hs : d.site <;> simp_all [dReq, smReq, dPh]
  | epi d => cases hs : d.site <;> simp_all [dReq, epiReq, dPh]

theorem w_req_phase {s : WComp.WSt} {i : Bool} {n : Nat} (h : wReqS s = some (i, n))
    (hr : ¬ ∃ P, s = .worker ⟨.loop, P⟩) :
    wPh s = (1, 1) ∨ wPh s = (2, 3) := by
  cases s with
  | worker w =>
    cases hs : w.site <;> simp_all [wReqS, wReq, wPh]
    all_goals exact hr w.P (by cases w; simp_all)
  | idle d => cases hs : d.site <;> simp_all [wReqS, idleReq, wPh]
  | loader d P => cases hs : d.site <;> simp_all [wReqS, loaderReq, wPh]
  | mma d P => cases hs : d.site <;> simp_all [wReqS, mmaReq, wPh]
  | exit x => simp [wReqS] at h

/-! ### The role of a warp -/

/-- The roles of warps 4 to 7: the idle role is warp 4's and 5's, the loader is warp 6's, the MMA
role is warp 7's. The machine follows every role byte on every warp, so this is not an invariant
of the machine: it holds along a run whose role bytes are the warps' (`RoleOfWarp`). -/
def roleWarp (warp : Nat) : WComp.WSt → Prop
  | .idle _ => warp = 4 ∨ warp = 5
  | .loader _ _ => warp = 6
  | .mma _ _ => warp = 7
  | _ => True

/-- The role index the role table gives warp `w` of 4 to 7: byte `w - 4` of the word `0x01000202`
the prologue stores, that is 2 (idle) for warps 4 and 5, 0 (loader) for warp 6 and 1 (MMA) for
warp 7. -/
def warpRole (w : Nat) : Nat := 16777730 / 256 ^ (w - 4) % 256

/-- At the dispatch, the thread is of a worker warp (4 to 7) and the role byte it reads, if it
names a role (an index below 3), names the warp's. -/
def RoleOfWarp (w : Nat) (s : WComp.WSt) (e : Event) : Prop :=
  ldRoleSt s = true → 4 ≤ w ∧ w < 8 ∧
    ∀ a bs, e.kind = .rd a bs → ∀ i, roleIdx bs = some i → i < 3 → i = warpRole w

theorem warpRole_0 {w : Nat} (hw : w < 8) (h : 0 = warpRole w) : w = 6 := by
  revert h
  unfold warpRole
  interval_cases w <;> norm_num

theorem warpRole_1 {w : Nat} (hw : w < 8) (h : 1 = warpRole w) : w = 7 := by
  revert h
  unfold warpRole
  interval_cases w <;> norm_num

theorem warpRole_2 {w : Nat} (hw4 : 4 ≤ w) (hw : w < 8) (h : 2 = warpRole w) :
    w = 4 ∨ w = 5 := by
  revert h
  unfold warpRole
  interval_cases w <;> norm_num

/-- **The dispatch enters the warp's role** when the byte it reads names the warp's role or the
exit. -/
theorem dispatch_roleWarp {L : Launch} {g : Nat} {P : Loader.Pro} {e : Event} {s' : WComp.WSt}
    (h : WComp.next L g (.worker ⟨.ldRole, P⟩) e = some (some s'))
    (hr : RoleOfWarp (WComp.warpOf L g) (.worker ⟨.ldRole, P⟩) e) :
    roleWarp (WComp.warpOf L g) s' := by
  obtain ⟨hw4, hw, hr⟩ := hr (by simp [ldRoleSt])
  simp only [WComp.next, WComp.dispatch, Worker.next] at h
  cases hk : e.kind with
  | rd a bs =>
    rw [hk] at h
    have hr' := hr a bs hk
    simp only [Worker.dispatch] at h
    unfold roleIdx at hr'
    cases hb : rebuild 3 bs with
    | error err => simp [hb] at h
    | ok v =>
      simp only [hb] at h hr'
      cases hx : extendLoaded (MemExt.zero 32) 8 v with
      | error err => simp [hx] at h
      | ok val =>
        simp only [hx] at h hr'
        cases val with
        | bits w x =>
          by_cases hw32 : w = 32
          · subst hw32
            have hxl := extend_zero_lt hx
            have htr : (truncBits 32 x).toNat = x.toNat := by
              simp only [truncBits, BitVec.toNat_ofNat]
              omega
            simp only [htr] at h
            have hi := hr' x.toNat rfl
            cases hs : Worker.roleSite x.toNat with
            | none =>
              simp only [hs, Option.getD_none, WComp.roleStart, Option.some.injEq] at h
              subst h
              trivial
            | some st =>
              simp only [hs, Option.getD_some] at h
              rcases roleSite_cases hs with ⟨h0, rfl⟩ | ⟨h0, rfl⟩ | ⟨h0, rfl⟩ | ⟨h0, rfl⟩
              · simp only [WComp.roleStart, Option.some.injEq] at h
                subst h
                exact warpRole_0 hw (h0 ▸ hi (by omega))
              · simp only [WComp.roleStart] at h
                split at h
                · split at h
                  · simp only [Option.some.injEq] at h
                    subst h
                    exact warpRole_1 hw (h0 ▸ hi (by omega))
                  · simp at h
                · simp at h
              · simp only [WComp.roleStart, Option.some.injEq] at h
                subst h
                exact warpRole_2 hw4 hw (h0 ▸ hi (by omega))
              · simp only [WComp.roleStart, Option.some.injEq] at h
                subst h
                trivial
          · simp [hw32] at h
        | _ => simp at h
  | _ => rw [hk] at h; simp at h

/-- **A step of the worker machine keeps the role of the warp.** -/
theorem w_next_roleWarp {L : Launch} {g : Nat} {s s' : WComp.WSt} {e : Event}
    (h : WComp.next L g s e = some (some s')) (hs : roleWarp (WComp.warpOf L g) s)
    (hr : RoleOfWarp (WComp.warpOf L g) s e) :
    roleWarp (WComp.warpOf L g) s' := by
  cases s with
  | worker w =>
    obtain ⟨site, P⟩ := w
    by_cases hl : site = .ldRole
    · subst hl
      exact dispatch_roleWarp h hr
    · have h' : (Worker.next L g ⟨site, P⟩ e).map (Option.map WComp.WSt.worker) =
          some (some s') := by
        cases site <;> first | exact absurd rfl hl | exact h
      obtain ⟨a, ha, rfl⟩ := mapInv h'
      trivial
  | idle d =>
    obtain ⟨site, P⟩ := d
    cases site <;> simp only [WComp.next] at h
    all_goals first
      | (obtain ⟨a, ha, rfl⟩ := mapInv h
         exact hs)
      | (simp only [Option.some.injEq] at h
         subst h
         trivial)
  | loader d P =>
    obtain ⟨d0, pro, i, n, p0, p1, ln⟩ := d
    cases d0 <;> simp only [WComp.next] at h
    all_goals first
      | (obtain ⟨a, ha, rfl⟩ := mapInv h
         exact hs)
      | (simp only [Option.some.injEq] at h
         subst h
         trivial)
  | mma d P =>
    obtain ⟨d0, i, n, tm, pro⟩ := d
    cases d0 <;> simp only [WComp.next] at h
    all_goals first
      | (obtain ⟨a, ha, rfl⟩ := mapInv h
         exact hs)
      | (simp only [Option.some.injEq] at h
         subst h
         trivial)
  | exit x =>
    obtain ⟨site, P⟩ := x
    cases site <;> simp only [WComp.next] at h
    · simp only [Option.some.injEq] at h
      subst h
      trivial
    · simp at h

/-- The position of the request of ordinal `r` of a thread of warp `w`: the default partition's
three requests, the workers' loop head and the role's `dec` and `inc`. -/
def reqPcOf (w r : Nat) : Nat :=
  if w < 4 then
    (if r = 0 then Flow.setMaxReg_0 else if r = 1 then Flow.setMaxReg_1 else Flow.setMaxReg_9)
  else if r % 3 = 0 then Flow.setMaxReg_4
  else if r % 3 = 1 then
    (if w = 6 then Flow.setMaxReg_5 else if w = 7 then Flow.setMaxReg_7 else Flow.setMaxReg_2)
  else (if w = 6 then Flow.setMaxReg_6 else if w = 7 then Flow.setMaxReg_8 else Flow.setMaxReg_3)

theorem reqPcOf_round {w : Nat} (hw : 4 ≤ w) (r t : Nat) :
    reqPcOf w (r + 3 * t) = reqPcOf w r := by
  have h : (r + 3 * t) % 3 = r % 3 := by omega
  have hn : ¬ w < 4 := by omega
  simp only [reqPcOf, hn, h, ite_false]

/-- **A default-partition request is at the position of its ordinal.** -/
theorem d_req_pc {w : Nat} (hw : w < 4) {s : DComp.St} {i : Bool} {n : Nat}
    (h : dReq s = some (i, n)) : DComp.pc s = reqPcOf w (dPh s).1 := by
  cases s with
  | dstart d => cases hs : d.site <;> simp_all [dReq, dstartReq, dPh, reqPcOf, DComp.pc,
      DStart.Site.pc]
  | pro d => cases hs : d.site <;> simp_all [dReq, proReq, dPh, reqPcOf, DComp.pc, ProA.Site.pc]
  | sm d => cases hs : d.site <;> simp_all [dReq, smReq, dPh, reqPcOf, DComp.pc, Sm.Site.pc]
  | epi d => cases hs : d.site <;> simp_all [dReq, epiReq, dPh, reqPcOf, DComp.pc, Epi.Site.pc]

/-- **A worker's request is at the position of its ordinal in its round.** -/
theorem w_req_pc {w : Nat} (hw : 4 ≤ w) {s : WComp.WSt} {i : Bool} {n : Nat}
    (h : wReqS s = some (i, n)) (hto : wTo s = false) (hrw : roleWarp w s) :
    WComp.pc s = reqPcOf w (wPh s).1 := by
  have hn : ¬ w < 4 := by omega
  cases s with
  | worker x =>
    obtain ⟨site, P⟩ := x
    cases site <;> simp_all [wReqS, wReq, wTo, wPh, reqPcOf, WComp.pc, Worker.Site.pc]
  | idle d =>
    have hrw' : w = 4 ∨ w = 5 := hrw
    have h6 : w ≠ 6 := by omega
    have h7 : w ≠ 7 := by omega
    cases hs : d.site <;> simp_all [wReqS, idleReq, wPh, reqPcOf, WComp.pc, Worker.Idle.Site.pc]
  | loader d P =>
    cases hs : d.site <;> simp_all [wReqS, loaderReq, wPh, reqPcOf, WComp.pc, Loader.Site.pc,
      roleWarp]
  | mma d P =>
    cases hs : d.site <;> simp_all [wReqS, mmaReq, wPh, reqPcOf, WComp.pc, Mma.Site.pc, roleWarp]
  | exit x => simp [wReqS] at h

/-- **A worker request that is no loop head is a role's**: its state is of the role kind. -/
theorem w_req_kind {s : WComp.WSt} {i : Bool} {n : Nat} (h : wReqS s = some (i, n))
    (hr : ¬ ∃ P, s = .worker ⟨.loop, P⟩) (hto : wTo s = false) : wKind s = 1 := by
  cases s with
  | worker w =>
    obtain ⟨site, P⟩ := w
    cases site <;> simp_all [wReqS, wReq, wTo]
  | idle d => rfl
  | loader d P => rfl
  | mma d P => rfl
  | exit x => simp [wReqS] at h

/-- **A barrier-1 event of the default partition at barrier ordinal 0 or 2** has made at least as
many requests as the ordinal says (one and two). -/
theorem d_b1_phase {s : DComp.St} (h : dB1 s = true) :
    ((dPh s).2 = 0 → 1 ≤ (dPh s).1) ∧ ((dPh s).2 = 2 → 2 ≤ (dPh s).1) ∧ (dPh s).2 ≤ 3 := by
  cases s with
  | dstart d => simp [dB1] at h
  | pro d => cases hs : d.site <;> simp_all [dB1, proB1, dPh]
  | sm d => cases hs : d.site <;> simp_all [dB1, smB1, dPh]
  | epi d => cases hs : d.site <;> simp_all [dB1, epiB1, dPh]

/-- A worker barrier-1 event at barrier ordinal 0 or 2 has made at least one and two requests;
the state is no bad site (`wTo`), whose second barrier event is at ordinal 2 after one request. -/
theorem w_b1_phase {s : WComp.WSt} (h : wB1S s = true) (hto : wTo s = false) :
    ((wPh s).2 = 0 → 1 ≤ (wPh s).1) ∧ ((wPh s).2 = 2 → 2 ≤ (wPh s).1) ∧ (wPh s).2 ≤ 3 := by
  cases s with
  | worker w => cases hs : w.site <;> simp_all [wB1S, wB1, wPh, wTo]
  | idle d => cases hs : d.site <;> simp_all [wB1S, idleB1, wPh]
  | loader d P => cases hs : d.site <;> simp_all [wB1S, loaderB1, wPh]
  | mma d P => cases hs : d.site <;> simp_all [wB1S, mmaB1, wPh]
  | exit x => simp [wB1S] at h

/-- The default partition's exit is at phase `(3, 4)`. -/
theorem d_exit_phase (d : Epi.D) (h : d.site = .exit) : dPh (.epi d) = (3, 4) := by
  simp [dPh, h]

/-- A worker state is the loop head exactly when its phase is `(0,0)`, in the common start and the
loop; every other state of a worker has a positive phase. -/
theorem w_ph_le (s : WComp.WSt) : (wPh s).1 ≤ 2 ∧ (wPh s).2 ≤ 3 := by
  cases s with
  | worker w => cases hs : w.site <;> simp [wPh, hs]
  | idle d => cases hs : d.site <;> simp [wPh, hs]
  | loader d P => cases hs : d.site <;> simp [wPh, hs]
  | mma d P => cases hs : d.site <;> simp [wPh, hs]
  | exit x => simp [wPh]

end
end PTX.Kernels.InklingRelDecode.Proof.Ledger
