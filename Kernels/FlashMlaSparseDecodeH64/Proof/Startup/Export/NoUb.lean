-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.NoUbAt
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.NoUbView
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.StartEv
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.FollowStep
import Kernels.FlashMlaSparseDecodeH64.Proof.Startup.Shape
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Launch
import Lemmas.Flow.SharedSymOk
import Lemmas.Flow.AllocTmpl
import Lemmas.Flow.UbStop
import Lemmas.Flow.RoleStep

@[expose] public section

/-! # The startup's events are no undefined behaviour

`startup_noUb`: an event fired from a startup state of a followed lane is no undefined behaviour,
and the machine stops at it only if it is an exit. The startup's states are strict
(`startup_ev`'s strict thread machine), so the event is its site's event, with the site's shape
(`Startup.shape`):

* the `ld` at pc 92 reads the shared word at byte 222752 of the CTA's window, 4-aligned and in
  the window (`sharedBase_lt`, `ldSharedSym_ok`), so its template is no fault;
* the `trap` at pc 95 is no state of a lane whose read-back read the bytes of `b32 0`
  (`hrd`, the row `AllocRead`): that read goes on to the relinquishment (`Startup.succ`);
* every other site's shape is no undefined behaviour, and every event of its shape has a
  successor. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- The read-back at pc 92: its instruction's weak 4-byte load of the shared word. -/
private theorem ld_ok_ins : ∃ a : MemAccess, kernel.code[92]? = some ⟨none, .mem a⟩ ∧
    a.kind = .load ∧ a.nc = false ∧ a.sem = .weak ∧ a.space = some (.shared .cta) ∧
    a.addr.base = .sharedSym 0 ∧ a.addr.off = 222752 ∧ a.elem.width = 32 ∧
    a.rule = some .threadAccess ∧ a.locSpace? = none ∧ a.vec = 1 ∧
    (a.hints.globalOnly || a.vec == 8 || (a.vec == 4 && a.elem.width == 64)) = false :=
  ⟨_, Flow.code_92, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by decide, by decide, by decide, by decide⟩

/-- **The read-back's template is no fault**: the word is 4-aligned and in the window. -/
private theorem ld_not_ub (hp : Pre P L m) {t : TState} {ins : Instr}
    (hc : kernel.code[92]? = some ins) (f : Fault) :
    eventTmpl Assumptions.all L g t ins.op ≠ .ub f := by
  obtain ⟨a, hc92, hk, hnc, hs, hsp, hb, ho, hw, hr, hl, hv, hglob⟩ := ld_ok_ins
  obtain rfl := Option.some.inj (hc.symm.trans hc92)
  have hS := sharedBase_lt hp
  have hA := hp.sharedAlignment
  have hB := hp.sharedBase
  refine ldSharedSym_ok (o := 0) hk hs hsp hb hnc hr hl hglob (by rw [hw]; decide) ?_ f
  rw [ho, hw, hv]
  simp only [wrapAddr, truncBits, BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_ofInt]
  omega

/-- The successor of a startup site other than the read-back, the `trap` and the exits exists
for every event of the site's shape. -/
private theorem succ_ne {d : Startup.D} {e : Event} (hE : Startup.Ev L g d e)
    (h1 : d.site ≠ .ld) (h2 : d.site ≠ .trap) (h3 : ∀ r, d.site ≠ .enter r) :
    Startup.succ L g d e ≠ none := by
  obtain ⟨site, x1, x2⟩ := d
  cases site with
  | sh j =>
    fin_cases j <;> obtain ⟨r, ok, hk⟩ := hE <;>
      simp only [Startup.succ, hk, Startup.word32] <;> split <;> simp
  | elect j =>
    obtain ⟨inst, ld, -, hk⟩ := hE
    fin_cases j <;> simp only [Startup.succ, hk] <;> simp
  | ld => exact absurd rfl h1
  | trap => exact absurd rfl h2
  | enter r => exact absurd rfl (h3 r)
  | _ => simp [Startup.succ]

/-- The shape of a startup site other than the read-back is no undefined behaviour. -/
private theorem ev_ne_ub {d : Startup.D} {e : Event} (hE : Startup.Ev L g d e)
    (h1 : d.site ≠ .ld) (h2 : d.site ≠ .trap) (h3 : ∀ r, d.site ≠ .enter r) :
    ∀ f, e.kind ≠ .ub f := by
  obtain ⟨site, x1, x2⟩ := d
  cases site with
  | sh j => fin_cases j <;> obtain ⟨r, ok, hk⟩ := hE <;> simp [hk]
  | elect j => obtain ⟨inst, ld, -, hk⟩ := hE; simp [hk]
  | allocSt => obtain ⟨col, -, hk⟩ := hE; simp [hk]
  | ld => exact absurd rfl h1
  | trap => exact absurd rfl h2
  | enter r => exact absurd rfl (h3 r)
  | init n => have hk : e.kind = _ := hE; simp [hk]
  | fence => have hk : e.kind = _ := hE; simp [hk]
  | alloc => have hk : e.kind = _ := hE; simp [hk]
  | relinq => have hk : e.kind = _ := hE; simp [hk]
  | bar => have hk : e.kind = _ := hE; simp [hk]

/-- **The read-back of `b32 0` goes to the relinquishment.** -/
private theorem succ_ld_zero (d : Startup.D) (hd : d.site = .ld) (a : Acc) :
    Startup.succ L g d ⟨92, .rd a ((b32 0).toBytes.map some)⟩ =
      some (some { d with site := .relinq }) := by
  obtain ⟨site, x1, x2⟩ := d
  simp only at hd
  subst hd
  simp only [Startup.succ]
  rw [rebuild_b32]
  simp only [Startup.afterLd, Startup.ldWord, b32]
  rfl

/-- Only the read-back's successor is the `trap`. -/
private theorem succ_trap {d0 d : Startup.D} {e : Event}
    (hs : Startup.succ L g d0 e = some (some d)) (ht : d.site = .trap) : d0.site = .ld := by
  obtain ⟨s0, y1, y2⟩ := d0
  obtain ⟨s, z1, z2⟩ := d
  simp only at ht
  subst ht
  cases s0 with
  | ld => rfl
  | sh j =>
    fin_cases j
    · simp only [Startup.succ, Startup.word32] at hs
      split at hs
      · split at hs <;> simp_all
      · simp_all
    · simp only [Startup.succ, Startup.word32] at hs
      split at hs
      · split at hs
        · split_ifs at hs <;> simp_all
        · simp_all
      · simp_all
  | elect j =>
    fin_cases j
    · simp only [Startup.succ] at hs
      split at hs <;> simp_all
    · simp only [Startup.succ] at hs
      split at hs
      · split_ifs at hs <;> simp_all
      · simp_all
  | init n =>
    simp only [Startup.succ, Option.some.injEq, Startup.D.mk.injEq] at hs
    unfold Startup.initSucc at hs
    split_ifs at hs <;> simp at hs
  | alloc =>
    simp only [Startup.succ, Option.some.injEq] at hs
    split_ifs at hs <;> simp at hs
  | bar =>
    simp only [Startup.succ, Startup.enterOf, Option.some.injEq] at hs
    split_ifs at hs <;> simp at hs
  | _ => simp [Startup.succ] at hs

/-- A startup state's predecessor is a startup state of the same lane. -/
private theorem pred_start {k : Nat} {e : Event} {d : Startup.D} {n : Cls → Nat}
    (he : (X.tr g)[k]? = some e)
    (hσ : Frame.stateAt (thread P L) X g (k + 1) = some (some (.inl d, n))) :
    ∃ d0 n0, Frame.stateAt (thread P L) X g k = some (some (.inl d0, n0)) ∧
      Startup.succ L g d0 e = some (some d) := by
  rw [Frame.stateAt_succ (C := thread P L) he] at hσ
  rcases h : Frame.stateAt (thread P L) X g k with _ | _ | ⟨s, n0⟩ <;> rw [h] at hσ
  · cases hσ
  · cases hσ
  · change (thread P L g).next (s, n0) e = _ at hσ
    rcases s with d0 | ⟨i, d'⟩
    · obtain ⟨b', hb, hs'⟩ := Code.roleThread_next_start hσ
      refine ⟨d0, n0, rfl, ?_⟩
      change Startup.succ L g d0 e = some (some b') at hb
      unfold Code.enter at hs'
      split at hs'
      · cases hs'
      · cases hs'
        exact hb
    · obtain ⟨s', -, hs'⟩ := Code.roleThread_next_role hσ
      cases hs'

/-- **The startup's events are no undefined behaviour**, given that every read at pc 92 reads
`b32 0`: an event fired from a startup state of a followed lane. -/
theorem startup_noUb (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hrd : ∀ g k a bs, X.get (g, k) = some ⟨92, .rd a bs⟩ → bs = (b32 0).toBytes.map some)
    (g k : Nat) (e : Event) (he : X.get (g, k) = some e) (ha : AliveIn P L X g k .startup) :
    (∀ f, e.kind ≠ .ub f) ∧ (StopsAt P L X g k → e.kind = .exit) := by
  obtain ⟨σ, hσ, hr⟩ := aliveIn_iff.mp ha
  cases hr with
  | startup d n =>
  have hσ' : Frame.stateAt (strictC P L) X g k = some (some (.inl d, n)) :=
    Code.strict_recover hσ
  obtain ⟨t, ins, o, hat, hi, hc, hf⟩ :=
    Frame.fired_site (C := strictC P L) (fun _ _ => strict_sound hp) hX he hσ'
  have hev := Startup.shape hp hat hi.1 hc hf
  have hpc : e.pc = d.site.pc := EventFrame.fires_source_pc hf
  have hx : startupEnter P L g d = none := Code.gatedExit_none.mp hi.2
  have hx' : ∀ r, d.site ≠ .enter r := fun r hs => by
    simp [startupEnter, Startup.exitOf, hs] at hx
  have hnext : StopsAt P L X g k → Startup.succ L g d e = none := fun hs => by
    have h1 := stopsAt_iff.mp hs
    rw [Frame.stateAt_succ (C := thread P L) (show (X.tr g)[k]? = some e from he), hσ] at h1
    change (thread P L g).next (.inl d, n) e = none at h1
    rw [next_startup] at h1
    simpa using h1
  obtain ⟨site, x1, x2⟩ := d
  by_cases hld : site = .ld
  · subst hld
    have hnu : ∀ f, e.kind ≠ .ub f := fun f hk => ld_not_ub hp hc f (fires_ub hf hk)
    refine ⟨hnu, fun hs => absurd (hnext hs) ?_⟩
    rcases hev with ⟨a, bs, hk, -⟩ | ⟨f, hk⟩
    · obtain ⟨pc, kd⟩ := e
      simp only at hk hpc
      subst hk
      have hpc' : pc = 92 := hpc
      subst hpc'
      rw [hrd g k a bs he]
      rw [succ_ld_zero (g := g) _ rfl a]
      simp
    · exact absurd hk (hnu f)
  by_cases htr : site = .trap
  · subst htr
    exfalso
    have hk : e.kind = .ub .trap := hev
    cases k with
    | zero =>
      rw [Frame.stateAt_zero] at hσ
      cases hσ
    | succ j =>
      have hlen := (List.getElem?_eq_some_iff.mp (show (X.tr g)[j + 1]? = some e from he)).1
      obtain ⟨ej, hej⟩ : ∃ ej, (X.tr g)[j]? = some ej :=
        ⟨_, List.getElem?_eq_getElem (by omega)⟩
      obtain ⟨d0, n0, hσ0, hs0⟩ := pred_start hej hσ
      obtain ⟨hE0, hpc0, -⟩ := startup_ev hp hX (show X.get (g, j) = some ej from hej) hσ0
      have hl0 := succ_trap hs0 rfl
      obtain ⟨site0, y1, y2⟩ := d0
      simp only at hl0
      subst hl0
      rcases hE0 with ⟨a, bs, hk, -⟩ | ⟨f, hk⟩
      · obtain ⟨pc, kd⟩ := ej
        simp only at hk hpc0
        subst hk
        have hpc' : pc = 92 := hpc0
        subst hpc'
        rw [hrd g j a bs hej, succ_ld_zero (g := g) _ rfl a] at hs0
        simp at hs0
      · simp [Startup.succ, hk] at hs0
  · have hn1 := ev_ne_ub hev hld htr hx'
    exact ⟨hn1, fun hs => absurd (hnext hs) (succ_ne hev hld htr hx')⟩

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
