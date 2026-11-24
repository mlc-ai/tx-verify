-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.ProtocolThreads
public import Kernels.InklingRelDecode.Proof.Protocol.RingCount
public import Kernels.InklingRelDecode.Proof.Protocol.RingSched

@[expose] public section

/-!
# The loader's polls of `kv_empty`, counted along its run

The loader (`Loader.D`, an abstract state of `WComp.code`) polls the `kv_empty` barrier of slot
`i % 3` once successfully per iteration `i`, `i = np, …, n - 1`, where `np` is the first word it
reads (`num_pre`) and `n` the second. `Ld.polled d` is the number of iterations whose poll has
succeeded when the loader is at state `d` (`d.i`, plus one at the sites after the `wait` of the
iteration `d.i`); `below s i` is the number of blocks `i' < i` of slot `s`.

* `ld_next`: a step of the loader, from a state of the loop (everything after the two loads), stays
  in the loop and raises `polled` exactly when the event is a successful poll at the `wait` site.
* `ld_okPoll`: the event that fires at a state of the loop is a successful poll of `kv_empty s` of
  the thread's CTA exactly when the state is the `wait` site of an iteration of slot `s` and the
  event is a successful poll (`LdShape`).
* `loader_polls`: along a run of the machine from a loop state `d₀` to `d` that stays in the loop,
  the successful polls of `kv_empty s` number `below s (polled d) - below s (polled d₀)`.
* `loader_wait`: **(a) for the loader.** At the `wait` site, with `np = polled d₀ ≤ 3` (`d₀`
  the state after the loads, `np = num_pre`), the event is the poll of `kv_empty (d.i % 3)` with
  parity `emptyParity d.i`, the poll is for the loader's `n`-th block of the slot
  (`d.i = loaderBlock np s n`, `n` the polls of that barrier made before), and its parity is
  `(n + δ) % 2`, `δ = 0` if `s < np` and `1` otherwise: exactly the alternation
  `MBarrier.Alternates` of a poller whose first poll passes on the fresh barrier (`δ = 1`) or
  waits for phase 0 (`δ = 0`).

The run is relative: it starts at a loop state and stays in the loop. That the thread's whole
trace is one such run, from the state `bar0` after its loads, is the role-table protocol
(obligation 6): the worker enters the loader once, and before that no event polls `kv_empty`
(`Ring.lean`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Ring
open PTX PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.EvW (kvEmpty LdShape MapReg loader_shape)

noncomputable section
set_option maxRecDepth 100000

/-- The sites of an iteration after its `wait`. -/
def Ld.afterWait : Loader.Site → Bool
  | .setMaxDec | .ld0 | .ld1 | .bar0 | .wait | .bar1 | .setMaxInc => false
  | _ => true

/-- The iterations whose `kv_empty` poll has succeeded at state `d`. -/
def Ld.polled (d : Loader.D) : Nat := d.i + if Ld.afterWait d.site then 1 else 0

/-- The states of the loop: after the two loads of `(num_pre, num_iters)`, with the counter
bounds (`Loader.Rng`: the machine follows every loaded word; a consistent execution gives the
bounds, `Interface.LdRng`). -/
def Ld.InLoop (d : Loader.D) : Prop :=
  d.site ≠ .setMaxDec ∧ d.site ≠ .ld0 ∧ d.site ≠ .ld1 ∧ Loader.Rng d

/-- A step of the loader from a state of the loop stays in the loop. -/
theorem Ld.inLoop_next {L : Launch} {g : Nat} {d d' : Loader.D} {e : Event} (hd : Ld.InLoop d)
    (h : Loader.next L g d e = some (some d')) : Ld.InLoop d' := by
  obtain ⟨h1, h2, h3, hr⟩ := hd
  refine ⟨?_, ?_, ?_, hr.next h2 h3 h⟩ <;>
  · obtain ⟨site, pro, i, n, p0, p1, ln⟩ := d
    cases site <;> simp only [Loader.next, Loader.afterIter] at h <;> (repeat' split at h) <;>
      simp only [Option.some.injEq, reduceCtorEq] at h <;> (try subst h) <;> simp_all

/-- In the loop the counter's increment does not wrap. -/
theorem Ld.mod_of_loop {d : Loader.D} (hd : Ld.InLoop d) :
    d.site.inLoop = true → (d.i + 1) % 2 ^ 32 = d.i + 1 := fun hl => by
  have h := hd.2.2.2.bndI (by
    obtain ⟨site, pro, i, n, p0, p1, ln⟩ := d
    cases site <;> simp_all [Loader.Site.iBounded, Loader.Site.bounded, Loader.Site.inLoop])
  exact Nat.mod_eq_of_lt (by omega)

/-- The blocks `i' < i` in slot `s` (`s < 3`). -/
def below (s i : Nat) : Nat := (i + 2 - s) / 3

/-- Whether an event is a successful poll. -/
def okW (e : Event) : Bool := match e.kind with | .wait _ _ ok _ _ => ok | _ => false

/-- **A step of the loader.** -/
theorem ld_next {L : Launch} {g : Nat} {d d' : Loader.D} {e : Event} (hd : Ld.InLoop d)
    (h : Loader.next L g d e = some (some d')) :
    Ld.InLoop d' ∧
      Ld.polled d' = Ld.polled d + if d.site = .wait ∧ okW e = true then 1 else 0 := by
  refine ⟨Ld.inLoop_next hd h, ?_⟩
  have hm := Ld.mod_of_loop hd
  obtain ⟨site, pro, i, n, p0, p1, ln⟩ := d
  obtain ⟨h1, h2, h3, -⟩ := hd
  simp only at h1 h2 h3 hm
  cases site
  case setMaxDec => exact absurd rfl h1
  case ld0 => exact absurd rfl h2
  case ld1 => exact absurd rfl h3
  all_goals
    simp only [Loader.next] at h
    (repeat' split at h)
    all_goals first
      | (obtain rfl := Option.some.inj (Option.some.inj h)
         simp_all [Ld.polled, Ld.afterWait, Loader.afterIter, okW, Loader.Site.inLoop]
         all_goals split
         all_goals simp_all)
      | cases h

theorem below_succ {s i : Nat} (hs : s < 3) :
    below s (i + 1) = below s i + if i % 3 = s then 1 else 0 := by
  unfold below
  split <;> omega

theorem below_small {s np : Nat} (hs : s < 3) (hnp : np ≤ 3) :
    below s np = if s < np then 1 else 0 := by
  unfold below
  split <;> omega

theorem below_of_slot {s i : Nat} (hs : s < 3) (hi : i % 3 = s) : below s i = i / 3 := by
  unfold below
  omega

/-- The location of `kv_empty s` is injective in `s`. -/
theorem kvEmpty_inj {L : Launch} {c s s' : Nat} (h : kvEmpty L c s = kvEmpty L c s') :
    s = s' := by
  simp only [kvEmpty, EvW.barLoc, EvW.kvEmptyOff, Loc.mk.injEq] at h
  omega

theorem kvEmpty_eq_iff {L : Launch} {c s s' : Nat} : kvEmpty L c s = kvEmpty L c s' ↔ s = s' :=
  ⟨kvEmpty_inj, fun h => h ▸ rfl⟩

variable {Q : Params} {L : Launch} {g : Nat} {mem0 : Mem0} {u : TState} {e : Event}

theorem ld_okPoll (hpre : Pre Q L mem0) {d : Loader.D} {P : Loader.Pro} (hmap : MapReg P)
    (hrg : Loader.Rng d)
    (hF : (WComp.code L g Q).toMachine.Fired (some (.loader d P)) e (some u)) (s : Nat) :
    okPoll (kvEmpty L (g / L.block) s) e =
      (decide (d.site = .wait ∧ d.i % 3 = s) && okW e) := by
  have hsh := loader_shape hpre hmap hrg hF
  obtain ⟨site, pro, i, n, p0, p1, ln⟩ := d
  cases site <;> simp only [LdShape] at hsh
  case wait =>
    obtain ⟨ok, rfl⟩ := hsh
    cases ok <;> simp [okPoll, sourceWaitSuccess, okW, kvEmpty_eq_iff]
  all_goals first
    | (obtain ⟨_, rfl⟩ := hsh; simp [okPoll, sourceWaitSuccess, okW])
    | (obtain ⟨_, _, rfl, -⟩ := hsh; simp [okPoll, sourceWaitSuccess, okW])

/-- The event of a step: a loader event that fires, or an event that ends the thread. -/
theorem ld_okPoll_step (hpre : Pre Q L mem0) {d : Loader.D} {P : Loader.Pro} (hmap : MapReg P)
    (hrg : Loader.Rng d)
    (hev : (∃ u, (WComp.code L g Q).toMachine.Fired (some (.loader d P)) e (some u)) ∨ Ends e)
    (s : Nat) :
    okPoll (kvEmpty L (g / L.block) s) e =
      (decide (d.site = .wait ∧ d.i % 3 = s) && okW e) := by
  rcases hev with ⟨u, hF⟩ | hend
  · exact ld_okPoll hpre hmap hrg hF s
  · obtain ⟨pc, k⟩ := e
    have hk : ∀ l p ok acq sc, k ≠ Kind.wait l p ok acq sc := by
      rcases hend with ⟨f, h⟩ | h <;> intro l p ok acq sc hh <;> simp only at h <;> subst h <;>
        cases hh
    have h1 : okPoll (kvEmpty L (g / L.block) s) ⟨pc, k⟩ = false :=
      okPoll_notWait (fun l p ok acq sc h => hk l p ok acq sc h)
    have h2 : okW ⟨pc, k⟩ = false := by
      cases k <;> first | rfl | exact absurd rfl (hk _ _ _ _ _)
    rw [h1, h2]
    simp

variable (hpre : Pre Q L mem0) {P : Loader.Pro} (hmap : MapReg P) {d0 : Loader.D} {es : List Event}
    (hT : (WComp.code L g Q).toMachine.Trace (some (.loader d0 P)) es)
    (hin : ∀ j < es.length, ∃ d, (WComp.code L g Q).toMachine.after (some (.loader d0 P))
      (es.take j) = some (some (.loader d P)) ∧ Ld.InLoop d ∧ d.site ≠ .setMaxInc) {d : Loader.D}
    (hd : (WComp.code L g Q).toMachine.after (some (.loader d0 P)) es = some (some (.loader d P)))
include hpre hmap hT hin hd

/-- **The loader's polls along a run.** -/
theorem loader_polls (s : Nat) (hs : s < 3) :
    okPolls (kvEmpty L (g / L.block) s) es + below s (Ld.polled d0) = below s (Ld.polled d) := by
  have h := count_trace (M := (WComp.code L g Q).toMachine) (okPoll (kvEmpty L (g / L.block) s))
    (fun σ => match σ with | some (.loader d _) => below s (Ld.polled d) | _ => 0)
    (fun σ => ∃ d, σ = some (.loader d P) ∧ Ld.InLoop d ∧ d.site ≠ .setMaxInc)
    (fun _ => True) (some (.loader d P)) ?_ hT (fun _ _ => trivial) ?_ hd
  · exact h
  · rintro σ e σ' ⟨d1, rfl, hin1, hne⟩ - hev hn hσ'
    have hn' : WComp.next L g (.loader d1 P) e = some σ' := hn
    rw [EvW.next_loader_map P hne] at hn'
    cases σ' with
    | none => rcases hσ' with ⟨_, h, _⟩ | h <;> cases h
    | some σ'' =>
      obtain ⟨a, ha, hfa⟩ := EvW.map_map_some hn'
      subst hfa
      obtain ⟨-, hpol⟩ := ld_next hin1 ha
      have hokp := ld_okPoll_step hpre hmap hin1.2.2.2 hev s
      show below s (Ld.polled a) = below s (Ld.polled d1) + if okPoll _ e = true then 1 else 0
      rw [hokp, hpol]
      by_cases hw : d1.site = .wait
      · have hp : Ld.polled d1 = d1.i := by simp [Ld.polled, Ld.afterWait, hw]
        by_cases hok : okW e = true
        · by_cases hm : d1.i % 3 = s
          · simp [hw, hok, hm, hp, below_succ hs]
          · simp [hw, hok, hm, hp, below_succ hs]
        · simp [hw, hok]
      · simp [hw]
  · intro j hj
    obtain ⟨d1, h1, h2, h3⟩ := hin j hj
    exact ⟨_, h1, d1, rfl, h2, h3⟩


/-- **The loader's `wait` event, with its place in the ring.** At the `wait` site, the event is the
poll of `kv_empty (d.i % 3)` with parity `emptyParity d.i`; the polls of that barrier it has made
since the loop state `d0` (the `n` earlier ones) put block `d.i` at the loader's `n`-th block of the
slot: `d.i = loaderBlock np s n`, with `np = polled d0` (the blocks the prologue preloaded when `d0`
is the state after the loads), and the poll's parity is `(n + δ) % 2`. -/
theorem loader_wait (hrg : Loader.Rng d) (hnp : Ld.polled d0 ≤ 3) (hw : d.site = .wait)
    (hF : (WComp.code L g Q).toMachine.Fired (some (.loader d P)) e (some u)) :
    ∃ ok, e = ⟨Loader.Site.wait.pc, .wait (kvEmpty L (g / L.block) (d.i % 3))
        (emptyParity d.i) ok true .cta⟩ ∧
      d.i = loaderBlock (Ld.polled d0) (d.i % 3)
        (okPolls (kvEmpty L (g / L.block) (d.i % 3)) es) ∧
      emptyParity d.i % 2 = (okPolls (kvEmpty L (g / L.block) (d.i % 3)) es +
        if d.i % 3 < Ld.polled d0 then 0 else 1) % 2 := by
  have hsh := loader_shape hpre hmap hrg hF
  have hcount := loader_polls hpre hmap hT hin hd (d.i % 3) (by omega)
  obtain ⟨site, pro, i, n, p0, p1, ln⟩ := d
  simp only at hw
  subst hw
  simp only [LdShape] at hsh
  obtain ⟨ok, rfl⟩ := hsh
  have hpd : Ld.polled ⟨.wait, pro, i, n, p0, p1, ln⟩ = i := by simp [Ld.polled, Ld.afterWait]
  rw [hpd, below_of_slot (by omega) rfl, below_small (by omega) hnp] at hcount
  refine ⟨ok, rfl, ?_, ?_⟩
  · unfold loaderBlock loaderUse blockOf
    split at hcount <;> split <;> omega
  · unfold emptyParity use
    split at hcount <;> split <;> omega

end
end PTX.Kernels.InklingRelDecode.Proof.Ring
