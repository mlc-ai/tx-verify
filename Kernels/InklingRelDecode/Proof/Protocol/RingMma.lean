-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.RingLoader

@[expose] public section

/-!
# The MMA warp's polls of `kv_ready`, counted along its run

The MMA warp (`Mma.D`, an abstract state of `WComp.code`) polls `kv_ready` of slot `i % 3` once
successfully for each block `i < n`, in the QK half of iteration `i`. `Mm.polled d` is the number
of QK halves whose poll has succeeded at state `d`: `d.i` before the poll of iteration `d.i`,
`d.i + 1` in the rest of its QK half, and `min (d.i + 1) n` in its PV half (the QK half of
iteration `n` does not exist), and `n` at the end sites of a loop that ran (`0` if it did not).

* `mm_next`: a step of the MMA warp (from a state with `Mma.Inv`) raises `polled` exactly at a
  successful `kvWait`.
* `mm_okPoll`: the event that fires at an MMA state is a successful poll of `kv_ready s`
  exactly at the `kvWait` site of an iteration of slot `s` (`MmShape`; the PV half polls
  `p_ready`, another barrier).
* `mma_polls`: along a run that stays in the role (and keeps `Mma.Inv`), the successful polls of
  `kv_ready s` number `below s (polled d) - below s (polled d₀)`.
* `mma_wait`: **(a) for the MMA warp.** At the `kvWait` site, in a run from the start of the loop,
  the event is the poll of `kv_ready (d.i % 3)` with parity `readyParity d.i`, it is for the
  warp's `n`-th block of the slot (`d.i = blockOf s n`, `n` the polls of that barrier made before),
  and its parity is `n % 2`: the alternation of a poller whose `n`-th poll waits for phase `n`.

As for the loader, the run is relative and stays in the role; the thread's whole trace is one
such run under the role-table protocol (`Ring.lean`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Ring
open PTX PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.EvW (kvReady MmShape mma_shape)
open PTX.Kernels.InklingRelDecode.Proof.EvW (QkIssue PvIssue)

noncomputable section
set_option maxRecDepth 100000

/-- The QK halves whose `kv_ready` poll has succeeded at state `d`. -/
def Mm.polled (d : Mma.D) : Nat :=
  match d.site with
  | .setMaxReg | .ldNum | .bar0 => 0
  | .qkBar | .kvWait => d.i
  | .qkShfl | .qkBar2 | .qkElect | .qk _ | .qkCommit | .qkSkip => d.i + 1
  | .pvBar | .pWait | .pvShfl | .pvBar2 | .pvElect | .pv _ | .pvCommit1 | .pvCommit2 | .pvSkip =>
    min (d.i + 1) d.n
  | .finBar | .finElect | .finCommit | .bar1 | .setMaxRegInc => if d.i = 0 then 0 else d.n

/-- **A step of the MMA warp.** -/
theorem mm_next {L : Launch} {g : Nat} {d d' : Mma.D} {e : Event} (hi : Mma.Inv d)
    (hne : d.site ≠ .setMaxRegInc) (h : Mma.next L g d e = some (some d')) :
    Mm.polled d' = Mm.polled d + if d.site = .kvWait ∧ okW e = true then 1 else 0 := by
  have hq := hi.qk
  have hp := hi.pv
  have hpre := hi.pre
  obtain ⟨site, i, n, tm, pro⟩ := d
  simp only [Mma.QkSite, Mma.PvSite, Mma.PreSite] at hq hp hpre
  simp only at hne
  cases site
  case setMaxRegInc => exact absurd rfl hne
  all_goals
    simp only [Mma.next] at h
    (repeat' split at h)
    all_goals try (obtain rfl := Option.some.inj (Option.some.inj h))
    all_goals try (cases h)
    all_goals try simp only [Mma.start, Mma.afterQk, Mma.iterNext, Mma.qkNext, Mma.pvNext]
    all_goals (repeat' split)
    all_goals simp_all [Mm.polled, okW]
    all_goals omega

theorem kvReady_inj {L : Launch} {c s s' : Nat} (h : kvReady L c s = kvReady L c s') :
    s = s' := by
  simp only [kvReady, EvW.barLoc, EvW.kvReadyOff, Loc.mk.injEq] at h
  omega

theorem kvReady_eq_iff {L : Launch} {c s s' : Nat} : kvReady L c s = kvReady L c s' ↔ s = s' :=
  ⟨kvReady_inj, fun h => h ▸ rfl⟩

theorem pReady_ne_kvReady {L : Launch} {c b s : Nat} (hs : s < 3) :
    EvW.pReady L c b ≠ kvReady L c s := by
  simp only [EvW.pReady, kvReady, EvW.barLoc, EvW.pReadyOff, EvW.kvReadyOff, ne_eq, Loc.mk.injEq]
  omega

variable {Q : Params} {L : Launch} {g : Nat} {mem0 : Mem0} {u : TState} {e : Event}

theorem mm_okPoll (hpre : Pre Q L mem0) (hg : g < L.threads) {d : Mma.D} {P : Loader.Pro}
    (hF : (WComp.code L g Q).toMachine.Fired (some (.mma d P)) e (some u)) {s : Nat}
    (hs : s < 3) :
    okPoll (kvReady L (g / L.block) s) e =
      (decide (d.site = .kvWait ∧ d.i % 3 = s) && okW e) := by
  have hsh := mma_shape hpre hg hF
  obtain ⟨site, i, n, tm, pro⟩ := d
  cases site <;> simp only [MmShape] at hsh
  case kvWait =>
    obtain ⟨ok, rfl⟩ := hsh
    cases ok <;> simp [okPoll, sourceWaitSuccess, okW, kvReady_eq_iff]
  case pWait =>
    obtain ⟨ok, rfl⟩ := hsh
    cases ok <;> simp [okPoll, sourceWaitSuccess, okW, pReady_ne_kvReady hs]
  all_goals first
    | obtain ⟨_, _, rfl, -⟩ := hsh
    | obtain ⟨_, _, rfl⟩ := hsh
    | obtain ⟨_, rfl⟩ := hsh
    | obtain rfl := hsh
    | obtain ⟨_, _, _, _, _, _, rfl⟩ := hsh
  all_goals simp [okPoll, sourceWaitSuccess, okW]

/-- The event of a step: an MMA event that fires, or an event that ends the thread. -/
theorem mm_okPoll_step (hpre : Pre Q L mem0) (hg : g < L.threads) {d : Mma.D} {P : Loader.Pro}
    (hev : (∃ u, (WComp.code L g Q).toMachine.Fired (some (.mma d P)) e (some u)) ∨ Ends e)
    {s : Nat} (hs : s < 3) :
    okPoll (kvReady L (g / L.block) s) e =
      (decide (d.site = .kvWait ∧ d.i % 3 = s) && okW e) := by
  rcases hev with ⟨u, hF⟩ | hend
  · exact mm_okPoll hpre hg hF hs
  · obtain ⟨pc, k⟩ := e
    have hk : ∀ l p ok acq sc, k ≠ Kind.wait l p ok acq sc := by
      rcases hend with ⟨f, h⟩ | h <;> intro l p ok acq sc hh <;> simp only at h <;> subst h <;>
        cases hh
    have h1 : okPoll (kvReady L (g / L.block) s) ⟨pc, k⟩ = false :=
      okPoll_notWait (fun l p ok acq sc h => hk l p ok acq sc h)
    have h2 : okW ⟨pc, k⟩ = false := by
      cases k <;> first | rfl | exact absurd rfl (hk _ _ _ _ _)
    rw [h1, h2]
    simp

variable (hpre : Pre Q L mem0) (hg : g < L.threads) {P : Loader.Pro} {d0 : Mma.D} {es : List Event}
    (hT : (WComp.code L g Q).toMachine.Trace (some (.mma d0 P)) es)
    (hin : ∀ j < es.length, ∃ d, (WComp.code L g Q).toMachine.after (some (.mma d0 P))
      (es.take j) = some (some (.mma d P)) ∧ Mma.Inv d ∧ d.site ≠ .setMaxRegInc) {d : Mma.D}
    (hd : (WComp.code L g Q).toMachine.after (some (.mma d0 P)) es = some (some (.mma d P)))
include hpre hg hT hin hd

/-- **The MMA warp's polls along a run.** -/
theorem mma_polls {s : Nat} (hs : s < 3) :
    okPolls (kvReady L (g / L.block) s) es + below s (Mm.polled d0) = below s (Mm.polled d) := by
  have h := count_trace (M := (WComp.code L g Q).toMachine) (okPoll (kvReady L (g / L.block) s))
    (fun σ => match σ with | some (.mma d _) => below s (Mm.polled d) | _ => 0)
    (fun σ => ∃ d, σ = some (.mma d P) ∧ Mma.Inv d ∧ d.site ≠ .setMaxRegInc)
    (fun _ => True) (some (.mma d P)) ?_ hT (fun _ _ => trivial) ?_ hd
  · exact h
  · rintro σ e σ' ⟨d1, rfl, hin1, hne⟩ - hev hn hσ'
    have hn' : WComp.next L g (.mma d1 P) e = some σ' := hn
    rw [EvW.next_mma_map P hne] at hn'
    cases σ' with
    | none => rcases hσ' with ⟨_, h, _⟩ | h <;> cases h
    | some σ'' =>
      obtain ⟨a, ha, hfa⟩ := EvW.map_map_some hn'
      subst hfa
      have hpol := mm_next hin1 hne ha
      have hokp := mm_okPoll_step hpre hg hev hs
      show below s (Mm.polled a) = below s (Mm.polled d1) + if okPoll _ e = true then 1 else 0
      rw [hokp, hpol]
      by_cases hw : d1.site = .kvWait
      · have hp : Mm.polled d1 = d1.i := by simp [Mm.polled, hw]
        by_cases hok : okW e = true
        · by_cases hm : d1.i % 3 = s
          · simp [hw, hok, hm, hp, below_succ hs]
          · simp [hw, hok, hm, hp, below_succ hs]
        · simp [hw, hok]
      · simp [hw]
  · intro j hj
    obtain ⟨d1, h1, h2, h3⟩ := hin j hj
    exact ⟨_, h1, d1, rfl, h2, h3⟩

/-- **The MMA warp's `kv_ready` poll, with its place in the ring.** At the `kvWait` site, in a run
from the start of the loop (`polled d₀ = 0`), the event is the poll of `kv_ready (d.i % 3)` with
parity `readyParity d.i`, it is for the warp's `n`-th block of the slot (`d.i = blockOf s n`, `n`
the polls of that barrier made before), and its parity is `n % 2`. -/
theorem mma_wait (h0 : Mm.polled d0 = 0) (hw : d.site = .kvWait)
    (hF : (WComp.code L g Q).toMachine.Fired (some (.mma d P)) e (some u)) :
    ∃ ok, e = ⟨Mma.Site.kvWait.pc, .wait (kvReady L (g / L.block) (d.i % 3))
        (readyParity d.i) ok true .cta⟩ ∧
      d.i = blockOf (d.i % 3) (okPolls (kvReady L (g / L.block) (d.i % 3)) es) ∧
      readyParity d.i = okPolls (kvReady L (g / L.block) (d.i % 3)) es % 2 := by
  have hsh := mma_shape hpre hg hF
  have hcount := mma_polls hpre hg hT hin hd (s := d.i % 3) (by omega)
  obtain ⟨site, i, n, tm, pro⟩ := d
  simp only at hw
  subst hw
  simp only [MmShape] at hsh
  obtain ⟨ok, rfl⟩ := hsh
  have hpd : Mm.polled ⟨.kvWait, i, n, tm, pro⟩ = i := by simp [Mm.polled]
  rw [hpd, h0, below_of_slot (by omega) rfl] at hcount
  refine ⟨ok, rfl, ?_, ?_⟩
  · unfold blockOf
    unfold below at hcount
    omega
  · unfold readyParity use
    unfold below at hcount
    omega

end
end PTX.Kernels.InklingRelDecode.Proof.Ring
