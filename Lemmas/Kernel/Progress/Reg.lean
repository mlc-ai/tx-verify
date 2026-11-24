-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.Progress.Blocked
public import Lemmas.Kernel.Progress.Rank
public import Lemmas.Kernel.Goals
public import Lemmas.Step.SetMaxNReg

@[expose] public section

/-! # Progress at a register request

A proof tool, generic over the kernel (promoted from FA4's `Proof/Progress/CollectiveReg.lean`).
A pending thread whose last event is a `setmaxnreg` that not every lane of its warp has matched
(`RegWait`, DEP-SETMAXNREG-RENDEZVOUS) steps (`Sched.reg_steps`). In a safe execution some lane
of the warp has no matching request (`Step.missing_member_lane`). When two requests of lanes of
one warp match (`RegMatch`), that lane has made no request at all, and when every exit follows a
request (`RegExit`) it has not exited: it is pending. The time table places a thread without a
request no later than a time `T` and a thread after its request later than `T`, so the lane is
earlier than the blocked thread. The kernel gives the two matching facts (from its safety layer)
and the two time facts (from its time table). -/

namespace PTX.Sched

open PTX

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0} {M : Timed K A L}
  {X : Execution}

/-- Two register requests of lanes of one warp match. -/
def RegMatch (L : Launch) (X : Execution) : Prop :=
  ∀ {e f : EvId} {pc pc' n n' inst inst' : Nat} {inc inc' : Bool}, e.1 < L.threads →
    f.1 < L.threads → SameWarp L e.1 f.1 → SetMaxNReg.Request X e pc inc n inst →
    SetMaxNReg.Request X f pc' inc' n' inst' → SetMaxNReg.SameRequest L X e f

/-- A thread exits after its register request. -/
def RegExit (L : Launch) (X : Execution) : Prop :=
  ∀ {h k pc : Nat}, h < L.threads → X.get (h, k) = some ⟨pc, .exit⟩ →
    1 ≤ SetMaxNReg.ordinal X (h, k)

/-- **A thread of the warp of `g` in a given lane**, when the block is a whole number of warps. -/
theorem warp_mate (hb : L.block % 32 = 0) {g : Nat} (hg : g < L.threads) {lane : Nat}
    (hl : lane < 32) : ∃ h, h < L.threads ∧ SameWarp L g h ∧ laneOf L h = lane := by
  have hB : 0 < L.block := by
    rcases Nat.eq_zero_or_pos L.block with h0 | h0
    · simp only [Launch.threads, h0, Nat.mul_zero] at hg; omega
    · exact h0
  have hgr := Nat.div_add_mod' g L.block
  have hr := Nat.mod_lt g hB
  have hq : g / L.block < L.grid := (Nat.div_lt_iff_lt_mul hB).mpr hg
  set q := g / L.block
  set r := g % L.block
  have hs : r / 32 * 32 + lane < L.block := by omega
  have hd : (r / 32 * 32 + lane + q * L.block) / L.block = q := by
    rw [Nat.add_mul_div_right _ _ hB, Nat.div_eq_of_lt hs, Nat.zero_add]
  have hm : (r / 32 * 32 + lane + q * L.block) % L.block = r / 32 * 32 + lane := by
    rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hs]
  have hlt : r / 32 * 32 + lane + q * L.block < L.threads := by
    have := Nat.mul_le_mul_right L.block (show q + 1 ≤ L.grid by omega)
    rw [Nat.succ_mul] at this
    simp only [Launch.threads]
    omega
  refine ⟨r / 32 * 32 + lane + q * L.block, hlt, ⟨⟨hg, hlt, hd.symm⟩, ?_⟩, ?_⟩
  · rw [hm]; omega
  · simp only [laneOf, hm]; omega

/-- A thread whose events before `k` count a register request has a request event. -/
theorem request_of_ordinal {h k : Nat} (hk : 1 ≤ SetMaxNReg.ordinal X (h, k)) :
    ∃ j pc inc n inst, X.get (h, j) = some ⟨pc, .setMaxReg inc n inst⟩ := by
  unfold SetMaxNReg.ordinal at hk
  obtain ⟨e, he, hp⟩ := List.countP_pos_iff.mp (Nat.lt_of_lt_of_le Nat.zero_lt_one hk)
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp (List.mem_of_mem_take he)
  obtain ⟨pc, kind⟩ := e
  cases kind with
  | setMaxReg inc n inst => exact ⟨j, pc, inc, n, inst, hj⟩
  | _ => simp [SetMaxNReg.isRequest] at hp

/-- **Progress at a register request.** A pending thread whose last event is a register request
that not every lane of its warp has matched steps: a lane with no request is pending and
earlier. -/
theorem reg_steps (hs : SafeGoal K A L mem0) (hmatch : RegMatch L X) (hexit : RegExit L X)
    (hb : L.block % 32 = 0) {T : Nat}
    (hbefore : ∀ {h : Nat}, h < L.threads →
      (∀ j pc inc n inst, X.get (h, j) ≠ some ⟨pc, .setMaxReg inc n inst⟩) →
      threadTime M X h ≤ T)
    (hafter : ∀ {g k pc n inst : Nat} {inc : Bool}, g < L.threads →
      X.get (g, k) = some ⟨pc, .setMaxReg inc n inst⟩ →
      ∃ d, Frame.stateAt M.code X g (k + 1) = some (some d) ∧ T < M.time g d)
    (hmax : Maximal L K A mem0 X) {g : Nat} (hp : Frame.Pending L X g)
    (hrel : ¬ Step.Released L X g) (hrw : RegWait L X g) : Steps M mem0 X (.thread g) := by
  obtain ⟨pc, inc, n, inst, hreq, hm⟩ := hrw
  have hX := hmax.1
  have hg := hp.1
  have hlast : X.get (g, (X.tr g).length - 1) = some ⟨pc, .setMaxReg inc n inst⟩ := hreq
  have hlen : 0 < (X.tr g).length := by
    have : (X.tr g).length - 1 < (X.tr g).length := len_of_get hlast
    omega
  have hne : X.tr g ≠ [] := List.ne_nil_of_length_pos hlen
  obtain ⟨dg, hσg, hgt⟩ := hafter hg hlast
  rw [Nat.sub_add_cancel hlen] at hσg
  obtain ⟨lane, hl, hmiss⟩ := Step.missing_member_lane (hs.2 X hX) hreq hm
  obtain ⟨h, hh, hwh, hlane⟩ := warp_mate hb hg hl
  obtain ⟨hno, -⟩ := hmiss h hh hwh hlane
  -- the lane has made no request: a request of it would match `g`'s
  have hnoreq : ∀ j pc' inc' n' inst', X.get (h, j) ≠ some ⟨pc', .setMaxReg inc' n' inst'⟩ := by
    intro j pc' inc' n' inst' hj
    exact hno j (hmatch (e := (g, _)) (f := (h, j)) hg hh hwh hreq hj)
  have hnx : ∀ j pc', X.get (h, j) ≠ some ⟨pc', .exit⟩ := by
    intro j pc' hj
    obtain ⟨j', pc'', inc', n', inst', hj'⟩ := request_of_ordinal (hexit hh hj)
    exact hnoreq j' pc'' inc' n' inst' hj'
  have hph := pending_of_noExit hX hg hne hh (cluster_of_sameWarp hwh) hnx
  refine earlier_steps hmax hrel hph ?_
  have h1 := hbefore hh hnoreq
  rw [threadTime_of hσg]
  omega

end

end PTX.Sched
