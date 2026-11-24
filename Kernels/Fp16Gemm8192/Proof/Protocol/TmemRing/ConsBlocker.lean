-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Protocol.TmemRing.Bounds
public import Lemmas.Protocol.MbarRingBlocker
public import Lemmas.Protocol.RecordCount
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-! # Who blocks a consumer at its accumulator-full wait

A consumer of accumulator buffer `j` polls its CTA's full barrier of the buffer before each tile
(`Consumer.Site.accWait`). A failed poll whose phase has the poll's parity finds the barrier at
phase `T`, where `T` is the consumer's successful polls on it (`cons_phase`): the barrier's phase is
at most `T + 1` (`full_phase_le`) and at least the phase its latest successful poll found
(`cons_poll_phase`), and the poll's parity excludes `T + 1`. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow MBarrier AsyncCopy

noncomputable section

namespace TmemRing

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **The phase of a consumer's failed accumulator-full poll.** A consumer thread `g` of buffer `j`
in cluster `c`, whose CTA is the `k`-th of the cluster, stopped at a failed poll of its CTA's full
barrier of the buffer, whose phase has the poll's parity: the barrier's phase is its successful
polls on it. -/
theorem cons_phase (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X)
    {g : Nat} (hg : g < L.threads) {c : Nat} {j k : Fin 2}
    (hc : g / L.block / 2 = c) (hw : g % L.block / 32 / 4 = j.val)
    (hk : g / L.block = 2 * c + k.val)
    {d : ThreadD} {pc p : Nat} {acq : Bool} {sc : MbarScope}
    (hσp : Frame.stateAt (code L) X g ((X.tr g).length - 1) = some (some d))
    (hlast : (X.tr g).getLast? = some
      ⟨pc, .wait (Bar.loc L (g / L.block) ⟨.acc, j.val, true⟩) p false acq sc⟩)
    {before : State}
    (hstate : stateBefore (X.objects (Bar.loc L (g / L.block) ⟨.acc, j.val, true⟩))
      (X.objects (Bar.loc L (g / L.block) ⟨.acc, j.val, true⟩)).length = some before)
    (hpar : before.phase % 2 = p % 2) :
    before.phase = okPolls (Bar.loc L (g / L.block) ⟨.acc, j.val, true⟩) (X.tr g) := by
  have hblock := hpre.block
  -- the consumer of buffer `j` in thread `g`'s position
  set b : Fin 256 := ⟨(g / L.block - 2 * c) * 128 + g % L.block % 128, by omega⟩ with hbdef
  have hgb : consumerOf L c j b = g := consumerOf_of hc hw
  have hown : (slot L c j).owner b = k := Fin.ext (by simp only [slot, hbdef]; omega)
  have hF : (slot L c j).full ((slot L c j).owner b) =
      Bar.loc L (g / L.block) ⟨.acc, j.val, true⟩ := by
    rw [hown]
    show Bar.loc L (2 * c + k.val) ⟨.acc, j.val, true⟩ = _
    rw [← hk]
  rw [← hF] at hlast hstate ⊢
  rw [← hgb] at hlast hσp ⊢
  have hch := X.objects_checked hX ((slot L c j).full ((slot L c j).owner b))
  have hni := objects_noInval hX ht ((slot L c j).full ((slot L c j).owner b))
  -- the failed poll is the last event, after the successful polls `ys`
  obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.mp hlast
  have hlen : (X.tr (consumerOf L c j b)).length - 1 = ys.length := by
    rw [hys]
    simp
  have htake : (X.tr (consumerOf L c j b)).take ((X.tr (consumerOf L c j b)).length - 1) = ys := by
    rw [hlen, hys, List.take_left' rfl]
  have hok : okPolls ((slot L c j).full ((slot L c j).owner b)) (X.tr (consumerOf L c j b)) =
      okPolls ((slot L c j).full ((slot L c j).owner b)) ys := by
    rw [hys, okPolls_snoc]
    simp [okPoll, sourceWaitSuccess]
  have hget : X.get (consumerOf L c j b, (X.tr (consumerOf L c j b)).length - 1) = some
      ⟨pc, .wait ((slot L c j).full ((slot L c j).owner b)) p false acq sc⟩ := by
    change (X.tr (consumerOf L c j b))[(X.tr (consumerOf L c j b)).length - 1]? = _
    rw [← List.getLast?_eq_getElem?]
    exact hlast
  have hpoll := ht.poll_parity (b := ⟨.acc, j.val, true⟩) (cta := 2 * c + b.val / 128)
    (hgb ▸ hg) hget hσp rfl j.isLt
  have hpoll' : p % 2 = okPolls ((slot L c j).full ((slot L c j).owner b))
      (X.tr (consumerOf L c j b)) % 2 := by
    rw [hok, ← htake]
    exact hpoll
  have hle := full_phase_le hpre hX ht hstate
  -- the latest successful poll found phase `T`
  have hge : okPolls ((slot L c j).full ((slot L c j).owner b)) (X.tr (consumerOf L c j b)) ≤
      before.phase := by
    rcases Nat.eq_zero_or_pos (okPolls ((slot L c j).full ((slot L c j).owner b))
      (X.tr (consumerOf L c j b))) with h0 | hpos
    · omega
    obtain ⟨k', w, hk', -, -, -, st, hst, hph⟩ := cons_poll_phase hpre hX ht (c := c) (j := j)
      (b := b)
      (t := okPolls ((slot L c j).full ((slot L c j).owner b)) (X.tr (consumerOf L c j b)) - 1)
      (by omega)
    obtain ⟨s2, hs2, hmono⟩ := hch.phase_mono hni (List.getElem?_eq_some_iff.mp hk').1.le le_rfl hst
    rw [hstate] at hs2
    cases hs2
    omega
  omega

/-- **The arrivals of a full barrier at its phase.** When the barrier is in phase `before.phase`, it
has received exactly that many notifications: each completes one phase, as the barrier's
transaction counter stays zero (`tx_zero_acc`), so one arrival is pending
(`MbarRing.Blocker.units_eq_phase`). -/
theorem full_arrivals (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X)
    {c : Nat} {j k : Fin 2} {before : State}
    (hstate : stateBefore (X.objects ((slot L c j).full k))
      (X.objects ((slot L c j).full k)).length = some before) :
    (X.objects ((slot L c j).full k)).countP isArrival = before.phase := by
  have hch := X.objects_checked hX ((slot L c j).full k)
  have hni := objects_noInval hX ht ((slot L c j).full k)
  have hexp := expected_eq (cta := 2 * c + k.val) (f := true) hpre hX ht _ before hstate
  change before.expected = 1 at hexp
  have hun : arrivalUnits (X.objects ((slot L c j).full k)) =
      (X.objects ((slot L c j).full k)).countP isArrival :=
    units_eq_isArrival (cta := 2 * c + k.val) (f := true) hX ht _ (fun r hr => hr)
  rw [← hun]
  exact MbarRing.Blocker.units_eq_phase hch hni hstate
    (tx_zero_acc (cta := 2 * c + k.val) (f := true) hX ht hstate) hexp
    (incrementsBefore_zero hX ht _)

/-- **An MMA thread's rank bound.** Outside the exit stage, an MMA thread's next event ranks at most
`blockAt N + 4160`, where `N` is its accumulator commits: its time is the block of its task
(`mmaCount / 128`, one task per 128 input commits), and the accumulator commit comes after the
task's 128 input commits, at the block of the task it commits (`Mma.vtime`). -/
theorem mma_vtime_le {m : Mma.D} {D N : Nat}
    (hN : N + (if m.site = .accCommit then 1 else 0) = D / 128) (hx : Mma.exitOff m = none) :
    Mma.vtime D m ≤ blockAt N + 4160 := by
  have hD : D % 128 < 128 := Nat.mod_lt _ (by norm_num)
  unfold Mma.vtime
  simp only [blockAt, ringAt, blockSpan]
  cases hs : m.site <;> simp [Mma.exitOff, hs] at hN hx ⊢ <;> omega

/-- **Commits leave notifications on the accumulator-full barrier.** With every commit notified,
the accumulator commits of MMA thread `h` to its leader CTA's buffer-`j` full barrier are at most
the notifications on the full barrier of CTA `h / L.block + a`, for either CTA `a` of the cluster.
Each commit notifies both CTAs (`htarget`, the commit's target by rank), and its notification is a
record of its own identity in the barrier's history. -/
theorem commits_counted_acc (hobj : ObjectsOk X) {j : Fin 2}
    (htarget : ∀ (h k pc : Nat) (sp : TcCommit.Spec) (r : Fin 16), h < L.threads →
      X.get (h, k) = some ⟨pc, .tc (.commit sp)⟩ →
      sp.mbar = Bar.loc L (h / L.block) ⟨.acc, j.val, true⟩ → r.val < 2 →
      TcCommit.target sp r = some (Bar.loc L (h / L.block + r.val) ⟨.acc, j.val, true⟩))
    (hall : ∀ i sp rank m, X.Commit i sp → TcCommit.target sp rank = some m →
      rank ∈ X.tcNotified i)
    {h : Nat} (hh : h < L.threads) (a : Fin 2) :
    (X.tr h).countP (commitsTo (Bar.loc L (h / L.block) ⟨.acc, j.val, true⟩)) ≤
      (X.objects (Bar.loc L (h / L.block + a.val) ⟨.acc, j.val, true⟩)).countP isNotify := by
  let rank : Fin 16 := ⟨a.val, by omega⟩
  refine countP_le_of_records (fun k => Ref.async (h, k) (.tcNotify rank)) ?_ ?_
  · intro i i' _ _ hij
    simp only [Ref.async.injEq, Prod.mk.injEq] at hij
    exact hij.1.2
  · intro k hk
    simp only [indicesP, Finset.mem_filter, Finset.mem_range] at hk
    obtain ⟨hlt, hp⟩ := hk
    obtain ⟨e, he⟩ : ∃ e, (X.tr h)[k]? = some e := ⟨_, List.getElem?_eq_getElem hlt⟩
    rw [he] at hp
    simp only [Option.map_some, Option.getD_some] at hp
    obtain ⟨pc, ek⟩ := e
    cases ek with
    | tc op =>
      cases op with
      | commit sp =>
        have hmb : sp.mbar = Bar.loc L (h / L.block) ⟨.acc, j.val, true⟩ := by
          simpa [commitsTo] using hp
        have hget : X.get (h, k) = some ⟨pc, .tc (.commit sp)⟩ := he
        have htg := htarget h k pc sp rank hh hget hmb a.isLt
        have hn := hall (h, k) sp rank _ ⟨pc, hget⟩ htg
        have htg' : TcCommit.target sp rank =
            some (Bar.loc L (h / L.block + a.val) ⟨.acc, j.val, true⟩) := htg
        have hact : objectAction X X.async (Bar.loc L (h / L.block + a.val) ⟨.acc, j.val, true⟩)
            (.async (h, k) (.tcNotify rank)) = some (.arrive 1 0) := by
          simp [objectAction, hget, htg', hn]
        obtain ⟨r, hr, hid⟩ := (hobj _).2.2 _ _ hact
        refine ⟨r, hr, hid, ?_⟩
        have hra := ((hobj _).2.1 r hr).1
        rw [hid, hact, Option.some.injEq] at hra
        simp only [isNotify, decide_eq_true_eq]
        exact hra.symm
      | _ => simp [commitsTo] at hp
    | _ => simp [commitsTo] at hp

/-- **A finished producer's accumulator commits are its successful response polls.** An MMA thread
of a leader CTA in an exit stage (its state has an exit offset), whose input commits are 32 per slot
per successful response poll (`mma_leader`'s finished case, `hfin`), has one accumulator commit of
its buffer per successful poll: the accumulator count of its state (`mma_acc_count`) over the input
commits, with no accumulator commit pending. -/
theorem finished_acc_count (ht : ThreadFacts L X) {g : Nat} (hg : g < L.threads)
    (hub : ∀ k pc f, X.get (g, k) ≠ some ⟨pc, .ub f⟩) {m : Mma.D}
    (hσ : Frame.stateAt (code L) X g (X.tr g).length = some (some (.inr (.mma m))))
    (hx : Mma.exitOff m ≠ none)
    (hfin : ∀ s : Fin 4, (X.tr g).countP (commitsTo (inputEmpty L (g / L.block) s)) =
      32 * okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (X.tr g)) :
    (X.tr g).countP (commitsTo (Bar.loc L (g / L.block) ⟨.acc, m.w % 2, true⟩)) =
      okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (X.tr g) := by
  have hc := (ht.mma_acc_count hg hub hσ).1
  have hsite : m.site ≠ .accCommit := by
    intro h
    apply hx
    simp [Mma.exitOff, h]
  have hmm : mmaCount L g (X.tr g) =
      128 * okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (X.tr g) := by
    unfold mmaCount
    simp only [hfin]
    simp
    omega
  simp only [hsite, ↓reduceIte, add_zero] at hc
  rw [hc, hmm]
  omega

/-- Notifications and arrivals agree on a full barrier: its records are fault-free. -/
theorem full_notify_eq_arrival (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {c : Nat} {j k : Fin 2} :
    (X.objects ((slot L c j).full k)).countP isNotify =
      (X.objects ((slot L c j).full k)).countP isArrival := by
  refine List.countP_congr fun q hq => ?_
  have hf := fault_free hpre hX ht c j ((slot L c j).full_mem k) q hq
  simp [isNotify, isArrival, hf]

/-- **The commits are at most the full barrier's phase.** With every commit notified, a leader MMA
thread's accumulator commits to its buffer's full barrier are at most the completed phases of the
barrier in CTA `h / L.block + a` (`full_arrivals`, `full_notify_eq_arrival`): each commit leaves one
notification there (`commits_counted_acc`). -/
theorem commits_le_phase (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) (hobj : ObjectsOk X) {j : Fin 2}
    (htarget : ∀ (h k pc : Nat) (sp : TcCommit.Spec) (r : Fin 16), h < L.threads →
      X.get (h, k) = some ⟨pc, .tc (.commit sp)⟩ →
      sp.mbar = Bar.loc L (h / L.block) ⟨.acc, j.val, true⟩ → r.val < 2 →
      TcCommit.target sp r = some (Bar.loc L (h / L.block + r.val) ⟨.acc, j.val, true⟩))
    (hall : ∀ i sp rank m, X.Commit i sp → TcCommit.target sp rank = some m →
      rank ∈ X.tcNotified i)
    {h : Nat} (hh : h < L.threads) (hlead : h / L.block % 2 = 0) {a : Fin 2} {before : State}
    (hstate : stateBefore (X.objects (Bar.loc L (h / L.block + a.val) ⟨.acc, j.val, true⟩))
      (X.objects (Bar.loc L (h / L.block + a.val) ⟨.acc, j.val, true⟩)).length = some before) :
    (X.tr h).countP (commitsTo (Bar.loc L (h / L.block) ⟨.acc, j.val, true⟩)) ≤ before.phase := by
  obtain ⟨c, hc⟩ : ∃ c, h / L.block = 2 * c := ⟨h / L.block / 2, by omega⟩
  have hF : Bar.loc L (h / L.block + a.val) ⟨.acc, j.val, true⟩ = (slot L c j).full a := by
    rw [hc]
    rfl
  rw [hF] at hstate
  have hcomm := commits_counted_acc hobj (j := j) htarget hall hh a
  rw [hF] at hcomm
  have hph := full_arrivals hpre hX ht (c := c) (j := j) (k := a) hstate
  rw [full_notify_eq_arrival hpre hX ht] at hcomm
  omega

/-- A successful poll is a wait on its barrier. -/
theorem okPoll_wait_form {m : Loc} {e : Event} (h : okPoll m e = true) :
    ∃ pc p acq sc, e = ⟨pc, .wait m p true acq sc⟩ := by
  obtain ⟨pc, kind⟩ := e
  cases kind
  case wait l p ok acq sc =>
    cases ok
    · simp [okPoll, sourceWaitSuccess] at h
    · simp only [okPoll, sourceWaitSuccess, decide_eq_true_eq] at h
      subst h
      exact ⟨pc, p, acq, sc, rfl⟩
  all_goals simp [okPoll, sourceWaitSuccess] at h

/-- **A consumer's successful polls are on its own buffer.** A consumer thread `g` polls the full
barrier of its own accumulator only (`RingEvent.wait`): the other buffer's barrier has none of its
successful polls. -/
theorem okPolls_other_zero (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X) {g : Nat}
    (hg : g < L.threads)
    {j : Fin 2} (hj : j.val ≠ g % L.block / 32 / 4) :
    okPolls (Bar.loc L (g / L.block) ⟨.acc, j.val, true⟩) (X.tr g) = 0 := by
  unfold Flow.okPolls
  refine List.countP_eq_zero.mpr fun e he => ?_
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp he
  intro hok
  obtain ⟨pc, p, acq, sc, he'⟩ := okPoll_wait_form hok
  have hget : X.get (g, k) = some
      ⟨pc, .wait (Bar.loc L (g / L.block) ⟨.acc, j.val, true⟩) p true acq sc⟩ := by
    show (X.tr g)[k]? = _
    rw [List.getElem?_eq_getElem hk, he']
  obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked hget (by simp)
  have hpb := (ht.ring_event hg hget hσ).wait ⟨.acc, j.val, true⟩ (g / L.block) p true acq sc rfl
    j.isLt
  obtain ⟨⟨cs, -⟩, hjw⟩ : (∃ cs, d = .inr (.cons cs)) ∧ j.val = g % L.block / 32 / 4 := hpb.1
  exact hj hjw

/-- **A consumer's successful polls are its own buffer's.** Its `consCount` is the successful polls
of its own accumulator-full barrier (its warp group `g % L.block / 32 / 4`, below two). -/
theorem consCount_eq_own (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X) {g : Nat}
    (hg : g < L.threads)
    (hw : g % L.block / 32 / 4 < 2) :
    consCount L g (X.tr g) =
      okPolls (Bar.loc L (g / L.block) ⟨.acc, g % L.block / 32 / 4, true⟩) (X.tr g) := by
  unfold consCount
  rw [Fin.sum_univ_two]
  rcases (show g % L.block / 32 / 4 = 0 ∨ g % L.block / 32 / 4 = 1 by omega) with h0 | h1
  · rw [okPolls_other_zero hX ht hg (j := 1) (by simp only [Fin.val_one]; omega), h0]
    simp
  · rw [okPolls_other_zero hX ht hg (j := 0) (by simp only [Fin.val_zero]; omega), h1]
    simp

end TmemRing

end
end PTX.Kernels.Fp16Gemm8192.Proof
