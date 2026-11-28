-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Protocol.Life.Exit
public import Kernels.InklingRelDecode.Proof.Protocol.Mbar.InitFirst
import Kernels.InklingRelDecode.Proof.Protocol.Tmem.AsyncDone
import Kernels.InklingRelDecode.Proof.Mma.Export.CommitOrder
import Kernels.InklingRelDecode.Proof.Mma.Export.Count
import Kernels.InklingRelDecode.Proof.Mma.Export.FinalCount
import Kernels.InklingRelDecode.Proof.Mma.Export.Election
import Kernels.InklingRelDecode.Proof.Protocol.KV.Decl
import Kernels.InklingRelDecode.Proof.Protocol.Shared.ReadValues
import Lemmas.Flow.NthEv

@[expose] public section

/-! # A commit's arrival finishes before its CTA exits

The kernel's four commits are the MMA warp's elected lane's, each with the one-CTA group and the
rank-zero target of its own CTA: to a score slot (pc 2499), to a slot's empty barrier (pc 2546), to
`o_done` (pc 2548), and to `o_final` (pc 2553). The final one is observed by the poll of `o_final`
that every default lane makes before its exit. The empty and done commits of an exited CTA are
followed by the lane's next commit, and the assumption `commitOrder` orders their arrivals before
that commit's (`CommitNext`). A score commit is observed by a poll of the softmax lanes (the open
`ScoreObserved`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Life
open PTX PTX.Flow PTX.AsyncCopy

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **Every score commit of an exited CTA is observed** by a successful poll of a lane of its
CTA. -/
def ScoreObserved (L : Launch) (X : Execution) : Prop :=
  ∀ g k sp rank m, X.get (g, k) = some ⟨2499, .tc (.commit sp)⟩ →
    TcCommit.target sp rank = some m → CtaExited L X (g / L.block) →
    ∃ h j acq ws, h / L.block = g / L.block ∧
      WaitObserves X (.async (g, k) (.tcNotify rank)) (h, j) m acq ws

private theorem target_zero {c a : Nat} {r : Fin 16} {l : Loc}
    (h : TcCommit.target ⟨.one, ⟨.shared, c, a⟩, 1, c, 1⟩ r = some l) : r.val = 0 := by
  simp only [TcCommit.target, Option.ite_none_right_eq_some, Option.some.injEq] at h
  omega

private theorem target_of {c a : Nat} {r : Fin 16} (h : r.val = 0) :
    TcCommit.target ⟨.one, ⟨.shared, c, a⟩, 1, c, 1⟩ r = some ⟨.shared, c, a⟩ := by
  simp [TcCommit.target, h]

/-- **The arrival of the final commit is enabled to the exit**: the poll of `o_final` that
every default lane of the exited CTA makes observes it. -/
theorem final_enabled (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (rows : MbarRows Q L X) (init : Mbar.InitRows L X) {g k sp r}
    (he : X.get (g, k) = some ⟨2553, .tc (.commit sp)⟩) (hr : r.val = 0)
    (hx : CtaExited L X (g / L.block)) :
    SharedEnabled L kernel Assumptions.all X (g / L.block) (.async (g, k) (.tcNotify r)) := by
  have hg := Frame.lt_of_get hX he
  have hc : g / L.block < L.grid :=
    Nat.div_lt_of_lt_mul (by simpa [Launch.threads, Nat.mul_comm] using hg)
  have hcd : g / L.block * L.block / L.block = g / L.block :=
    Nat.mul_div_cancel _ (by rw [hp.block]; omega)
  obtain ⟨jw, kx, l, q, ac, sc, hjk, hown, hpoll⟩ := final_wait hp hX hf hc hx
  obtain ⟨ic, spi, rank, hgc, hti, hrk, hobs⟩ := Tmem.poll_observes hp hX hf rows init hpoll
  rw [hcd] at hgc hrk hobs hti
  obtain ⟨ev, mem, won⟩ := Mma.Export.elected hp hX hf he (fun _ => nofun)
    (by change 2553 ∈ _; decide)
  have lead := Protocol.KV.leader_eq hX hg ⟨ev, (List.take_sublist k _).subset mem, won⟩
  rw [Mma.Export.commit_warp hp hX hf he] at lead
  rw [lead] at hgc hrk hobs
  have words : RoleBytes L X := fun h => Protocol.Shared.role_bytes hp hX h
  have hki : ic = k := by
    rcases Nat.lt_trichotomy ic k with h | h | h
    · exact absurd hgc (Mma.Export.final_first hp hX hf words he ic h spi)
    · exact h
    · exact absurd he (Mma.Export.final_first hp hX hf words hgc k h sp)
  subst hki
  obtain ⟨off, rfl, -⟩ := Mma.Export.commit hp hX hf (Mma.Export.commit_warp hp hX hf he) hgc
  have hrank : rank = r := Fin.ext ((target_zero hti).trans hr.symm)
  subst hrank
  have := observed_enabled hX hobs (by simpa [hcd] using hx)
  simpa [hcd] using this

/-- **The arrival of a selected commit is performed whenever the next one's is** (the
assumption `commitOrder`). -/
private theorem performed (hX : Consistent L kernel Assumptions.all m X) {g j j' pc : Nat}
    {sp : TcCommit.Spec} {r : Fin 16} (he : X.get (g, j) = some ⟨pc, .tc (.commit sp)⟩)
    (hs : Assumptions.commitOrderSites.contains pc = true) (hjj : j < j')
    (hc : ∃ s, X.Commit (g, j') s) (hk : ∀ k, j < k → k < j' → ¬ ∃ s, X.Commit (g, k) s)
    (hr : r ∈ X.tcNotified (g, j')) : r ∈ X.tcNotified (g, j) :=
  hX.asm Assumptions.commitOrder (by simp [Assumptions.all]) g j j' pc sp r he hs hjj hc hk hr

/-- **The arrival of every commit of an exited CTA is enabled to an exit of the CTA**, by
induction on the commits left in the lane. -/
theorem commit_enabled (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (rows : MbarRows Q L X) (init : Mbar.InitRows L X)
    (hS : ScoreObserved L X) :
    ∀ (n g k pc : Nat) (sp : TcCommit.Spec) (r : Fin 16) (l : Loc),
      (X.tr g).length - k ≤ n → X.get (g, k) = some ⟨pc, .tc (.commit sp)⟩ →
      TcCommit.target sp r = some l → CtaExited L X (g / L.block) →
        SharedEnabled L kernel Assumptions.all X (g / L.block) (.async (g, k) (.tcNotify r)) := by
  intro n
  induction n with
  | zero =>
    intro g k pc sp r l hn he
    have := len_of_get he
    simp only at this
    omega
  | succ n ih =>
    intro g k pc sp r l hn he htg hx
    obtain ⟨off, rfl, site⟩ := Mma.Export.commit hp hX hf (Mma.Export.commit_warp hp hX hf he) he
    have hr := target_zero htg
    have selected : (pc = 2546 ∨ pc = 2548) →
        SharedEnabled L kernel Assumptions.all X (g / L.block) (.async (g, k) (.tcNotify r)) := by
      intro sel
      obtain ⟨j, hj, sp', hj'⟩ := Mma.Export.later_final hp hX hf he sel hx
      have hex : ∃ q, k < q ∧ ∃ s', X.Commit (g, q) s' := ⟨j, hj, sp', 2553, hj'⟩
      classical
      obtain ⟨hkk, s', pc', hget'⟩ := Nat.find_spec hex
      have hnext : ∃ s, X.Commit (g, Nat.find hex) s := ⟨s', pc', hget'⟩
      have hmin : ∀ q, k < q → q < Nat.find hex → ¬ ∃ s, X.Commit (g, q) s :=
        fun q hq hq' ⟨s2, hs2⟩ => Nat.find_min hex hq' ⟨hq, s2, hs2⟩
      obtain ⟨off', rfl, -⟩ := Mma.Export.commit hp hX hf
        (Mma.Export.commit_warp hp hX hf hget') hget'
      have hlen : (X.tr g).length - Nat.find hex ≤ n := by
        have := len_of_get hget'
        simp only at this
        omega
      have next := ih g _ pc' _ r _ hlen hget' (target_of hr) hx
      have hs : Assumptions.commitOrderSites.contains pc = true := by
        rcases sel with rfl | rfl <;> decide +kernel
      have hp0 := performed hX he hs hkk hnext hmin next.1
      have hn : CommitNext Assumptions.all X (.async (g, k) (.tcNotify r))
          (.async (g, Nat.find hex) (.tcNotify r)) :=
        ⟨rfl, rfl, hkk, hp0, next.1, ⟨pc, _, he, by rcases sel with rfl | rfl <;> decide +kernel⟩,
          hnext, hmin⟩
      exact SharedEnabled.of_commit_next hn next
    rcases site with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
    · obtain ⟨h, j, acq, ws, hhc, hw⟩ := hS g k _ r l he htg hx
      have := observed_enabled hX hw (by simpa [hhc] using hx)
      simpa [hhc] using this
    · exact selected (Or.inl rfl)
    · exact selected (Or.inr rfl)
    · exact final_enabled hp hX hf rows init he hr hx

/-- **`CommitFinished`**: the arrival of a commit completes before an exit of its CTA, given the
observation of every score commit. -/
theorem commit_finished (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (rows : MbarRows Q L X) (init : Mbar.InitRows L X)
    (hS : ScoreObserved L X) : CommitFinished L kernel Assumptions.all X := by
  rintro ⟨g, k⟩ sp rank l ⟨pc, he⟩ htg hx
  exact (commit_enabled hp hX hf rows init hS _ g k pc sp rank l le_rfl he htg hx).finished

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Life
