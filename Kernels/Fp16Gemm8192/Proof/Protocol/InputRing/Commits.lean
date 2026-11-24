-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Protocol.InputRing.Slot
public import Kernels.Fp16Gemm8192.Proof.Interface
public import Lemmas.Protocol.RecordCount

@[expose] public section

/-! # Commits leave notifications

Once every commit has notified its targets, an MMA thread's commits to a slot's empty barrier
are at most the notifications its warp left on that barrier in either CTA of the cluster: each
commit notifies both CTAs (`ThreadFacts.commit_ranks`), and its notification is a record of its
own identity in the barrier's history (`commits_counted`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Flow MBarrier AsyncCopy

noncomputable section

namespace InputRing

variable {L : Launch} {mem0 : Mem0} {X : Execution}

/-- With every commit notified, an MMA thread's commits to slot `s`'s empty barrier are at most
its warp's notifications to that barrier in CTA `a` of the cluster. -/
theorem commits_counted (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X)
    (hall : ∀ i sp rank m, X.Commit i sp → TcCommit.target sp rank = some m →
      rank ∈ X.tcNotified i)
    {h : Nat} (hh : h < L.threads) (b a : Fin 2) (s : Fin 4)
    (hsel : consumerThread L (h / L.block / 2) b h = true) :
    (X.tr h).countP (commitsTo (inputEmpty L (h / L.block) s)) ≤
      (X.objects (emptyLoc L (h / L.block + a.val) s)).countP
        (notification L (h / L.block / 2) a b) := by
  have hsel' := hsel
  simp only [consumerThread, decide_eq_true_eq] at hsel'
  let rank : Fin 16 := ⟨a.val, by omega⟩
  have hloc : inputEmpty L (h / L.block + a.val) s = emptyLoc L (h / L.block + a.val) s := by
    simp only [inputEmpty, emptyLoc, Bar.loc, Bar.off]
    congr 1
    omega
  refine countP_le_of_records (fun k => Ref.async (h, k) (.tcNotify rank)) ?_ ?_
  · intro i j _ _ hij
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
        have hmb : sp.mbar = inputEmpty L (h / L.block) s := by
          simpa [commitsTo] using hp
        have hget : X.get (h, k) = some ⟨pc, .tc (.commit sp)⟩ := he
        obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked hget nofun
        have htg := ht.commit_ranks s rank hh hget hσ rfl hmb a.isLt
        rw [hloc] at htg
        have hn := hall (h, k) sp rank _ ⟨pc, hget⟩ htg
        have hact : objectAction X X.async (emptyLoc L (h / L.block + a.val) s)
            (.async (h, k) (.tcNotify rank)) = some (.arrive 1 0) := by
          simp only [objectAction, hget, htg, hn, and_self, ite_true]
        obtain ⟨r, hr, hid⟩ := (hX.tma.2.2.1 _).2.2 _ _ hact
        refine ⟨r, hr, hid, ?_⟩
        have hra := ((hX.tma.2.2.1 _).2.1 r hr).1
        rw [hid, hact, Option.some.injEq] at hra
        unfold notification
        rw [hid]
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨hsel, rfl, hra.symm⟩
      | _ => simp [commitsTo] at hp
    | _ => simp [commitsTo] at hp

/-- **Commits leave notifications.** -/
theorem commitsCounted (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X) :
    CommitsCounted L X :=
  fun hall _ b a s hh hsel => commits_counted hX ht hall hh b a s hsel

end InputRing

end
end PTX.Kernels.Fp16Gemm8192.Proof
