-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof2.Epilogue.Warp
public import Kernels.TmlFa4Fwd.Proof.InputRead

@[expose] public section

/-! # The output warp over the whole thread

With the read-only input (`cuQReadsFromLaunch`), the warp induction (`good`) holds in every
consistent execution:

* `good_all`: the thread machine follows every lane of warp 13, at states that hold `Ref`;
* `fits`: every role state of a lane holds the reference values and the ledger's closed forms;
* `read_addr`: every read a lane of warp 13 makes after its prologue reads the word of a
  cumulative query offset of the batch. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof2.Epilogue
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

theorem good_all (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hg : g < L.threads) (hw : Prologue.warpIndex L g = 13) (k : Nat) : Good p L X g k :=
  good hp hX (cuQReadsFromLaunch hp hX) hg hw k

/-- **Every role state of a lane of warp 13 holds the reference values.** -/
theorem fits (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hg : g < L.threads) (hw : Prologue.warpIndex L g = 13) {k : Nat} {d : D} {n : Cls → Nat}
    (hσ : Frame.stateAt (thread p L) X g k = some (some (inj p L g d n))) :
    Fits p L g d (n .shfl) (n .vote) ∧ Led n d :=
  have h := (good_all hp hX hg hw k).2 _ hσ
  ⟨h.1, h.2.2⟩

/-- The address of a read site of a state that holds the reference values is a cumulative query
offset of the batch. -/
theorem rdAddr_batch (hp : Pre p L m) {d : D} {ns nv : Nat} (hF : Fits p L g d ns nv)
    (hs : (∃ k, d.site = .word k) ∨ d.site = .q0 ∨ d.site = .q1) :
    ∃ i ≤ p.batch, (rdAddr p L g d).toNat = p.cuQBase + 4 * i := by
  have hb := batch_lt hp
  have hl : laneOf L g < 32 := Nat.mod_lt _ (by decide)
  rcases hs with ⟨k', hs⟩ | hs
  · have hF' := hF
    simp only [Fits, hs] at hF'
    obtain ⟨r, n0, v0, -, hR, -, -, hL, hrd⟩ := hF'
    have hidx := reqN_le hp hl hrd
    refine ⟨_, hidx, ?_⟩
    cases k' with
    | first | second =>
      have h0 : r = 0 := by have := hR.2; simp_all
      subst h0
      simp only [rdAddr, hs, laneW_W]
      rw [addrU_toNat hp (by simpa [reqN] using hidx)]
      simp [reqN]
    | loop | loop2 =>
      have h0 : r ≠ 0 := by have := hR.2; simp_all
      obtain ⟨hg', -⟩ := hL h0
      have hq : reqOf L g d.grp = W (reqN p r (laneOf L g)) := by
        rw [hg', reqOf_G h0, req_W hp _ r hl]
      simp only [rdAddr, hs, hq]
      exact addrS_toNat0 hp hidx
  · obtain ⟨R, bal, hC⟩ : ∃ R bal, ChosenVals p L g R bal d ns nv := by
      rcases hs with hs | hs <;> simp only [Fits, hs] at hF
      · exact hF
      · obtain ⟨R, bal, h, -⟩ := hF; exact ⟨R, bal, h⟩
    obtain ⟨i, hi, hib⟩ := chosen_W hp hC
    rcases hs with hs | hs
    · refine ⟨i, by omega, ?_⟩
      simp only [rdAddr, hs, hi]
      exact addrS_toNat0 hp (by omega)
    · refine ⟨i + 1, hib, ?_⟩
      simp only [rdAddr, hs, hi]
      exact addrS_toNat4 hp hib

/-- **Every read of a lane of warp 13 after its prologue reads a cumulative query offset of the
batch.** -/
theorem read_addr (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hw : Prologue.warpIndex L g = 13) {k pc : Nat} {a : Acc} {bs : List (Option Byte)}
    (hk5 : 5 ≤ k) (he : X.get (g, k) = some ⟨pc, .rd a bs⟩) :
    ∃ i ≤ p.batch, a = wordAcc (p.cuQBase + 4 * i) := by
  obtain ⟨d, n, hσ, hF, hE⟩ := good_at hp hX hk5 he (by rintro _ _ ⟨⟩)
    (good_all hp hX (Frame.lt_of_get hX he) hw k)
  obtain ⟨s, w, dn, tl, u1, u2, u4, u8, u16, tot, grp, acc, gx, cur, bal, pv, nt, c0, c1⟩ := d
  have hs : (∃ k, s = .word k) ∨ s = .q0 ∨ s = .q1 := by
    cases s <;> simp only [Ev] at hE <;> first
      | exact .inl ⟨_, rfl⟩
      | exact .inr (.inl rfl)
      | exact .inr (.inr rfl)
      | simp_all [isStore]
  obtain ⟨i, hi, haddr⟩ := rdAddr_batch hp hF (by simpa using hs)
  refine ⟨i, hi, ?_⟩
  rcases hs with ⟨k', rfl⟩ | rfl | rfl <;> simp only [Ev] at hE <;>
    rcases hE with ⟨bs', hk⟩ | ⟨f, hk⟩ <;> simp only [Kind.rd.injEq, reduceCtorEq] at hk <;>
    rw [hk.1, haddr]

end
end PTX.Kernels.TmlFa4Fwd.Proof2.Epilogue
