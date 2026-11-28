-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Bar.Group
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.NoBarArrive
public import Lemmas.Protocol.NamedBarSources
import Lemmas.Protocol.ClusterTrace

@[expose] public section

/-! # A named barrier orders its participants by their counts

Two lanes `u`, `v` of one CTA, `u` at an event that is no event of named barrier `id` after `n` of
its events on `id` and `v` at an event after more than `n` of its own, `u` a participant: the event
of `u` is ordered before the one of `v` (`barId_order`). Both lanes made their `n`-th event on
`id` (`v` before its event, `u` since it exits only past `n` of them, `hexit`, and otherwise by the
released generation), and arrivals of one ordinal synchronize
(`Sources.same_ordinal_baseCausality`). The barrier's group is `barWarps id` (`bar_groupW`).
`bar9_order` (`Sync9.lean`) is barrier 9's. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow MbarRow ClusterTrace

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- The `c`-th event on barrier `id` of a lane is a `bar.sync` of that barrier. -/
theorem barId_nth (hR : BarRows P L X) {id y c : Nat} (hy : y < L.threads)
    (h : c + 1 ≤ (X.tr y).countP (Execution.isBarId id)) :
    ∃ j pc, X.get (y, j) = some ⟨pc, .bar id (barCnt id) .sync⟩ ∧
      ((X.tr y).take j).countP (Execution.isBarId id) = c := by
  obtain ⟨j, ev, hj, hbj, hcj⟩ := MbarRing.Slot.exists_nth_countP (Execution.isBarId id) h
  obtain ⟨pce, kd⟩ := ev
  cases kd <;> simp only [Execution.isBarId, Bool.false_eq_true] at hbj
  rename_i id' cnt md
  simp only [beq_iff_eq] at hbj
  subst hbj
  have hget : X.get (y, j) = some ⟨pce, .bar id' cnt md⟩ := hj
  have hc := bar_cnt hR hy hget
  have hm := bar_sync hR hy hget
  subst hc hm
  exact ⟨j, pce, hget, hcj⟩

/-- **A participant of a named barrier arrives, before it is passed**: `v`'s event after more than
`n` of its events on `id` follows `u`'s `n`-th event on `id` (`u` a participant warp, and an
exiting `u` made more than `n`), and every earlier event of `u` is before `v`'s. -/
theorem barId_arrive (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hR : BarRows P L X) {id u v k n : Nat} (hs : SameCta L u v)
    (hmem : barIn id ((u % L.block) / 32) = true) (hk : k < (X.tr v).length)
    (hlt : n < ((X.tr v).take k).countP (Execution.isBarId id))
    (hexit : (∃ j pcx, X.get (u, j) = some ⟨pcx, .exit⟩) →
      n + 1 ≤ (X.tr u).countP (Execution.isBarId id)) :
    ∃ i' pc', X.get (u, i') = some ⟨pc', .bar id (barCnt id) .sync⟩ ∧
      ((X.tr u).take i').countP (Execution.isBarId id) = n ∧
      ∀ i, i < i' → baseCausality L X (u, i) (v, k) := by
  obtain ⟨hyu, hyv, hcta⟩ := hs
  have hle : ((X.tr v).take k).countP (Execution.isBarId id) ≤
      (X.tr v).countP (Execution.isBarId id) := (List.take_sublist _ _).countP_le
  obtain ⟨j, pcj, hj, hjn⟩ := barId_nth hR (id := id) hyv (c := n) (by omega)
  obtain ⟨hG, hS⟩ := bar_groupW hp hR hyv hj
  have hjk : j < k := lt_of_countP_take_lt (xs := X.tr v) (p := Execution.isBarId id)
    (by rw [hjn]; exact hlt)
  have hkl : j + 1 < (X.tr v).length := by omega
  have hw : (u % L.block) / 32 ∈ barWarps id := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, hmem⟩
    rw [hp.block]
    omega
  obtain ⟨i', pc', hi', hci'⟩ := hS.member_arrival hX hG (f := (v, j)) (pc := pcj) hj hkl hcta hw
    fun hx => by
      have h6 := hexit hx
      obtain ⟨n', pcn, hn, hcn⟩ := barId_nth hR (id := id) hyu (c := n) h6
      exact ⟨n', pcn, hn, hcn.trans hjn.symm⟩
  refine ⟨i', pc', hi', by rw [hci', hjn], fun i hii => ?_⟩
  exact hS.same_ordinal_baseCausality hX hG ⟨hyu, hyv, hcta⟩ hi' hj hkl
    (by rw [hci', hjn]) hii hjk hk

/-- **A named barrier orders its participants**: `u`'s event, not an event of `id`, after `n` of
its events on `id`, is before `v`'s event after more than `n` (`u` a participant warp, and an
exiting `u` made more than `n`). -/
theorem barId_order (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hR : BarRows P L X) {id u v i k : Nat} {e : Event} (hs : SameCta L u v)
    (hmem : barIn id ((u % L.block) / 32) = true) (hi : X.get (u, i) = some e)
    (hnb : Execution.isBarId id e = false) (hk : k < (X.tr v).length)
    (hlt : ((X.tr u).take i).countP (Execution.isBarId id) <
      ((X.tr v).take k).countP (Execution.isBarId id))
    (hexit : ∀ j pcx, X.get (u, j) = some ⟨pcx, .exit⟩ →
      ((X.tr u).take i).countP (Execution.isBarId id) + 1 ≤
        (X.tr u).countP (Execution.isBarId id)) :
    baseCausality L X (u, i) (v, k) := by
  obtain ⟨i', pc', hget, hci', hcaus⟩ := barId_arrive hp hX hR hs hmem hk hlt
    (fun ⟨j, pcx, hx⟩ => hexit j pcx hx)
  refine hcaus i ?_
  have hbar : Execution.isBarId id ⟨pc', .bar id (barCnt id) .sync⟩ = true := by
    simp [Execution.isBarId]
  rcases Nat.lt_trichotomy i i' with h | h | h
  · exact h
  · subst h
    rw [hi] at hget
    have he := Option.some.inj hget
    subst he
    simp only [hbar] at hnb
    cases hnb
  · have h1 : ((X.tr u).take i').countP (Execution.isBarId id) + 1 ≤
        ((X.tr u).take i).countP (Execution.isBarId id) :=
      ClusterTrace.countP_take_lt h hget hbar
    omega

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
