-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Shared.RowMax
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Chain
public import Lemmas.Tcgen05.TcFence
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.UbBefore
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Bar9Odd
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Out
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Bar.SyncId
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Bar.Ord
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Bar.Sync9
import Lemmas.Protocol.ClusterTrace

@[expose] public section

/-! # The partner lane's row-maximum store

Lane `g` of warpgroup 0 reads the word of its partner, the lane `tid ^ 64` of the same CTA (load
address `4 t ^^^ 256`), after `2 r + 2` barrier-9 events. The partner has its exchange store (pc 566
of block `r`, pc 1155 in the epilogue) after exactly `2 r + 1` of its own (`rmax_peer_store`):
it arrived at the barrier that `g` passed (`barId_arrive`), and the barrier event at pc 569 or
1156 follows the store (`w0_prev_569`, `w0_prev_1156`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow MbarRow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **Below an event**: the events of lane `h` before the event `(g, k)` in the tcgen05 order are no
undefined behaviour and have a valid prefix of warpgroup 0's trace through them (what the
induction on that order gives). -/
def W0Below (P : Params) (L : Launch) (X : Execution) (h g k : Nat) : Prop :=
  ∀ j e, X.get (h, j) = some e → Relation.TransGen (TcMma.TcStep L X) (h, j) (g, k) →
    W0Valid P.scale ((X.tr h).take (j + 1)) ∧ ∀ u, e.kind ≠ .ub u

/-- The partner lane of `g`: the lane `tid ^ 64` of its CTA. -/
def w0Partner (L : Launch) (g : Nat) : Nat := g - g % L.block + ((g % L.block) ^^^ 64)

theorem w0Partner_facts (hp : Pre P L m) {g : Nat} (hw : warp L g < 4) (hg : g < L.threads) :
    SameCta L (w0Partner L g) g ∧ warp L (w0Partner L g) < 4 ∧
      w0Partner L g / L.block = g / L.block ∧ w0Partner L g % L.block = (g % L.block) ^^^ 64 := by
  have hb : L.block = 384 := by have := hp.block; omega
  have hlt : g % 384 < 128 := by
    simp only [warp, tidOf_x_eq hp] at hw
    omega
  have hx : (g % 384) ^^^ 64 < 128 := Nat.xor_lt_two_pow (n := 7) (by omega) (by omega)
  have hth : L.threads = L.grid * 384 := by simp only [Launch.threads, hb]
  have hd : w0Partner L g / 384 = g / 384 := by simp only [w0Partner, hb]; omega
  have hm : w0Partner L g % 384 = (g % 384) ^^^ 64 := by simp only [w0Partner, hb]; omega
  refine ⟨⟨?_, hg, by rw [hb]; exact hd⟩, ?_, by rw [hb]; exact hd, by rw [hb]; exact hm⟩
  · rw [hth] at hg ⊢
    simp only [w0Partner, hb]
    omega
  · simp only [warp, tidOf_x_eq hp]
    omega

/-- **The partner's store** (valid rows): after `2 r + 2` barrier-9 events of lane `g` (`r` at most
the CTA's block count) the partner lane's exchange store (pc 566 or 1155) is the one after exactly
`2 r + 1` of its own, and the only one there. -/
theorem rmax_peer_store (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hR : BarRows P L X) {g k r : Nat} {e : Event}
    (hw : warp L g < 4) (he : X.get (g, k) = some e)
    (hcnt : ((X.tr g).take k).countP (Execution.isBarId 9) = 2 * r + 2)
    (hrR : r ≤ blocksOf P L (g / L.block)) (hv : W0Below P L X (w0Partner L g) g k) :
    ∃ j f, X.get (w0Partner L g, j) = some f ∧ (f.pc = 566 ∨ f.pc = 1155) ∧
      ((X.tr (w0Partner L g)).take j).countP (Execution.isBarId 9) = 2 * r + 1 ∧
      Relation.TransGen (TcMma.TcStep L X) (w0Partner L g, j) (g, k) ∧
      ∀ j' f', X.get (w0Partner L g, j') = some f' → (f'.pc = 566 ∨ f'.pc = 1155) →
        ((X.tr (w0Partner L g)).take j').countP (Execution.isBarId 9) = 2 * r + 1 → j' = j := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨hs, hwh, hdiv, -⟩ := w0Partner_facts hp hw hg
  set h := w0Partner L g with hh
  have hmem : barIn 9 ((h % L.block) / 32) = true := by
    simp only [warp, tidOf_x_eq hp] at hwh
    simp only [barIn, ite_true, decide_eq_true_eq]
    rw [hp.block]
    exact hwh
  have hk : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  obtain ⟨i', pc', hget, hci, hbc⟩ := barId_arrive hp hX hR hs hmem hk (n := 2 * r + 1)
    (by omega) (fun ⟨j, pcx, hx⟩ => by
    have := wg0_outExit hp hX hFw hwh hx
    rw [hdiv] at this
    omega)
  have hbar : Execution.isBarId 9 ⟨pc', .bar 9 (barCnt 9) .sync⟩ = true := by
    simp [Execution.isBarId]
  have hrange : 103 ≤ pc' ∧ pc' < 1842 := by
    rcases bar_cls (bar_use hR hs.1 hget rfl) with ⟨-, hc⟩ | ⟨⟨-, hlo, hhi⟩, -⟩ | ⟨hw4, -⟩
    · simp [BarRow.Cta] at hc
    · simp only at hlo hhi
      omega
    · omega
  have hodd := wg0_bar9_odd hp hX hFw hget hrange hbar hci (by rw [hdiv]; exact hrR)
  obtain ⟨j, rfl⟩ : ∃ j, i' = j + 1 := by
    cases i' with
    | zero => simp at hci
    | succ j => exact ⟨j, rfl⟩
  have hjl : j < (X.tr h).length := by
    have := (List.getElem?_eq_some_iff.mp hget).1
    simp only at this
    omega
  obtain ⟨f0, hf0⟩ : ∃ f0, X.get (h, j) = some f0 := ⟨_, List.getElem?_eq_getElem hjl⟩
  have htcj : Relation.TransGen (TcMma.TcStep L X) (h, j) (g, k) :=
    .single (.inl (hbc j (by omega)))
  have hvj : W0Valid P.scale ((X.tr h).take (j + 1)) := (hv j f0 hf0 htcj).1
  have hnext : ∃ f, X.get (h, j) = some f ∧ (f.pc = 566 ∨ f.pc = 1155) := by
    rcases hodd with h5 | h5
    · obtain ⟨f, hf, hfp⟩ := Wg0.w0_prev_569 hp hX hFw hwh hget (fun _ h => by cases h) h5 hvj
      exact ⟨f, hf, .inl hfp⟩
    · obtain ⟨f, hf, hfp⟩ := Wg0.w0_prev_1156 hp hX hFw hwh hget (fun _ h => by cases h) h5 hvj
      exact ⟨f, hf, .inr hfp⟩
  obtain ⟨f, hf, hfpc⟩ := hnext
  have hsplit : ((X.tr h).take (j + 1)) = (X.tr h).take j ++ [f] := by
    have hf' : (X.tr h)[j]? = some f := hf
    rw [List.take_add_one, hf']; rfl
  have hnb := wg0_store_notBar hp hX hFw hf hfpc
  have hcj : ((X.tr h).take j).countP (Execution.isBarId 9) = 2 * r + 1 := by
    rw [hsplit, List.countP_append] at hci
    simpa [hnb] using hci
  refine ⟨j, f, hf, hfpc, hcj, htcj, fun j' f' hf' hpc' hc' => ?_⟩
  have hbar' : ∀ x, x = j + 1 → X.get (h, x) = some ⟨pc', .bar 9 (barCnt 9) .sync⟩ →
      (pc' = 569 ∨ pc' = 1156) := fun _ _ _ => hodd
  rcases Nat.lt_trichotomy j' j with hlt | rfl | hgt
  · exfalso
    have hex : ∃ e2, X.get (h, j' + 1) = some e2 := by
      have : j' + 1 < (X.tr h).length := by
        have := (List.getElem?_eq_some_iff.mp hf).1
        simp only at this
        omega
      exact ⟨_, List.getElem?_eq_getElem this⟩
    obtain ⟨e2, he2⟩ := hex
    have hvj' : W0Valid P.scale ((X.tr h).take (j' + 1)) :=
      (hv j' f' hf' (.single (.inl (hbc j' (by omega))))).1
    have hu2 : ∀ u, e2.kind ≠ .ub u := noUb_kind_of_lt hX he2 (k := j + 1) (by omega) (by
      have := (List.getElem?_eq_some_iff.mp hget).1
      simp only at this
      omega)
    have hpc2 : e2.pc = 569 ∨ e2.pc = 1156 := by
      rcases hpc' with h1 | h1
      · exact .inl (Wg0.w0_next_566 hp hX hFw hwh hf' h1 he2 hu2 hvj')
      · exact .inr (Wg0.w0_next_1155 hp hX hFw hwh hf' h1 he2 hu2 hvj')
    have hb2 := wg0_bar9_of_pc hp hX hFw he2 hu2 hpc2
    have hne : j' + 1 ≠ j := by
      rintro rfl
      rw [hf] at he2
      cases he2
      omega
    have hlt2 := ClusterTrace.countP_take_lt (xs := X.tr h) (p := Execution.isBarId 9)
      (z := j' + 1) (m := j) (r := e2) (by omega) he2 hb2
    have hnb' := wg0_store_notBar hp hX hFw hf' hpc'
    have hsp : ((X.tr h).take (j' + 1)) = (X.tr h).take j' ++ [f'] := by
      have hf'' : (X.tr h)[j']? = some f' := hf'
      rw [List.take_add_one, hf'']; rfl
    rw [hsp, List.countP_append] at hlt2
    simp [hnb'] at hlt2
    omega
  · rfl
  · exfalso
    have hb2 : Execution.isBarId 9 (⟨pc', .bar 9 (barCnt 9) .sync⟩ : Event) = true := hbar
    have hne : j + 1 ≠ j' := by
      rintro rfl
      rw [hget] at hf'
      cases hf'
      simp only at hpc'
      omega
    have := ClusterTrace.countP_take_lt (xs := X.tr h) (p := Execution.isBarId 9)
      (z := j + 1) (m := j') (by omega) hget hb2
    omega

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
