-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.Lk5WBfly
public import Kernels.InklingRelDecode.Proof.Interface.Lk5VChain
public import Kernels.InklingRelDecode.Proof.Thread.Lk3Num
public import Kernels.InklingRelDecode.Proof.Thread.ShapeSmWait

@[expose] public section

/-!
# The shuffles of the rescale test do not fault

`Sm.next` at the exchanges of the lazy-rescale test (`shfl7` to `shfl12`) is `none` where a
minimum or the comparison with `1.0` has no outcome. Both operands read as numbers (`ReadsAs`), so
they do not:

* `shfl7` to `shfl10`: the thread's word and the word received from the source lane are words of
  level `k` of the butterfly (`Lev`, `lev_reads`), numbers that are not `+inf`
  (`shfl_min_ok`);
* `shfl11`: the loaded scratch word of the thread and of its source lane read as numbers
  (`ScratchIt`, `shfl11_ok`);
* `shfl12`: the decision is the comparison of the value of the four words' minimum with `1.0`
  (`p170_value_d`, `shfl12_ok`).

The premises are those of the value chain: `Rs.SmBaseZero` (the base word's zero for the level 0)
and `ScratchIt` of every iteration.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface.Lk
open PTX PTX.Proof PTX.Flow PTX.Assumption PTX.Kernels.InklingRelDecode.Proof.Sm

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **The levels `0` to `4` of every iteration and CTA.** -/
theorem lev_upto (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hz : Rs.SmBaseZero Q L X) (c i : Nat) :
    ∀ k, k ≤ 4 → Lev Q L X c i k
  | 0, _ => lev0 hpre hX hf hz c i
  | k + 1, hk => lev_step hpre hX hf (by omega) (lev_upto hpre hX hf hz c i k (by omega))

/-- **A word of level `k` reads as a number that is not `+inf`.** -/
theorem lev_reads {c i k : Nat} (H : Lev Q L X c i k) {y kk : Nat} {d : Sm.D}
    (hy : y < L.threads) (hc : y / L.block = c)
    (hσ : St Q L X y kk = some (some (.d (.sm d)))) (hs : d.site = lv k) (hi : d.i = i)
    (hk : kk ≤ (X.tr y).length) (hev : k = 0 → ∃ e, X.get (y, kk) = some e) :
    ∃ x : EReal, x ≠ ⊤ ∧ ReadsAs (lval k d) x := by
  obtain ⟨-, x, hx, hr, -⟩ := H hy hy hc hc (m := 0) (by omega) (by simp) (by simp) hσ hσ hs hs hi
    hi hk hk (fun h => ⟨hev h, hev h⟩)
  exact ⟨x, hx, hr⟩

/-- **The exchange of level `k`** (`shfl7` to `shfl10`): the event is the shuffle of the level's
word, and the minimum of the thread's word and the received one has an outcome. -/
theorem shfl_min_ok (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hz : Rs.SmBaseZero Q L X) {k : Nat} (hk4 : k < 4) {g a : Nat}
    {d : Sm.D} {e : Event} (hg : g < L.threads) (he : X.get (g, a) = some e)
    (hσ : St Q L X g a = some (some (.d (.sm d)))) (hs : d.site = lv k) :
    ∃ recv ok, e = ⟨d.site.pc, .shfl .bfly (lval k d) (loff k) 31 recv ok⟩ ∧
      ∃ v, minE [lval k d, recv] = .ok v := by
  obtain ⟨recv, ok, x, j, d2, he', hw, -, hσ2, hs2, hi2, hrecv, -, hj, r2, o2, he2⟩ :=
    sm_shfl_peer_d hpre hX hf hpre.block (fld := lval k) (k := loff k)
      (by rw [hs]; exact shape_lv hk4) hg he hσ
  have H : Lev Q L X (g / L.block) d.i k := lev_upto hpre hX hf hz (g / L.block) d.i k (by omega)
  obtain ⟨xa, -, ha⟩ := lev_reads H hg rfl hσ hs rfl (event_le he) (fun _ => ⟨e, he⟩)
  obtain ⟨xb, -, hb⟩ := lev_reads H (y := x) (kk := j) hw.1.2.1 hw.1.2.2.symm hσ2
    (hs2.trans hs) hi2 hj (fun _ => ⟨⟨d2.site.pc, .shfl .bfly (lval k d2) (loff k) 31 r2 o2⟩, he2⟩)
  refine ⟨recv, ok, he', ?_⟩
  rw [hrecv]
  exact ⟨_, minE_readsAs ha hb⟩

/-- **The exchange of the loaded scratch word** (`shfl11`): the event is the shuffle of the word
and the thread's word and the received one read as numbers. -/
theorem shfl11_ok (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hI : ∀ i, ScratchIt Q L X i) {g a : Nat} {d : Sm.D}
    {e : Event} (hg : g < L.threads) (he : X.get (g, a) = some e)
    (hσ : St Q L X g a = some (some (.d (.sm d)))) (hs : d.site = .shfl11) :
    ∃ recv ok, e = ⟨d.site.pc, .shfl .bfly d.stg.ld 2 31 recv ok⟩ ∧
      ∃ x y, ReadsAs d.stg.ld x ∧ ReadsAs recv y := by
  obtain ⟨recv, ok, x, j, d2, he', hw, -, hσ2, hs2, hi2, hrecv, -, hj, r2, o2, he2⟩ :=
    sm_shfl_peer_d hpre hX hf hpre.block (fld := fun d => d.stg.ld) (k := 2)
      (by rw [hs]; exact shflShape_11 L) hg he hσ
  obtain ⟨W, -, hR⟩ := hI d.i (g / L.block)
  have h1 := hR hg rfl hσ hs rfl
  have h2 := hR hw.1.2.1 hw.1.2.2.symm hσ2 (hs2.trans hs) hi2
  rw [← hrecv] at h2
  exact ⟨recv, ok, he', _, _, h1, h2⟩

/-- A comparison of two values that read as numbers has an outcome. -/
theorem setpE_readsAs {c : FCmp} {cmp : Cmp} {fz : Bool} {va vb : Value} {x y : EReal}
    (hc : c = .ord cmp ∨ c = .unord cmp) (hx : ReadsAs va x) (hy : ReadsAs vb y) :
    setpE c fz va vb = .ok (erealCompare cmp x y) := by
  have hbase : fcmpBase c = some cmp := by rcases hc with rfl | rfl <;> rfl
  simp only [setpE, idealSetp, hbase, hx, hy, bindRead, pure, Except.pure]

/-- **The decision at `shfl12`** has an outcome: the event is the shuffle of `m2` and the
decision `%p170` is a boolean. -/
theorem shfl12_ok (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hI : ∀ i, ScratchIt Q L X i) {g a : Nat} {d : Sm.D}
    {e : Event} (hg : g < L.threads) (he : X.get (g, a) = some e)
    (hσ : St Q L X g a = some (some (.d (.sm d)))) (hs : d.site = .shfl12) :
    ∃ recv ok, e = ⟨d.site.pc, .shfl .bfly d.stg.m2 1 31 recv ok⟩ ∧ ∃ b, d.p170 recv = .ok b := by
  obtain ⟨W, hW, hR⟩ := hI d.i (g / L.block)
  obtain ⟨recv, ok, he', hp⟩ := p170_value_d hpre hX hf hpre.block hW
    (fun hg' hc hσ' hs' hi' => hR hg' hc hσ' hs' hi') hg rfl he hσ hs rfl
  refine ⟨recv, ok, he', ?_⟩
  rw [hp]
  have h1 : ReadsAs (erealValue .f32 (Wmin W)) (Wmin W) :=
    ReadsAs.of_erealValue (min_ne_top' (min_ne_top' (hW 0)))
  obtain ⟨y, hy⟩ := valFloat_b32_one
  exact ⟨_, setpE_readsAs (Or.inr rfl) h1 (by simpa using readEReal_of_valFloat hy)⟩

end
end PTX.Kernels.InklingRelDecode.Proof.Interface.Lk
