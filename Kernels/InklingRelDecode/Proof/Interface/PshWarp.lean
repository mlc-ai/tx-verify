-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.Lk5VShfl
public import Kernels.InklingRelDecode.Proof.Thread.ProAPsh

@[expose] public section

/-!
# The prologue's broadcasts receive the warp index (`pshSo_all`)

The prologue's machine follows every word its three broadcasts of the warp index (`psh0` …
`psh2`) receive and records it (`ProA.shOf`); bit 0 of the word picks the half of the K/V preload
the block's copies fill (`ProA.half`). In an execution of the kernel the word is the warp index:

* DEP-WARP-SHUFFLE (`Consistent.shfl`): the received word is the operand of the source lane's
  shuffle of the same instance, or any value if the source lane exited before it. The source of
  `shfl.sync.idx … 0, 31` is lane 0 of the warp, a thread of the default partition.
* Lane 0 has not exited before (`Lk.shflLiveD_of`: no lane of a default warp exits before a
  shuffle instance of its warp, by the count of shuffles along the thread, `Lk.cnt_inv`).
* Lane 0's shuffle of the instance has the same count `n`, with `1 ≤ n < 1 + num_pre` (a
  broadcast of the prologue, `pro_shfl_cnt`); a shuffle state of a default thread with such a
  count is a broadcast of the prologue (the common start's has count 0, the softmax region's and
  the epilogue's at least `1 + num_pre`), whose operand is the thread's warp index
  (`ProA.shape_psh`), which is the receiving thread's (`src_operand`, `psh_recv`).

`ShSo` carries the word to the states after the broadcast (`ProA.sh_next`, `ProA.pshAfter_next`,
`ProA.next_psh`). The consumers: `pro_half` (the half of a copy is `warp % 2`) and
`pro_not_pelDead` (the election after a broadcast is not the fault state `ProA.PelDead`).
No premise beyond `Pre`, consistency and `ThreadFacts`.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.InklingRelDecode.Proof.Mbar (wordsSo_all next_map_some next_sm_not_pro
  next_epi_not_pro)
open PTX.Kernels.InklingRelDecode.Proof.Interface.Lk

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **The count of a broadcast of the prologue** is below `1 + num_pre`. -/
theorem pro_shfl_cnt (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) {g k : Nat} (hg : g < L.threads) {d : ProA.D}
    (hσ : St Q L X g k = some (some (.d (.pro d)))) (h1 : ProA.proShfl d.site = true) :
    cntF Q L g (.d (.pro d)) < 1 + NP Q L g := by
  have hG := (pgSo_all hpre hX hf k _ hσ).1
  have hlt := ProA.lt_npOf hG (ProA.psh_blk _ h1)
  obtain ⟨hdef, tm, -, hpro⟩ := hf.reach hg hσ
  have ha : ProA.ArgsOk L g d.dt.pro := by
    rw [hpro]; exact DStart.argsOk_inh hpre hg hdef tm
  have hw : d.dt.pro.w71 = Q.splits := by rw [hpro]; exact DStart.inh_w71 hpre
  obtain ⟨h0, h1', h2⟩ := wordsSo_all hpre hX hf k _ hσ
  have hk : d.site.afterSk = true := by
    obtain ⟨st, dt⟩ := d
    cases st <;> first | rfl | (simp [ProA.proShfl] at h1)
  have hne : d.site ≠ .sMax ∧ d.site ≠ .ldCu0 := by
    constructor <;> (intro h; rw [h] at hk; exact absurd hk (by decide))
  have hm : ProA.WordsMatch Q (ProA.cta L g .z) d.dt :=
    ⟨h0 hne.1 hne.2, h1' (Or.inl hk), h2 hk⟩
  have hnp := ProA.npOf_eq hpre hg ha hw hm
  have hb := ProA.proShfl_blk _ h1
  obtain ⟨st, dt⟩ := d
  simp only at hnp hlt hb
  simp only [cntF, ProA.proW_lit dt hb, NP]
  omega

/-- **The operand of an index shuffle of a default thread whose count is that of a broadcast of
the prologue** is the thread's warp index. -/
theorem src_operand (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) {x j pc : Nat} {av : Value} {b c : Nat} {r : Value} {o : Bool}
    (hx : x < L.threads) (hxd : x % L.block < 128)
    (hget : X.get (x, j) = some ⟨pc, .shfl .idx av b c r o⟩)
    (h1 : 1 ≤ cnt Execution.isShfl X x j) (h2 : cnt Execution.isShfl X x j < 1 + NP Q L x) :
    av = b32 (x % L.block / 32) := by
  obtain ⟨s, hs⟩ := Frame.event_state hf.sound hX hf.tracked hget (fun pc f h => by cases h)
  have hs' : St Q L X x j = some (some s) := hs
  have hsh : shflSt s = true := by
    rw [← isShfl_state hX hf hx hget hs']; rfl
  cases s with
  | w s => exact absurd ((cls_inv j _ (event_le hget) hs').mpr hxd) id
  | d s =>
    have hc := (cnt_inv hpre hX hf hx j (event_le hget) hs').1
    cases s with
    | dstart d =>
      exfalso
      have h3 : DStart.dsShfl d.site = true := by rw [← ds_shfl]; exact hsh
      have : d.site ≠ .toProA := by
        intro h; rw [h] at h3; exact absurd h3 (by decide)
      simp only [cntF, DStart.dsW, this, ↓reduceIte] at hc
      omega
    | pro d =>
      have h3 : ProA.proShfl d.site = true := by rw [← pro_shfl]; exact hsh
      obtain ⟨u, hF⟩ := fired_cont hX hf hx hget hs' (by simp [ExitState])
      have hps : d.site = .psh0 ∨ d.site = .psh1 ∨ d.site = .psh2 := by
        obtain ⟨st, dt⟩ := d
        cases st <;> simp_all [ProA.proShfl]
      obtain ⟨recv, ok, hev⟩ := ProA.shape_psh (fired_pro hF) hps
      simp only [Event.mk.injEq, Kind.shfl.injEq] at hev
      exact hev.2.2.1
    | sm d =>
      exfalso
      simp only [cntF] at hc
      omega
    | epi d =>
      exfalso
      simp only [cntF] at hc
      omega

/-- **The word a broadcast of the prologue receives is the warp index.** -/
theorem psh_recv (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) {g k : Nat} (hg : g < L.threads) {d : ProA.D} {e : Event}
    (he : X.get (g, k) = some e) (hσ : St Q L X g k = some (some (.d (.pro d))))
    (hs : d.site = .psh0 ∨ d.site = .psh1 ∨ d.site = .psh2) :
    ∃ pc ok, e = ⟨pc, .shfl .idx (b32 (g % L.block / 32)) 0 31 (b32 (g % L.block / 32)) ok⟩ := by
  obtain ⟨u, hF⟩ := fired_cont hX hf hg he hσ (by simp [ExitState])
  obtain ⟨recv, ok, hev⟩ := ProA.shape_psh (fired_pro hF) hs
  subst hev
  have hdef : g % L.block < 128 := (hf.reach hg hσ).1
  have hK : X.ShflK (g, k) (cnt Execution.isShfl X g k) :=
    ⟨⟨_, _, _, _, _, _, _, he⟩, rfl⟩
  obtain ⟨j, pc', b', c', r', o', hkj, hget', hw⟩ :=
    shfl_source_d (Q := Q) hX (shflLiveD_of hpre hX hf) hpre.block hg hdef he hK
  have hx : shflSrc L g .idx 0 31 < L.threads := hw.1.2.1
  have hxd : shflSrc L g .idx 0 31 % L.block < 128 := by have := hw.2; omega
  have h3 : ProA.proShfl d.site = true := by
    rcases hs with h | h | h <;> rw [h] <;> rfl
  have hc := (cnt_inv hpre hX hf hg k (event_le he) hσ).1
  have hlt := pro_shfl_cnt hpre hX hf hg hσ h3
  obtain ⟨e1, -, -⟩ := np_ni_eq (Q := Q) hw.1.2.2
  have hcj : cnt Execution.isShfl X (shflSrc L g .idx 0 31) j = cnt Execution.isShfl X g k :=
    hkj.2
  have hop := src_operand hpre hX hf hx hxd hget' (by rw [hcj, hc]; simp [cntF])
    (by rw [hcj, hc, ← e1]; exact hlt)
  rw [hop, ← hw.2]
  exact ⟨_, ok, rfl⟩

/-! ### The words along a thread -/

/-- **What a prologue state knows about its received words**: after the broadcast of block `j`,
word `j` is the warp index. -/
def ShSo (L : Launch) (g : Nat) : TSt → Prop
  | .d (.pro d) => ∀ j < 3, d.site ∈ ProA.pshAfter j → ProA.shOf d.dt j = b32 (g % L.block / 32)
  | _ => True

theorem pshAfter_not_psh {j : Nat} (hj : j < 3) {s : ProA.Site} (h : s ∈ ProA.pshAfter j) :
    s ∉ ProA.pshSites := by
  interval_cases j <;> revert h <;> cases s <;> decide

theorem shOf_keep {dt dt' : ProA.Dat} (h : dt'.sh0 = dt.sh0 ∧ dt'.sh1 = dt.sh1 ∧ dt'.sh2 = dt.sh2)
    (j : Nat) : ProA.shOf dt' j = ProA.shOf dt j := by
  match j with
  | 0 => exact h.1
  | 1 => exact h.2.1
  | j + 2 => exact h.2.2

theorem psh_of_eq {s : ProA.Site} {j : Nat} (hj : j < 3) (h : s = ProA.pshSite j) :
    s = .psh0 ∨ s = .psh1 ∨ s = .psh2 := by
  subst h
  interval_cases j <;> simp [ProA.pshSite]

/-- **One prologue step keeps `ShSo`.** -/
theorem shSo_step (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) {g k0 : Nat} {d0 d1 : ProA.D} {e : Event} (hg : g < L.threads)
    (he : X.get (g, k0) = some e) (hσ : St Q L X g k0 = some (some (.d (.pro d0))))
    (hI : ShSo L g (.d (.pro d0))) (hn : ProA.next L g d0 e = some (some d1)) :
    ShSo L g (.d (.pro d1)) := by
  obtain ⟨s, dt⟩ := d0
  intro j hj hm
  rcases ProA.pshAfter_next hn j hj hm with hs | hs
  · rw [shOf_keep (ProA.sh_next hn (pshAfter_not_psh hj hs)) j]
    exact hI j hj hs
  · subst hs
    obtain ⟨m, av, b, c, recv, ok, hk, hsh, -, -⟩ := ProA.next_psh hj hn
    obtain ⟨pc, ok', hev⟩ := psh_recv hpre hX hf hg he hσ (psh_of_eq hj rfl)
    rw [hsh]
    subst hev
    simp only [Kind.shfl.injEq] at hk
    exact hk.2.2.2.2.1.symm

theorem shSo_start (L : Launch) (g : Nat) (P : ProA.Inh) (w : Value) :
    ShSo L g (.d (.pro (ProA.D.start P w))) := by
  intro j hj hm
  exfalso
  change ProA.Site.sMax ∈ ProA.pshAfter j at hm
  interval_cases j <;> revert hm <;> decide

/-- **The received words of every prologue state of a thread are the warp index.** -/
theorem shSo_all (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) {g : Nat} :
    ∀ k s, St Q L X g k = some (some s) → ShSo L g s := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro s hσ
  by_cases hinit : s = (code L Q g).init
  · subst hinit
    show ShSo L g (if g % L.block < 128 then .d (DComp.code L g Q).init
      else .w (WComp.code L g Q).init)
    split <;> exact trivial
  · obtain ⟨k0, e, s0, hlt, he', hs0, hn⟩ := stateAt_pred hσ hinit
    have he : X.get (g, k0) = some e := he'
    have hg : g < L.threads := Frame.lt_of_get hX he
    have hI := ih k0 hlt s0 hs0
    cases s0 with
    | w w0 =>
      rw [next_w] at hn
      obtain ⟨a, -, rfl⟩ := next_map_some hn
      exact trivial
    | d d0 =>
      rw [next_d] at hn
      obtain ⟨s1, hn1, rfl⟩ := next_map_some hn
      cases s1 with
      | dstart d1 => exact trivial
      | sm d1 => exact trivial
      | epi d1 => exact trivial
      | pro d1 =>
        cases d0 with
        | dstart ds =>
          have h' : DComp.dstartNext L g Q ds e = some (some (.pro d1)) := hn1
          unfold DComp.dstartNext at h'
          obtain ⟨d2, -, h2⟩ := next_map_some h'
          split_ifs at h2
          cases h2
          exact shSo_start L g _ _
        | sm ds => exact absurd hn1 (next_sm_not_pro g Q ds e d1)
        | epi ds => exact absurd hn1 (next_epi_not_pro g Q ds e d1)
        | pro dp =>
          have h' : DComp.proNext L g Q dp e = some (some (.pro d1)) := hn1
          unfold DComp.proNext at h'
          by_cases hb : dp.site = ProA.Site.bar18
          · simp only [hb, ↓reduceIte] at h'
            split_ifs at h' <;> cases h'
          · simp only [hb, ↓reduceIte] at h'
            obtain ⟨d3, hd3, h3⟩ := next_map_some h'
            cases h3
            exact shSo_step hpre hX hf hg he hs0 hI hd3

/-! ### The consumers -/

theorem half_b32 {w : Nat} (hw : w < 2 ^ 32) : ProA.shW (b32 w) % 2 = w % 2 := by
  rw [ProA.shW_of (Raw.word32Of_b32 w), Nat.mod_eq_of_lt hw]

/-- **The half of the K/V preload a prologue copy fills is the warp's**: bit 0 of the warp
index. -/
theorem pro_half (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) {g k : Nat} {d : ProA.D}
    (hσ : St Q L X g k = some (some (.d (.pro d)))) {i : Nat} (hi : i < 12)
    (hs : d.site = ProA.ptcSite i) : ProA.half d.dt (i / 4) = ProA.tidOf L g / 32 % 2 := by
  have h := shSo_all hpre hX hf k _ hσ (i / 4) (by omega) (by rw [hs]; exact ProA.ptcSite_after hi)
  have hb : L.block = 256 := hpre.block
  have hw : g % L.block / 32 < 2 ^ 32 := by
    have := Nat.mod_lt g (show 0 < L.block by omega)
    omega
  unfold ProA.half
  rw [h, half_b32 hw]

/-- **No prologue state of an execution is the fault state after a broadcast**: the received
word is the warp index, which has bits. -/
theorem pro_not_pelDead (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) {g k : Nat} {d : ProA.D}
    (hσ : St Q L X g k = some (some (.d (.pro d)))) : ¬ ProA.PelDead d := by
  rintro ⟨b, hb, hs, hw⟩
  have h := shSo_all hpre hX hf k _ hσ b hb (by rw [hs]; exact ProA.pelSite_after hb)
  rw [h, Raw.word32Of_b32] at hw
  cases hw

end
end PTX.Kernels.InklingRelDecode.Proof.Interface
