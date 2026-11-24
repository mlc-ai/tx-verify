-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.Lk5VCount

@[expose] public section

/-!
# The shuffle instances of the default partition, without the lockstep

From the count of shuffles along a default-partition thread (`cnt_inv`):

* `shfl_state_cases`: a shuffle state of a default thread is the common start's (count 0), a
  prologue block's (count between 1 and `num_pre`), the softmax region's (count
  `1 + num_pre + smW`, iteration below `num_iters`) or the epilogue's (count
  `1 + num_pre + smBase num_iters`, on the branch with a block);
* `shflLiveD`: no lane of a default warp exits before a shuffle instance of its warp (an exit has
  the full count, which is above every shuffle's);
* `shfl_peer_d`: the source lane of a shuffle of the softmax region is at the softmax state of the
  same site and iteration, and the received word is the field of that state.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface.Lk
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.InklingRelDecode.Proof.Mbar (wordsSo_all)

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

theorem event_le {k : Nat} {e : Event} (he : X.get (g, k) = some e) : k ≤ (X.tr g).length := by
  have := (List.getElem?_eq_some_iff.mp he).1
  simp only at this
  omega

/-- The CTA numbers of two threads of one CTA. -/
theorem np_ni_eq {h : Nat} (hc : g / L.block = h / L.block) :
    NP Q L g = NP Q L h ∧ NI Q L g = NI Q L h ∧ skC Q L g = skC Q L h := by
  have h1 : NI Q L g = NI Q L h := by unfold NI ProA.cta; rw [hc]
  have h2 : NP Q L g = NP Q L h := by unfold NP ProA.cta; rw [hc]
  exact ⟨h2, h1, by simp only [skC, h1]⟩

/-- **A softmax shuffle state** has an iteration below `num_iters`. -/
theorem sm_shfl_facts (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hg : g < L.threads) {k : Nat} {e : Event} {d : Sm.D}
    (he : X.get (g, k) = some e) (hσ : St Q L X g k = some (some (.d (.sm d))))
    (hsh : shflSt (.d (.sm d)) = true) :
    Sm.smShfl d.site = true ∧ (Sm.smMid d.site = true → 1 ≤ d.i) ∧ d.i < NI Q L g := by
  have hS := (cnt_inv hpre hX hf hg k (event_le he) hσ).2
  have h1 : Sm.smShfl d.site = true := by rw [← sm_shfl]; exact hsh
  have hI : Sm.Inv L g d := by
    obtain ⟨t, ins, o, -, hinv, -, -⟩ := Frame.fired_site hf.sound hX he hσ
    exact hinv.2
  have hlate : Sm.LateSite d.site := by
    rcases Sm.smShfl_cases h1 with h | h | h | h | h | h | h | h | h <;> rw [h] <;> trivial
  have hi := (hI.late hlate).2.2
  rw [r26_eq hpre hf hX hg he hσ] at hi
  exact ⟨h1, hS, hi⟩

/-- **The shuffle states of a default-partition thread and their counts.** -/
theorem shfl_state_cases (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hg : g < L.threads) {k : Nat} {e : Event} {s : DComp.St}
    (he : X.get (g, k) = some e) (hσ : St Q L X g k = some (some (.d s)))
    (hsh : shflSt (.d s) = true) :
    cntF Q L g (.d s) = 0 ∨
    (1 ≤ cntF Q L g (.d s) ∧ cntF Q L g (.d s) < 1 + NP Q L g) ∨
    (∃ d, s = .sm d ∧ Sm.smShfl d.site = true ∧ (Sm.smMid d.site = true → 1 ≤ d.i) ∧
      d.i < NI Q L g ∧ cntF Q L g (.d s) = 1 + NP Q L g + Sm.smW d) ∨
    (cntF Q L g (.d s) = 1 + NP Q L g + Sm.smBase (NI Q L g) ∧ skC Q L g = false) := by
  have hS := (cnt_inv hpre hX hf hg k (event_le he) hσ).2
  cases s with
  | dstart d =>
    left
    have h1 : DStart.dsShfl d.site = true := by rw [← ds_shfl]; exact hsh
    simp only [cntF, DStart.dsW]
    have : d.site ≠ .toProA := by
      intro h; rw [h] at h1; exact absurd h1 (by decide)
    simp [this]
  | pro d =>
    right; left
    have h1 : ProA.proShfl d.site = true := by rw [← pro_shfl]; exact hsh
    have hG := (pgSo_all hpre hX hf k _ hσ).1
    have hlt := ProA.lt_npOf hG (ProA.psh_blk _ h1)
    obtain ⟨hdef, tm, -, hpro⟩ := hf.reach hg hσ
    have ha : ProA.ArgsOk L g d.dt.pro := by
      rw [hpro]; exact DStart.argsOk_inh hpre hg hdef tm
    have hw : d.dt.pro.w71 = Q.splits := by rw [hpro]; exact DStart.inh_w71 hpre
    obtain ⟨h0, h1', h2⟩ := wordsSo_all hpre hX hf k _ hσ
    have hk : d.site.afterSk = true := by
      have hb := ProA.proShfl_blk _ h1
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
  | sm d =>
    right; right; left
    have h1 : Sm.smShfl d.site = true := by rw [← sm_shfl]; exact hsh
    have hI : Sm.Inv L g d := by
      obtain ⟨t, ins, o, -, hinv, -, -⟩ := Frame.fired_site hf.sound hX he hσ
      exact hinv.2
    have hlate : Sm.LateSite d.site := by
      rcases Sm.smShfl_cases h1 with h | h | h | h | h | h | h | h | h <;> rw [h] <;> trivial
    have hi := (hI.late hlate).2.2
    rw [r26_eq hpre hf hX hg he hσ] at hi
    exact ⟨d, rfl, h1, hS, hi, rfl⟩
  | epi d =>
    right; right; right
    have h1 : Epi.epShfl d.site = true := by rw [← epi_shfl]; exact hsh
    have hs : d.site = .shfl := by simpa [Epi.epShfl] using h1
    have hsk : d.sk = false := hS.1 (by rw [hs]; rfl)
    refine ⟨?_, hS.2 ▸ hsk⟩
    simp [cntF, Epi.epW, hs]

/-- The count of a shuffle state of a default thread is below the count at an exit of a thread
of its CTA. -/
theorem shfl_lt_exit (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hg : g < L.threads) {k : Nat} {e : Event} {s : DComp.St}
    (he : X.get (g, k) = some e) (hσ : St Q L X g k = some (some (.d s)))
    (hsh : shflSt (.d s) = true) :
    cntF Q L g (.d s) < 1 + NP Q L g + Sm.smBase (NI Q L g) + (if skC Q L g then 0 else 1) := by
  rcases shfl_state_cases hpre hX hf hg he hσ hsh with h | ⟨-, h⟩ | ⟨d, -, h1, hm, hi, h⟩ |
    ⟨h, hk⟩
  · omega
  · omega
  · have h2 := Sm.shfl_lt_next h1 hm
    have h3 := Sm.smBase_le (show d.i + 1 ≤ NI Q L g by omega)
    simp only [Sm.smW] at h
    split <;> omega
  · simp only [hk, Bool.false_eq_true, ↓reduceIte]
    omega

/-- The count at an exit of a default thread. -/
theorem exit_cnt (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hg : g < L.threads) {k pc : Nat}
    (he : X.get (g, k) = some ⟨pc, .exit⟩) (hdef : g % L.block < 128) :
    cnt Execution.isShfl X g k =
      1 + NP Q L g + Sm.smBase (NI Q L g) + (if skC Q L g then 0 else 1) := by
  rcases exit_event_state hX hf.sound hf.tracked he with ⟨d, hσ, hs⟩ | ⟨x, hσ, -⟩
  · obtain ⟨hc, hS⟩ := cnt_inv hpre hX hf hg k (event_le he) hσ
    rw [hc]
    simp only [cntF, Epi.epW, hs, hS.2]
  · exfalso
    have := (cls_inv k _ (event_le he) hσ).mpr hdef
    exact this

/-- **No lane of a default warp exits before a shuffle instance of its warp.** -/
def ShflLiveD (Q : Params) (L : Launch) (X : Execution) : Prop :=
  ∀ {g a n : Nat}, g % L.block < 128 → X.ShflK (g, a) n →
    ∀ {x : Nat}, SameWarp L g x → ¬ ShflExited X x n

theorem shflLiveD_of (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) : ShflLiveD Q L X := by
  intro g a n hdef hk x hw hex
  obtain ⟨kx, pce, hexit, hcx⟩ := hex
  obtain ⟨⟨pc, md, av, bb, c, r, o, hget⟩, hcnt⟩ := id hk
  have hg : g < L.threads := hw.1.1
  have hx : x < L.threads := hw.1.2.1
  have hxd : x % L.block < 128 := by have := hw.2; omega
  obtain ⟨s, hs⟩ := Frame.event_state hf.sound hX hf.tracked hget (fun pc f h => by cases h)
  have hs' : St Q L X g a = some (some s) := hs
  have hsh : shflSt s = true := by
    rw [← isShfl_state hX hf hg hget hs']; rfl
  cases s with
  | w s => exact absurd ((cls_inv a _ (event_le hget) hs').mpr hdef) id
  | d s =>
    have hc := (cnt_inv hpre hX hf hg a (event_le hget) hs').1
    have hlt := shfl_lt_exit hpre hX hf hg hget hs' hsh
    have hex := exit_cnt hpre hX hf hx hexit hxd
    obtain ⟨e1, e2, e3⟩ := np_ni_eq (Q := Q) hw.1.2.2
    have hc' : cnt Execution.isShfl X g a = n := hcnt
    have hcx' : cnt Execution.isShfl X x kx ≤ n := hcx
    rw [e1, e2, e3] at hlt
    omega

/-- **The received word of a shuffle is the operand of the source lane's shuffle of the
instance**, for a default lane. -/
theorem shfl_source_d (hX : Consistent L kernel asms mem0 X) (hlive : ShflLiveD Q L X)
    (hb : L.block = 256) {g a n pc : Nat} {m : ShflMode} {av : Value} {b c : Nat} {recv : Value}
    {ok : Bool} (hg : g < L.threads) (hdef : g % L.block < 128)
    (hget : X.get (g, a) = some ⟨pc, .shfl m av b c recv ok⟩) (hk : X.ShflK (g, a) n) :
    ∃ j pc' b' c' r' o', X.ShflK (shflSrc L g m b c, j) n ∧
      X.get (shflSrc L g m b c, j) = some ⟨pc', .shfl m recv b' c' r' o'⟩ ∧
      SameWarp L g (shflSrc L g m b c) := by
  obtain ⟨-, hsource⟩ := hX.shfl g a n pc m av b c recv ok hget hk
  have hlt : (shflSource m (laneOf L g) b c).1 < 32 :=
    shflSource_lt m (Nat.mod_lt _ (by decide))
  have hw : SameWarp L g (shflSrc L g m b c) := (src_sameWarp hb hg hlt).1
  rcases hsource with ⟨j, pc', b', c', r', o', hpeer, hepeer⟩ | hx
  · exact ⟨j, pc', b', c', r', o', hpeer, hepeer, hw⟩
  · exact absurd hx (hlive hdef hk hw)

/-- **The source lane of a shuffle of the softmax region is at the same site and iteration**:
two default lanes of a warp whose `n`-th shuffles are softmax states have them at one site and
iteration. -/
theorem shfl_same_site (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) {y x a j n : Nat} {d : Sm.D} {s : TSt}
    (hw : SameWarp L y x) (hk : X.ShflK (y, a) n) (hk' : X.ShflK (x, j) n)
    (hσ : St Q L X y a = some (some (.d (.sm d)))) (hσ' : St Q L X x j = some (some s))
    (hyd : y % L.block < 128) :
    ∃ d2, s = .d (.sm d2) ∧ d2.site = d.site ∧ d2.i = d.i := by
  obtain ⟨⟨pc, md, av, bb, c, r, o, hget⟩, hcnt⟩ := id hk
  obtain ⟨⟨pc', md', av', bb', c', r', o', hget'⟩, hcnt'⟩ := id hk'
  have hy : y < L.threads := hw.1.1
  have hx : x < L.threads := hw.1.2.1
  have hxd : x % L.block < 128 := by have := hw.2; omega
  obtain ⟨e1, e2, e3⟩ := np_ni_eq (Q := Q) hw.1.2.2
  have hsh : shflSt (.d (.sm d)) = true := by
    rw [← isShfl_state hX hf hy hget hσ]; rfl
  have hsh' : shflSt s = true := by
    rw [← isShfl_state hX hf hx hget' hσ']; rfl
  have hc := (cnt_inv hpre hX hf hy a (event_le hget) hσ).1
  have hcy : cnt Execution.isShfl X y a = n := hcnt
  have hcx : cnt Execution.isShfl X x j = n := hcnt'
  obtain ⟨h1, hm, hi⟩ := sm_shfl_facts hpre hX hf hy hget hσ hsh
  have h : cntF Q L y (.d (.sm d)) = 1 + NP Q L y + Sm.smW d := rfl
  cases s with
  | w s => exact absurd ((cls_inv j _ (event_le hget') hσ').mpr hxd) id
  | d s =>
    have hc' := (cnt_inv hpre hX hf hx j (event_le hget') hσ').1
    have hlt := Sm.shfl_lt_next h1 hm
    have hle := Sm.smBase_le (show d.i + 1 ≤ NI Q L y by omega)
    simp only [Sm.smW] at h
    rcases shfl_state_cases hpre hX hf hx hget' hσ' hsh' with h' | ⟨-, h'⟩ |
      ⟨d2, hd2, h1', hm', hi', h'⟩ | ⟨h', -⟩
    · omega
    · rw [← e1] at h'; omega
    · subst hd2
      simp only [Sm.smW] at h'
      rw [← e1] at h'
      obtain ⟨hs, hi⟩ := Sm.shfl_inj h1' h1 hm' hm (by omega)
      exact ⟨d2, rfl, hs, hi⟩
    · rw [← e1, ← e2] at h'; omega

end
end PTX.Kernels.InklingRelDecode.Proof.Interface.Lk
