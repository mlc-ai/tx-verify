-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.Lk5VShfl

@[expose] public section

/-!
# The epilogue's broadcast receives the warp index

The epilogue broadcasts the warp index from lane 0 (`Epi.Site.shfl`) and forms the lane field of
its load's address from the received word; its machine follows every received word and records
the lane bits (`Epi.Prm.bw`). After tracking, the received word is the warp index:

* `epi_of_cnt`: a shuffle state of a default thread whose shuffle count is at least the
  epilogue's (`1 + num_pre + smBase num_iters`) is the epilogue's broadcast (the common start's
  has count 0, a prologue block's is below `1 + num_pre`, a softmax state's below the epilogue's);
* `epi_recv`: DEP-WARP-SHUFFLE gives the operand of lane 0's shuffle of the same instance, since
  lane 0 has not exited before it (`shflLiveD_of`); that shuffle has the count of the thread's, so
  it is lane 0's epilogue broadcast, whose operand is lane 0's warp index, the thread's;
* `epi_bw`: at the load the recorded lane bits are the warp index, so the load's address is the
  warp's lanes (`Prm.taddr` with `bw = w`);
* `sm_recv`: the same for the softmax region's broadcast (`Sm.Site.shfl4`), whose source lane is
  at the broadcast of the same iteration (`shfl_same_site`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface.Lk
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.InklingRelDecode.Proof.Mbar (wordsSo_all)

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

variable (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X) (hf : ThreadFacts Q L mem0 X)
include hpre hX hf

/-- **A shuffle state whose count is at least the epilogue's is the epilogue's broadcast.** -/
theorem epi_of_cnt (hg : g < L.threads) {k : Nat} {e : Event} {s : DComp.St}
    (he : X.get (g, k) = some e) (hσ : St Q L X g k = some (some (.d s)))
    (hsh : shflSt (.d s) = true) (hc : 1 + NP Q L g + Sm.smBase (NI Q L g) ≤ cntF Q L g (.d s)) :
    ∃ d, s = .epi d ∧ d.site = .shfl := by
  cases s with
  | dstart d =>
    exfalso
    have h1 : DStart.dsShfl d.site = true := by rw [← ds_shfl]; exact hsh
    have : d.site ≠ .toProA := by
      intro h; rw [h] at h1; exact absurd h1 (by decide)
    simp [cntF, DStart.dsW, this] at hc
  | pro d =>
    exfalso
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
    simp only [cntF, ProA.proW_lit dt hb, NP] at hc
    omega
  | sm d =>
    exfalso
    obtain ⟨h1, hm, hi⟩ := sm_shfl_facts hpre hX hf hg he hσ hsh
    have h2 := Sm.shfl_lt_next h1 hm
    have h3 := Sm.smBase_le (show d.i + 1 ≤ NI Q L g by omega)
    simp only [cntF, Sm.smW] at hc
    omega
  | epi d =>
    have h1 : Epi.epShfl d.site = true := by rw [← epi_shfl]; exact hsh
    exact ⟨d, rfl, by simpa [Epi.epShfl] using h1⟩

/-- **The epilogue's broadcast receives the thread's warp index.** -/
theorem epi_recv (hg : g < L.threads) {k pc : Nat} {m : ShflMode} {av : Value} {b c : Nat}
    {recv : Value} {ok : Bool} {d : Epi.D} (he : X.get (g, k) = some ⟨pc, .shfl m av b c recv ok⟩)
    (hσ : St Q L X g k = some (some (.d (.epi d)))) (hs : d.site = .shfl) :
    recv = b32 (g % L.block / 32) := by
  have hb : L.block = 256 := hpre.block
  have hdef : g % L.block < 128 := (hf.reach hg hσ).1
  obtain ⟨u, hF⟩ := fired_cont hX hf hg he hσ (by simp [ExitState, hs])
  have hsh0 := Epi.shape (by rw [hb]) (fired_epi hF)
  unfold Epi.Shape at hsh0
  rw [hs] at hsh0
  obtain ⟨recv', ok', he'⟩ := hsh0
  simp only [Event.mk.injEq, Kind.shfl.injEq] at he'
  obtain ⟨-, rfl, rfl, rfl, rfl, -, -⟩ := he'
  have hk : X.ShflK (g, k) (cnt Execution.isShfl X g k) :=
    ⟨⟨_, _, _, _, _, _, _, he⟩, rfl⟩
  obtain ⟨j, pc', b', c', r', o', hk', hget', hw⟩ :=
    shfl_source_d (Q := Q) hX (shflLiveD_of hpre hX hf) hb hg hdef he hk
  set x := shflSrc L g .idx 0 31 with hx_def
  have hx : x < L.threads := hw.1.2.1
  have hxd : x % L.block < 128 := by have := hw.2; omega
  obtain ⟨s, hs'⟩ := Frame.event_state hf.sound hX hf.tracked hget' (fun pc f h => by cases h)
  have hσ' : St Q L X x j = some (some s) := hs'
  have hsh' : shflSt s = true := by
    rw [← isShfl_state hX hf hx hget' hσ']; rfl
  cases s with
  | w s => exact absurd ((cls_inv j _ (event_le hget') hσ').mpr hxd) id
  | d s =>
    have hc := (cnt_inv hpre hX hf hg k (event_le he) hσ)
    have hc' := (cnt_inv hpre hX hf hx j (event_le hget') hσ').1
    have hcx : cnt Execution.isShfl X x j = cnt Execution.isShfl X g k := hk'.2
    obtain ⟨e1, e2, -⟩ := np_ni_eq (Q := Q) hw.1.2.2
    have hge : 1 + NP Q L x + Sm.smBase (NI Q L x) ≤ cntF Q L x (.d s) := by
      rw [← hc', hcx, hc.1, ← e1, ← e2]
      simp only [cntF]
      omega
    obtain ⟨d2, rfl, hs2⟩ := epi_of_cnt hpre hX hf hx hget' hσ' hsh' hge
    obtain ⟨u2, hF2⟩ := fired_cont hX hf hx hget' hσ' (by simp [ExitState, hs2])
    have hsh2 := Epi.shape (by rw [hb]) (fired_epi hF2)
    unfold Epi.Shape at hsh2
    rw [hs2] at hsh2
    obtain ⟨recv2, ok2, he2⟩ := hsh2
    simp only [Event.mk.injEq, Kind.shfl.injEq] at he2
    obtain ⟨-, -, rfl, -, -, -, -⟩ := he2
    have hm2 : Epi.Means Q L x d2.pr := (hf.reach hx hσ').2
    rw [hm2.w]
    exact congrArg b32 hw.2.symm


/-- **The softmax region's broadcast receives the thread's warp index**: lane 0's shuffle of the
same instance is its broadcast of the same iteration (`shfl_same_site`), whose operand is its warp
index. -/
theorem sm_recv (hg : g < L.threads) {k pc : Nat} {m : ShflMode} {av : Value} {b c : Nat}
    {recv : Value} {ok : Bool} {d : Sm.D} (he : X.get (g, k) = some ⟨pc, .shfl m av b c recv ok⟩)
    (hσ : St Q L X g k = some (some (.d (.sm d)))) (hs : d.site = .shfl4) :
    recv = b32 (g % L.block / 32) := by
  have hb : L.block = 256 := hpre.block
  have hdef : g % L.block < 128 := (hf.reach hg hσ).1
  obtain ⟨u, hF⟩ := fired_cont hX hf hg he hσ (by simp [ExitState])
  obtain ⟨recv', ok', he'⟩ := Sm.shape_shfl4 (fired_sm hF) hs
  simp only [Event.mk.injEq, Kind.shfl.injEq] at he'
  obtain ⟨-, rfl, rfl, rfl, rfl, -, -⟩ := he'
  have hk : X.ShflK (g, k) (cnt Execution.isShfl X g k) :=
    ⟨⟨_, _, _, _, _, _, _, he⟩, rfl⟩
  obtain ⟨j, pc', b', c', r', o', hk', hget', hw⟩ :=
    shfl_source_d (Q := Q) hX (shflLiveD_of hpre hX hf) hb hg hdef he hk
  set x := shflSrc L g .idx 0 31 with hx_def
  have hx : x < L.threads := hw.1.2.1
  obtain ⟨s, hs'⟩ := Frame.event_state hf.sound hX hf.tracked hget' (fun pc f h => by cases h)
  have hσ' : St Q L X x j = some (some s) := hs'
  obtain ⟨d2, rfl, hs2, -⟩ := shfl_same_site hpre hX hf hw hk hk' hσ hσ' hdef
  obtain ⟨u2, hF2⟩ := fired_cont hX hf hx hget' hσ' (by simp [ExitState])
  obtain ⟨recv2, ok2, he2⟩ := Sm.shape_shfl4 (fired_sm hF2) (hs2.trans hs)
  simp only [Event.mk.injEq, Kind.shfl.injEq] at he2
  obtain ⟨-, -, rfl, -, -, -, -⟩ := he2
  exact congrArg b32 hw.2.symm

end
end PTX.Kernels.InklingRelDecode.Proof.Interface.Lk
