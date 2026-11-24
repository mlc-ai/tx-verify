-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Step.WarpBatch
public import Lemmas.Snoc.ExtensionWaitFrame
public import Lemmas.Tcgen05.TcExtend

@[expose] public section

/-! # The lanes of a warp and fresh instance labels

A proof tool for the warp collectives. `warpThreads L g` lists the threads of `g`'s warp; in a
CTA whose size is a multiple of 32 it has a thread for every lane (`warp_full`). Election and
warp-barrier instances are labels only (DEP-WARP-ELECT, DEP-WARP-BARRIER), so a new instance takes a
label no earlier election or warp barrier has (`exists_fresh_label`). A batch of one collective
kind keeps the matching of the two others (`appendLanes_shflOk_of_not_shfl`,
`appendLanes_electOk_of_not_elect`, `appendLanes_warpBarOk_of_not_warpBar`). -/

namespace PTX.Step
open PTX AsyncCopy Classical
noncomputable section

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}
  {ds : List Nat} {ev : Nat → Event}

theorem sameWarp_trans {a b c : Nat} (h1 : SameWarp L a b) (h2 : SameWarp L b c) :
    SameWarp L a c :=
  ⟨⟨h1.1.1, h2.1.2.1, h1.1.2.2.trans h2.1.2.2⟩, h1.2.trans h2.2⟩

/-- The threads of `g`'s warp. -/
def warpThreads (L : Launch) (g : Nat) : List Nat :=
  (List.range L.threads).filter fun h => decide (SameWarp L g h)

theorem mem_warpThreads {g h : Nat} : h ∈ warpThreads L g ↔ SameWarp L g h := by
  simp only [warpThreads, List.mem_filter, List.mem_range, decide_eq_true_eq]
  exact ⟨fun h => h.2, fun hs => ⟨hs.1.2.1, hs⟩⟩

theorem warpThreads_nodup (g : Nat) : (warpThreads L g).Nodup :=
  (List.nodup_range).filter _

theorem warpThreads_ne_nil {g : Nat} (hg : g < L.threads) : warpThreads L g ≠ [] :=
  List.ne_nil_of_mem (mem_warpThreads.mpr ⟨⟨hg, hg, rfl⟩, rfl⟩)

/-- In a CTA whose size is a multiple of 32, every lane of a warp is a thread: lane `lane` of
`g`'s warp is `g - laneOf L g + lane`. -/
theorem sameWarp_lane (hb : L.block % 32 = 0) {g : Nat} (hg : g < L.threads) {lane : Nat}
    (hl : lane < 32) :
    SameWarp L g (g - laneOf L g + lane) ∧ laneOf L (g - laneOf L g + lane) = lane := by
  unfold laneOf
  have hB : 0 < L.block := by
    rcases Nat.eq_zero_or_pos L.block with h0 | h0
    · simp [Launch.threads, h0] at hg
    · exact h0
  have hr := Nat.mod_lt g hB
  have hd := Nat.div_add_mod g L.block
  obtain ⟨b, hbk⟩ : ∃ b, L.block = 32 * b := ⟨L.block / 32, by omega⟩
  have hw := Nat.div_add_mod (g % L.block) 32
  have hlt : g % L.block - g % L.block % 32 + lane < L.block := by
    have h0 : g % L.block < 32 * b := by rw [← hbk]; exact hr
    have h1 : g % L.block / 32 < b := by omega
    omega
  have hmod : (g - g % L.block % 32 + lane) % L.block = g % L.block - g % L.block % 32 + lane := by
    have he : g - g % L.block % 32 + lane =
        (g % L.block - g % L.block % 32 + lane) + L.block * (g / L.block) := by omega
    rw [he, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
  have hdiv : (g - g % L.block % 32 + lane) / L.block = g / L.block := by
    have he : g - g % L.block % 32 + lane =
        (g % L.block - g % L.block % 32 + lane) + L.block * (g / L.block) := by omega
    rw [he, Nat.add_mul_div_left _ _ hB, Nat.div_eq_of_lt hlt, Nat.zero_add]
  have hth : g - g % L.block % 32 + lane < L.threads := by
    have h1 : g / L.block < L.grid := by
      unfold Launch.threads at hg
      exact (Nat.div_lt_iff_lt_mul hB).mpr hg
    have h2 := Nat.div_add_mod (g - g % L.block % 32 + lane) L.block
    rw [hdiv, hmod] at h2
    unfold Launch.threads
    have h3 : L.block * (g / L.block) + L.block ≤ L.grid * L.block := by
      rw [Nat.mul_comm L.grid]
      exact (Nat.mul_succ L.block _).symm ▸ Nat.mul_le_mul_left _ h1
    omega
  refine ⟨⟨⟨hg, hth, hdiv.symm⟩, ?_⟩, ?_⟩
  · rw [hmod]
    omega
  · rw [hmod]
    omega

theorem warp_full (hb : L.block % 32 = 0) {g : Nat} (hg : g < L.threads) {lane : Nat}
    (hl : lane < 32) : ∃ h, SameWarp L g h ∧ laneOf L h = lane :=
  ⟨_, sameWarp_lane hb hg hl⟩

/-- The instance label of an election or a warp barrier. -/
def instLabel (e : Event) : Nat :=
  match e.kind with
  | .elect _ inst _ => inst
  | .warpBar _ inst => inst
  | _ => 0

/-- A label that no election or warp barrier of the execution has. -/
theorem exists_fresh_label (hX : Consistent L K A mem0 X) :
    ∃ inst, ∀ e q, X.get e = some q → instLabel q ≠ inst := by
  refine ⟨((((List.range L.threads).flatMap X.tr).map instLabel).sum + 1), fun e q hq hl => ?_⟩
  have he : e.1 < L.threads := by
    by_contra hn
    have := len_of_get hq
    rw [hX.outside e.1 (by omega)] at this
    simp at this
  have hm : q ∈ (List.range L.threads).flatMap X.tr :=
    List.mem_flatMap.mpr ⟨e.1, List.mem_range.mpr he, List.mem_of_getElem? hq⟩
  have := List.le_sum_of_mem (List.mem_map_of_mem (f := instLabel) hm)
  omega

/-- Lane `laneOf L h` of the warp of a thread `g` of `h`'s warp is `h`. -/
theorem warpLane_of_sameWarp {g h : Nat} (hs : SameWarp L g h) : warpLane L g (laneOf L h) = h := by
  obtain ⟨⟨-, -, hc⟩, hw⟩ := hs
  unfold warpLane laneOf
  have h1 := Nat.div_add_mod g L.block
  have h2 := Nat.div_add_mod h L.block
  have h3 := Nat.div_add_mod (g % L.block) 32
  have h4 := Nat.div_add_mod (h % L.block) 32
  rw [hc] at h1
  rw [hw] at h3
  generalize L.block * (h / L.block) = t at h1 h2
  generalize 32 * (h % L.block / 32) = w at h3 h4
  omega

/-- A new event of no vote kind and no exit is the dependency source of no vote (DEP-WARP-VOTE):
the source of `MaskWait` is an event of the class or an exit. -/
theorem appendLanes_not_voteWait {h : Nat} (hh : h ∈ ds) (hc : voteClass (ev h).kind = none)
    (hx : (ev h).kind ≠ .exit) {j : EvId} :
    ¬ MaskWait L voteClass (X.appendLanes ds ev) (h, (X.tr h).length) j := by
  rintro ⟨-, m, n, q, -, ⟨-, q', p, hg, hp, -⟩ | ⟨-, ⟨pc, hg⟩, -⟩⟩
  · rw [appendLanes_get_new hh] at hg
    cases hg
    rw [hc] at hp
    cases hp
  · rw [appendLanes_get_new hh] at hg
    exact hx (congrArg Event.kind (Option.some.inj hg))

/-- A batch without shuffles keeps the shuffle matching. -/
theorem appendLanes_shflOk_of_not_shfl (hX : Consistent L K A mem0 X)
    (hn : ∀ h ∈ ds, ∀ m a b c recv ok, (ev h).kind ≠ .shfl m a b c recv ok) :
    ShflOk L (X.appendLanes ds ev) := by
  have hget {i : EvId} {pc : Nat} {m : ShflMode} {a : Value} {b c : Nat} {r : Value} {o : Bool} :
      (X.appendLanes ds ev).get i = some ⟨pc, .shfl m a b c r o⟩ ↔
        X.get i = some ⟨pc, .shfl m a b c r o⟩ :=
    appendLanes_get_kind (fun h hh => hn h hh _ _ _ _ _ _)
  apply Proof.ExtensionWait.shflOk hX le_appendLanes hget
  intro i n
  constructor
  · rintro ⟨⟨pc, m, a, b, c, r, o, hs⟩, hk⟩
    have hs' := hget.mp hs
    exact ⟨⟨pc, m, a, b, c, r, o, hs'⟩, by rwa [appendLanes_take (len_of_get hs').le] at hk⟩
  · rintro ⟨⟨pc, m, a, b, c, r, o, hs⟩, hk⟩
    exact ⟨⟨pc, m, a, b, c, r, o, hget.mpr hs⟩, by rwa [appendLanes_take (len_of_get hs).le]⟩

/-- A batch without elections keeps the election matching. -/
theorem appendLanes_electOk_of_not_elect (hX : Consistent L K A mem0 X)
    (hn : ∀ h ∈ ds, ∀ mask inst leader, (ev h).kind ≠ .elect mask inst leader) :
    ElectOk L (X.appendLanes ds ev) := by
  have hiff {i : EvId} {pc mask inst leader : Nat} :
      (X.appendLanes ds ev).Elect i pc mask inst leader ↔ X.Elect i pc mask inst leader :=
    appendLanes_get_kind (fun h hh => hn h hh _ _ _)
  simpa only [ElectOk, hiff] using hX.elect

/-- A batch without warp barriers keeps the warp-barrier matching. -/
theorem appendLanes_warpBarOk_of_not_warpBar (hX : Consistent L K A mem0 X)
    (hn : ∀ h ∈ ds, ∀ mask inst, (ev h).kind ≠ .warpBar mask inst) :
    WarpBarOk L (X.appendLanes ds ev) := by
  have hiff {i : EvId} {mask inst : Nat} :
      (X.appendLanes ds ev).WarpBar i mask inst ↔ X.WarpBar i mask inst :=
    exists_congr fun _ => appendLanes_get_kind (fun h hh => hn h hh _ _)
  simpa only [WarpBarOk, hiff] using hX.warpBar

/-- A new event that is no shuffle has no shuffle ordinal. -/
theorem appendLanes_not_shflK_new {h n : Nat} (hh : h ∈ ds)
    (hn : ∀ m a b c recv ok, (ev h).kind ≠ .shfl m a b c recv ok) :
    ¬ (X.appendLanes ds ev).ShflK (h, (X.tr h).length) n := by
  rintro ⟨⟨pc, m, a, b, c, r, o, hs⟩, -⟩
  rw [appendLanes_get_new hh] at hs
  exact hn m a b c r o (congrArg Event.kind (Option.some.inj hs))

end
end PTX.Step
