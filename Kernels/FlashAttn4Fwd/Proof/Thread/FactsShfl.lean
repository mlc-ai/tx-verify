-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.Tracked
public import Kernels.FlashAttn4Fwd.Proof.Interface.Floats

@[expose] public section

/-! # The shuffle fields of `FloatFacts`

Every shuffle of the kernel is a full-warp `shfl.sync.idx` from lane 0 whose source is the value
the state before it expects (`shfl_form` of `Tracked.lean`, `opv`). Two lanes of a warp at their
`n`-th shuffles are at states with the same shuffle count (`shflJ`), and the expected value is a
function of the warp and that count (`opv_eq`); a lane at its exit has made more shuffles than
any lane of its warp makes (`exit_cnt`). These give, in an execution whose threads the machine
follows:

* `FloatFacts_shfl_form`: every shuffle is `idx` from lane 0 over the full warp;
* `FloatFacts_shfl_uniform`: the `n`-th shuffles of two lanes of a warp have one source value;
* `FloatFacts_shfl_live`: lane 0 of a warp does not exit before its `n`-th shuffle when a lane of
  the warp makes one. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Cross
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

variable (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X)
include hpre hX ht

/-- The state before a thread's event, with the shuffle-count run invariant and the role's
warp. -/
theorem shfl_origin {g k : Nat} {e : Event} (he : X.get (g, k) = some e)
    (hub : ∀ pc f, e ≠ ⟨pc, .ub f⟩) :
    ∃ d t ins o, Frame.stateAt (code L) X g k = some (some d) ∧
      shflJ L g d ((X.tr g).take k) ∧ (code L g).AtD d t ∧ (code L g).inv d ∧
      kernel.code[(code L g).pc d]? = some ins ∧
      Fires ((code L g).pc d) (eventTmpl asms L g t ins.op) e o ∧
      ∀ r, d = .inr r → r.kind.Warp (warpOf L g) := by
  obtain ⟨d, t, ins, o, hσ, hJ, hat, hi, hc, hf⟩ :=
    event_origin hpre hX ht (J := shflJ L) (fun _ hg => shflJ_run hpre hg) he hub
  have hg := Frame.lt_of_get hX he
  refine ⟨d, t, ins, o, hσ, hJ, hat, hi, hc, hf, ?_⟩
  rintro r rfl
  exact role_warp_run hpre hg (Frame.trace (C := code L) (fun _ hg => sound hpre hg) hX hg) k r hσ

/-- A shuffle event is its state's broadcast of the expected value, at a shuffle site. -/
theorem shfl_event {g k pc b c : Nat} {md : ShflMode} {a recv : Value} {ok : Bool}
    (he : X.get (g, k) = some ⟨pc, .shfl md a b c recv ok⟩) :
    ∃ d, Frame.stateAt (code L) X g k = some (some d) ∧ shflJ L g d ((X.tr g).take k) ∧
      (code L g).inv d ∧ (∀ r, d = .inr r → r.kind.Warp (warpOf L g)) ∧
      isShflSite d = true ∧ md = .idx ∧ a = opv L g d ∧ b = 0 ∧ c = 31 := by
  obtain ⟨d, t, ins, o, hσ, hJ, hat, hi, hc, hf, hk⟩ := shfl_origin hpre hX ht he nofun
  obtain ⟨hs, recv', ok', he'⟩ := shfl_form hat hc hf rfl
  simp only [Event.mk.injEq, Kind.shfl.injEq] at he'
  obtain ⟨-, h1, h2, h3, h4, -, -⟩ := he'
  exact ⟨d, hσ, hJ, hi, hk, hs, h1, h2, h3, h4⟩

/-- **Every shuffle is a full-warp `shfl.sync.idx` from lane 0.** -/
theorem _root_.PTX.Kernels.FlashAttn4Fwd.Proof.FloatFacts_shfl_form :
    ∀ {g i pc b c : Nat} {md : ShflMode} {a recv : Value} {ok : Bool}, g < L.threads →
      X.get (g, i) = some ⟨pc, .shfl md a b c recv ok⟩ → md = .idx ∧ b = 0 ∧ c = 31 := by
  intro g i pc b c md a recv ok _ he
  obtain ⟨-, -, -, -, -, -, h1, -, h3, h4⟩ := shfl_event hpre hX ht he
  exact ⟨h1, h3, h4⟩

/-- **The `n`-th shuffles of two lanes of a warp have the same source value.** -/
theorem _root_.PTX.Kernels.FlashAttn4Fwd.Proof.FloatFacts_shfl_uniform :
    ∀ {g h i j n pc pc' b b' c c' : Nat} {md md' : ShflMode}
      {a a' r r' : Value} {o o' : Bool}, SameWarp L g h → X.ShflK (g, i) n →
      X.ShflK (h, j) n →
      X.get (g, i) = some ⟨pc, .shfl md a b c r o⟩ →
      X.get (h, j) = some ⟨pc', .shfl md' a' b' c' r' o'⟩ → a = a' := by
  intro g h i j n pc pc' b b' c c' md md' a a' r r' o o' hw hKg hKh heg heh
  obtain ⟨dg, -, hJg, hig, hkg, hsg, -, rfl, -⟩ := shfl_event hpre hX ht heg
  obtain ⟨dh, -, hJh, hih, hkh, hsh, -, rfl, -⟩ := shfl_event hpre hX ht heh
  refine opv_eq hpre hw hJg hJh hig hih hkg hkh hsg hsh ?_
  rw [← hJg.2.1, ← hJh.2.1]
  exact hKg.2.trans hKh.2.symm

/-- **Lane 0 of a warp does not exit before its `n`-th shuffle** when a lane of the warp makes
one. -/
theorem _root_.PTX.Kernels.FlashAttn4Fwd.Proof.FloatFacts_shfl_live :
    ∀ {g i n : Nat}, g < L.threads → X.ShflK (g, i) n →
      ¬ ShflExited X (g - laneOf L g) n := by
  intro g i n hg hK ⟨k, pc, hex, hcnt⟩
  obtain ⟨⟨pcs, md, a, b, c, r, o, he⟩, hn⟩ := hK
  obtain ⟨dg, -, hJg, hig, hkg, hsg, -⟩ := shfl_event hpre hX ht he
  have hpos : 0 < L.block := by rw [hpre.block]; decide
  obtain ⟨hw0, -⟩ := laneZero_sameWarp hpos hg
  obtain ⟨d0, t0, ins0, o0, -, hJ0, hat0, hi0, hc0, hf0, hk0⟩ :=
    shfl_origin hpre hX ht hex nofun
  have hret : retOp ins0.op = true := retOp_of_fires hf0 rfl
  have hpc := OpPcsFast.mem kernel_ret_pcs hc0 hret
  simp only [List.mem_singleton] at hpc
  have hlt := exit_cnt hpre hw0 hJg hJ0 hig hi0 hkg hk0 hsg hpc
  rw [← hJg.2.1, ← hJ0.2.1] at hlt
  change ((X.tr g).take i).countP Execution.isShfl = n at hn
  omega

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Cross
