-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Prologue.Strict.Ld2
import Kernels.InklingRelDecode.Proof.Lib.Coordinates

@[expose] public section

/-! # The strict step of the third request load -/

namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Strict
open PTX PTX.Proof PTX.Flow PTX.Flow.Havoc PTX.Flow.Tagged Control Arith32

set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {g : Nat} {w : Value}
variable (a y p : Nat) (won : Bool) (bcast : Value) (v : Data.Vals)

/-- The state at the third request load, once the first two words are known. -/
abbrev dLd : Data.D := ⟨⟨.ld 2, .bits 32 (BitVec.ofNat 64 a), .bits 32 (BitVec.ofNat 64 y),
  .bits 32 (BitVec.ofNat 64 p), won, bcast⟩, v⟩

/-- The facts after the load are those of the span's first cut (no step). -/
theorem seq_start : SegQ kernel Assumptions.all L g (QT proQt) 42
    ([(612, .bits 32 (BitVec.ofNat 64 p))] ++ dFacts Q L g w (dLd a y p won bcast v)) 42
    (dFactsAt Q L g w (dSeq a y p won bcast v) 42) := by
  intro t ht hq
  obtain ⟨hp, hs, ha, hf, hr⟩ := ht
  refine ⟨t, .refl, ⟨hp, hs, ha, hf, holds_of_forall fun q hq' => ?_⟩, hq⟩
  simp only [dFactsAt, List.mem_append] at hq'
  rcases hq' with hq' | hq'
  · exact holds_mem hr (List.mem_append_right _ (List.mem_append_left _ hq'))
  · obtain ⟨r, hr', rfl⟩ := List.mem_map.mp hq'
    have key : ∀ r ∈ ctlLive 42, r = 612 ∨ r ∈ ctlLive 41 := by decide +kernel
    rcases key r hr' with rfl | h41
    · exact holds_mem hr (List.mem_append_left _ List.mem_cons_self)
    · exact holds_mem hr (List.mem_append_right _ (List.mem_append_right _
        (mem_factsFrom (val := valueOf Q L g w (dLd a y p won bcast v).c) h41)))

/-- **The sequence span**: from the third request word to the first election. -/
theorem seq_span (hb : g % L.block < 256) (hs0 : 0 < Q.splits)
    (hs1 : (L.ctaidOf (g / L.block)).get .x < Q.splits) (hs2 : Q.splits + 2 ^ 24 < 2 ^ 31)
    (hp : p + 511 < 2 ^ 31) :
    SegQ kernel Assumptions.all L g (QT proQt) 42
      ([(612, .bits 32 (BitVec.ofNat 64 p))] ++ dFacts Q L g w (dLd a y p won bcast v)) 130
      (dFacts Q L g w (dSeq a y p won bcast v)) :=
  (seq_start a y p won bcast v).comp ((seqA a y p won bcast v).comp
    ((seqD a y p won bcast v hs0 hs1 hs2 hp).comp (seqC a y p won bcast v hb)))

/-- **The third request load** strictly steps to the first election. -/
theorem step_ld2 {m} (hp : Pre Q L m) (hg : g < L.threads) (d : Data.D) (hs : d.c.site = .ld 2)
    (hk : Ok Q L g d) (e : Event) :
    (Data.code Q L g w).StepForQ (QT proQt) (Wf Q L g) d e := by
  obtain ⟨⟨s, a0, b0, c0, won, bcast⟩, vs⟩ := d
  cases hs
  have ha : a0 = b32 (Q.qStart (reqOf L g)) := hk.1.first (by change 34 < 41; decide)
  have hb : b0 = b32 (Q.qStart (reqOf L g + 1)) := hk.1.last (by change 37 < 41; decide)
  subst ha hb
  intro t u ins hat hinv hc hq hw hf
  obtain ⟨hseq, hpay⟩ := hinv
  subst hseq
  obtain ⟨hx, -, hr⟩ := Lib.coordinate_bounds hp hg
  have hblk : g % L.block < 256 := by
    have := hp.block
    have := Nat.mod_lt g (show L.block > 0 by omega)
    omega
  refine Code.ldWQ (C := Data.code Q L g w) (qt := proQt) (ex := [])
    (P := fun v => v = b32 (requestWord Q (reqOf L g) 2)) (r := 612)
    (d := ⟨⟨.ld 2, b32 (Q.qStart (reqOf L g)), b32 (Q.qStart (reqOf L g + 1)), b32 0, won,
      bcast⟩, vs⟩)
    (f := fun v => ⟨⟨.el 0, b32 (Q.qStart (reqOf L g)), b32 (Q.qStart (reqOf L g + 1)), v, won,
      bcast⟩, vs⟩)
    Flow.code_41 rfl rfl rfl rfl ?_ ?_ rfl rfl ?_ (fun _ _ => typed_nil') ?_ ?_ ?_ e ins hat
    ⟨rfl, hpay⟩ hc hq hw hf
  · exact fun e hWf hpc x bs hk => ⟨_, hWf.1 2 hpc x bs hk, rfl⟩
  · ld_hn
  · ld_fr 41 612 (.ld 2)
  · exact ld_hv (n := 42) (r := 612) (by decide +kernel)
  · exact ld_hq (n := 41) (r := 612) (by decide +kernel)
  · intro v hv
    subst hv
    refine ⟨rfl, rfl, ⟨trivial, ⟨fun _ => rfl, fun _ => ⟨_, rfl⟩⟩⟩, ?_⟩
    rw [code_facts_ld2 (w := w) _ rfl vs (b32 (requestWord Q (reqOf L g) 2))]
    exact dFacts_seg (pre := [(612, _)]) (seq_span _ _ _ won bcast vs hblk hp.splitsPos hx
      hp.splitsRange (by have := hp.seqRange _ hr; simp only [requestWord, reqOf]; omega))

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Strict
