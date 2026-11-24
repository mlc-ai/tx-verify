-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerStoreFacts
public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerClc

@[expose] public section

/-! # A consumer's values at its slices, along an execution

Projections of `ConsInv` (`ValRel`, `OutTile`) and of `ClcPollInv`: at a slice's second output
barrier the slice's sixteen staging stores wrote the packed halves of the accumulator entries, each
the word of a load of the tile, made one accumulator arrival before (`cons_slice_values_fact`);
the output barrier arrivals there and at a TMA store count the tile's slices, and at the TMA store
the response polls are the accumulator arrivals (`cons_tma_epoch_fact`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

/-- **A slice's values.** At a slice's second output barrier, on a trace without undefined
behaviour: element `m` of the slice's staging stores wrote the packed halves of accumulator entries
`32 s + 8 (m / 4) + 2 (m % 4)` and the next; each entry of chunk `ch` is word `w` of a load of the
chunk made one accumulator arrival before; and the output barrier arrivals are sixteen per
accumulator arrival, less the slice's remaining fifteen less `2 s`. -/
theorem cons_slice_values_fact {X : Execution} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Prod mem0 X) (hg : g < L.threads) {k : Nat}
    (hk : k < (X.tr g).length) {c : Consumer.D} {s : Fin 8}
    (hσ : (code L g).toMachine.after (some (code L g).init) ((X.tr g).take k) =
      some (some (.inr (.cons c))))
    (hs : c.site = .barB s) (hub : ∀ j pc f, X.get (g, j) ≠ some ⟨pc, .ub f⟩) :
    (∀ m, m < 16 → ∃ pc a bs, X.get (g, k - 16 + m) = some ⟨pc, .wr a bs⟩ ∧
      bs = (Consumer.storeWord c.acc s (m / 4) (m % 4)).toBytes) ∧
    (∀ ch, ch < 16 → ∃ kl pc vals, kl < k ∧
      X.get (g, kl) =
        some ⟨pc, .tc (.ld (256 * (Consumer.tidOf L g / 32 / 4) + 16 * ch) vals .s32x32b)⟩ ∧
      (∀ w, w < 16 → vals[w]? = some (c.acc (16 * ch + w))) ∧
      arrivals (Bar.loc L (2 * (g / L.block / 2)) ⟨.acc, Consumer.tidOf L g / 32 / 4, false⟩)
          ((X.tr g).take kl) + 1 =
        arrivals (Bar.loc L (2 * (g / L.block / 2)) ⟨.acc, Consumer.tidOf L g / 32 / 4, false⟩)
          ((X.tr g).take k)) ∧
    Consumer.outBars L g ((X.tr g).take k) + 16 =
      16 * arrivals (Bar.loc L (2 * (g / L.block / 2)) ⟨.acc, Consumer.tidOf L g / 32 / 4, false⟩)
        ((X.tr g).take k) + (2 * s.val + 1) := by
  have htr := Frame.trace (fun _ => sound hpre) hX hg
  obtain ⟨-, -, -, -, -, hO, -, ⟨-, hL, hS⟩, -⟩ : ConsInv L g (.inr (.cons c)) ((X.tr g).take k) :=
    consInv hpre hg htr k _ hσ
  have hnu : ∀ e ∈ (X.tr g).take k, ∀ f, e.kind ≠ .ub f := by
    intro e he f hef
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp he
    have hjk : j < k := by
      have := (List.getElem?_eq_some_iff.mp hj).1
      simp only [List.length_take] at this
      omega
    rw [List.getElem?_take_of_lt hjk] at hj
    obtain ⟨pc, kd⟩ := e
    simp only at hef
    subst hef
    exact hub j pc f hj
  have hlen : ((X.tr g).take k).length = k := by
    simp only [List.length_take]; omega
  obtain ⟨-, hst⟩ := hS hnu s 16 (by simp [Consumer.D.storePos, hs])
  rw [hlen] at hst
  refine ⟨fun m hm => ?_, fun ch hch => ?_, ?_⟩
  · obtain ⟨pc, a, bs, h1, h2⟩ := hst m hm
    refine ⟨pc, a, bs, ?_, h2⟩
    have hk16 : k - 16 + m < k := by
      have := (List.getElem?_eq_some_iff.mp h1).1
      rw [hlen] at this
      exact this
    rw [List.getElem?_take_of_lt hk16] at h1
    exact h1
  · obtain ⟨kl, pc, vals, hkl, h1, h2, h3⟩ := hL ch (by simp [Consumer.D.loaded, hs]; omega)
    rw [hlen] at hkl
    rw [List.getElem?_take_of_lt hkl] at h1
    rw [List.take_take, Nat.min_eq_left hkl.le] at h3
    simp only [Consumer.D.inEpi, hs] at h3
    exact ⟨kl, pc, vals, hkl, h1, h2, h3⟩
  · have h := hO.1
    simp only [Consumer.D.inEpi, Consumer.D.outPhase, hs] at h
    omega

/-- **A TMA store's tile counts.** At a consumer's TMA store of slice `s`, its output barrier
arrivals are sixteen per accumulator arrival, less fourteen less `2 s`, and its successful response
polls are its accumulator arrivals. -/
theorem cons_tma_epoch_fact {X : Execution} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Prod mem0 X) (hg : g < L.threads) {k : Nat} {c : Consumer.D}
    {s : Fin 8}
    (hσ : (code L g).toMachine.after (some (code L g).init) ((X.tr g).take k) =
      some (some (.inr (.cons c))))
    (hs : c.site = .tma s) :
    Consumer.outBars L g ((X.tr g).take k) + 16 =
      16 * arrivals (Bar.loc L (2 * (g / L.block / 2)) ⟨.acc, Consumer.tidOf L g / 32 / 4, false⟩)
        ((X.tr g).take k) + (2 * s.val + 2) ∧
    okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take k) =
      arrivals (Bar.loc L (2 * (g / L.block / 2)) ⟨.acc, Consumer.tidOf L g / 32 / 4, false⟩)
        ((X.tr g).take k) := by
  have htr := Frame.trace (fun _ => sound hpre) hX hg
  obtain ⟨-, -, -, -, -, hO, -⟩ : ConsInv L g (.inr (.cons c)) ((X.tr g).take k) :=
    consInv hpre hg htr k _ hσ
  obtain ⟨-, hP, -⟩ := clcPoll_inv hpre hg htr k _ hσ
  refine ⟨?_, ?_⟩
  · have h := hO.1
    simp only [Consumer.D.inEpi, Consumer.D.outPhase, hs] at h
    omega
  · simp only [Consumer.tileOpen, hs, Nat.add_zero] at hP
    exact hP

end

end PTX.Kernels.Fp16Gemm8192.Proof
