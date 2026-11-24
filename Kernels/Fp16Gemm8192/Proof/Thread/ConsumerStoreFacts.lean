-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerOutFacts
public import Kernels.Fp16Gemm8192.Proof.Thread.RoleWarp
public import Kernels.Fp16Gemm8192.Proof.Thread.GlobalWrites

@[expose] public section

/-! # A consumer's staging stores and TMA stores, along an execution

Projections of `ConsInv` and of the consumer's events at the sites of its epilogue: the sixteen
staging stores a thread has made when it arrives at a slice's second output barrier
(`cons_slice_stores_fact`), the barrier arrival and the proxy fence that precede its TMA store
(`cons_tma_prev_fact`), the TMA store's specification (`cons_tma_fact`) and the length of its
writes (`cons_write_len_fact`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

/-- A consumer thread is in one of the two consumer warp groups. -/
theorem cons_tid_lt {X : Execution} (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (hg : g < L.threads) {k : Nat} (hk : k ≤ (X.tr g).length) {c : Consumer.D}
    (hσ : (code L g).toMachine.after (some (code L g).init) ((X.tr g).take k) =
      some (some (.inr (.cons c)))) : Consumer.tidOf L g < 256 := by
  have hrw := role_warp hpre hX hg _ hk _ hσ
  simp only [roleWarp, Prologue.warpOf] at hrw
  simp only [Consumer.tidOf]
  omega

/-- A thread at a slice's second output barrier, on a trace without undefined behaviour, has just
made
the slice's sixteen staging stores: element `m` is the write, at index `k - 16 + m`, of the four
bytes of chunk `m / 4` and element `m % 4` of the staging buffer of the slice's parity. -/
theorem cons_slice_stores_fact {X : Execution} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Prod mem0 X) (hg : g < L.threads) {k : Nat}
    (hk : k < (X.tr g).length) {c : Consumer.D} {s : Fin 8}
    (hσ : (code L g).toMachine.after (some (code L g).init) ((X.tr g).take k) =
      some (some (.inr (.cons c))))
    (hs : c.site = .barB s) (hub : ∀ j pc f, X.get (g, j) ≠ some ⟨pc, .ub f⟩) :
    16 ≤ k ∧ ∀ m, m < 16 → ∃ pc a bs, X.get (g, k - 16 + m) = some ⟨pc, .wr a bs⟩ ∧
      a.loc = ⟨.shared, g / L.block, L.sharedBase +
        Consumer.stagingOff (Consumer.tidOf L g) (s.val % 2) (m / 4) (m % 4)⟩ ∧
      a.size = 4 ∧ bs.length = 4 := by
  have htr := Frame.trace (fun _ => sound hpre) hX hg
  obtain ⟨-, -, -, -, -, -, -, hS, -⟩ : ConsInv L g (.inr (.cons c)) ((X.tr g).take k) :=
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
  obtain ⟨hle, hst⟩ := hS.1 hnu s 16 (by simp [Consumer.D.storePos, hs])
  have hlen : ((X.tr g).take k).length = k := by
    simp only [List.length_take]; omega
  rw [hlen] at hle hst
  refine ⟨hle, fun m hm => ?_⟩
  obtain ⟨pc, a, bs, h1, h2, h3, h4⟩ := hst m hm
  refine ⟨pc, a, bs, ?_, h2, h3, h4⟩
  rw [List.getElem?_take_of_lt (by omega)] at h1
  exact h1

/-- A thread at its TMA store has made, as its two latest events, its output barrier arrival and its
proxy fence. -/
theorem cons_tma_prev_fact {X : Execution} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Prod mem0 X) (hg : g < L.threads) {k : Nat}
    (hk : k < (X.tr g).length) {c : Consumer.D} {s : Fin 8}
    (hσ : (code L g).toMachine.after (some (code L g).init) ((X.tr g).take k) =
      some (some (.inr (.cons c)))) (hs : c.site = .tma s) :
    2 ≤ k ∧ (∃ pc, X.get (g, k - 2) = some ⟨pc, .bar (Consumer.outId L g) (some 128)⟩) ∧
      ∃ pc, X.get (g, k - 1) = some ⟨pc, .fenceProxy (.async (some (.shared .cta))) none⟩ := by
  have htr := Frame.trace (fun _ => sound hpre) hX hg
  obtain ⟨-, -, -, hfen, -, -, -, -, hbar, -⟩ : ConsInv L g (.inr (.cons c)) ((X.tr g).take k) :=
    consInv hpre hg htr k _ hσ
  have hlen : ((X.tr g).take k).length = k := by
    simp only [List.length_take]; omega
  obtain ⟨hl2, pcb, hb⟩ := hbar.2 s hs
  obtain ⟨pcf, hf⟩ := hfen s hs
  rw [hlen] at hl2 hb
  refine ⟨hl2, ⟨pcb, ?_⟩, ⟨pcf, ?_⟩⟩
  · rw [List.getElem?_take_of_lt (by omega)] at hb
    exact hb
  · rw [List.getLast?_eq_getElem?, hlen, List.getElem?_take_of_lt (by omega)] at hf
    exact hf

/-- A tensor store is a consumer's slice's: valid, through the output map, from the staging buffer
of
the slice's parity. -/
theorem cons_tma_fact {X : Execution} (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    {k pc a : Nat} {sp : TensorStore.Spec} {d : ThreadD}
    (he : X.get (g, k) = some ⟨pc, .tensorStore a sp⟩)
    (hσ : (code L g).toMachine.after (some (code L g).init) ((X.tr g).take k) =
      some (some d)) :
    ∃ (c : Consumer.D) (s : Fin 8), d = .inr (.cons c) ∧ c.site = .tma s ∧
      TensorStore.Valid (g / L.block) sp ∧
      ∃ b cls origin, sp = ⟨⟨1, Fp16Gemm8192.mapD b cls, origin,
        ⟨.shared, g / L.block, L.sharedBase +
          Consumer.stagingBase (Consumer.tidOf L g) (s.val % 2)⟩,
        none⟩, none⟩ := by
  obtain ⟨t, ins, o, hat, hinv, hc, hfire⟩ := Frame.fired_site (fun _ => sound hpre) hX he hσ
  obtain ⟨c, s, rfl, hs⟩ :=
    store_state (OpPcsFast.mem kernel_store_pcs hc (fires_tensorStore_op hfire rfl))
  obtain ⟨-, htid, -⟩ := hinv
  change kernel.code[c.site.pc]? = some ins at hc
  change Fires c.site.pc (eventTmpl Prod L g t ins.op) ⟨pc, .tensorStore a sp⟩ o at hfire
  obtain ⟨-, h2, h3⟩ := Consumer.tma_event hpre hat htid hc hfire hs a sp rfl
  obtain ⟨hv, hrows, hred⟩ := Consumer.tma_valid hc hfire hs a sp rfl
  refine ⟨c, s, rfl, hs, hv, P.dBase, P.dClass, ?_⟩
  obtain ⟨⟨outer, desc, origin, sb, rows⟩, red⟩ := sp
  simp only [Sigma.mk.injEq] at h2
  obtain ⟨rfl, hdesc⟩ := h2
  cases hdesc
  simp only at hrows hred h3
  subst hrows hred
  exact ⟨origin, by rw [h3]⟩

/-- A consumer's write has as many bytes as its footprint. -/
theorem cons_write_len_fact {X : Execution} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Prod mem0 X) (hg : g < L.threads) {k pc : Nat} {a : Acc}
    {bs : List Byte} {c : Consumer.D} (he : X.get (g, k) = some ⟨pc, .wr a bs⟩)
    (hσ : (code L g).toMachine.after (some (code L g).init) ((X.tr g).take k) =
      some (some (.inr (.cons c)))) : bs.length = a.size := by
  have hk' : k ≤ (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1.le
  have htid := cons_tid_lt hpre hX hg hk' hσ
  obtain ⟨t, ins, o, hat, -, hc, hfire⟩ := Frame.fired_site (fun _ => sound hpre) hX he hσ
  change kernel.code[c.site.pc]? = some ins at hc
  change Fires c.site.pc (eventTmpl Prod L g t ins.op) ⟨pc, .wr a bs⟩ o at hfire
  obtain ⟨wrS, -, -⟩ := Consumer.out_site hc hfire
  obtain ⟨s, i, el, hs⟩ := wrS a bs rfl
  obtain ⟨⟨-, hsize⟩, hlen⟩ := (Consumer.store_event_all hpre hat htid hc hfire hs).2 a bs rfl
  rw [hlen, hsize]

end
end PTX.Kernels.Fp16Gemm8192.Proof
