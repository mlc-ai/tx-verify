-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.BaseAccess
public import Kernels.Fp16Gemm8192.Proof.Thread.TmemFacts
public import Lemmas.Flow.AllocTmpl
public import Kernels.Fp16Gemm8192.Proof.Thread.UbSite

@[expose] public section

/-! # The Tensor Memory base word's write

CTA thread 0 allocates the Tensor Memory at its event 20 (512 columns, its column into the base
word at the start of its CTA's shared window) and writes the column it got there at event 21. A
role event of any thread of the CTA's cluster comes after that write (`base_written_fact`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow

noncomputable section

set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- A prologue state of CTA thread 0 at its event 20 is its allocation, at event 21 its write. -/
theorem first_site {g k : Nat} {p : Prologue.D} (hf : Prologue.first L g = true)
    (hidx : k = Prologue.index L g p) (hw : p.w = Prologue.warpOf L g) :
    (k = 20 → p.site = .alloc) ∧ (k = 21 → p.site = .allocWrite) := by
  have hw0 := Prologue.warpOf_of_first hf
  obtain ⟨site, w⟩ := p
  simp only at hw ⊢
  cases site <;> simp only [Prologue.index, Prologue.fenceIdx, hf, hw, hw0, ↓reduceIte] at hidx <;>
    constructor <;> intro h <;> first | rfl | omega

set_option maxHeartbeats 8000000 in
/-- **CTA thread 0's allocation request and address store.** -/
theorem first_alloc (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) {g : Nat}
    (hg : g < L.threads) (hf0 : g % L.block = 0) (hlen : 21 < (X.tr g).length) :
    ∃ col, X.get (g, 20) = some ⟨Flow.tmemAlloc_0, .tc (.resource .two
        (some ⟨.shared, g / L.block, L.sharedBase⟩) (.alloc 512))⟩ ∧
      X.get (g, 21) = some ⟨Flow.tmemAlloc_0, .wr
        ⟨⟨.shared, g / L.block, L.sharedBase⟩, 4, false, false, .cta, 0, false⟩
        (b32 col).toBytes⟩ ∧ col < 2 ^ 16 := by
  have hbase := hpre.sharedRange
  unfold sharedBytes at hbase
  have hal := hpre.sharedAlignment
  have hb : L.block % 32 = 0 := by rw [hpre.block]
  have hf : Prologue.first L g = true := (Prologue.first_iff L g).2 hf0
  have hl0 : laneOf L g = 0 := Prologue.laneOf_of_first hf
  have hci := Prologue.clusterIndex_first hf
  have htr := Frame.trace (fun _ => sound hpre) hX hg
  obtain ⟨p20, h20⟩ := Prologue.prologue_state hpre hX hg 20 (by omega) (by omega) (by omega)
  obtain ⟨hidx, hwp, -⟩ := (onPath_all hpre hX hg 20 (by omega)).1 p20 h20
  have hs20 := (first_site hf hidx (hwp (by omega))).1 rfl
  obtain ⟨e20, he20⟩ : ∃ e, (X.tr g)[20]? = some e := ⟨_, List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨τ, u, ha, hfd⟩ := htr.fired_some he20 (by omega)
  have hτ : τ = some (.inl p20) := Option.some.inj (ha.symm.trans h20)
  subst hτ
  obtain ⟨t, ins, hat, -, hc, hfire⟩ := Code.fired_site (sound hpre hg) hfd
  obtain ⟨s, w⟩ := p20
  simp only at hs20
  subst hs20
  change kernel.code[Flow.tmemAlloc_0]? = some ins at hc
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemAlloc_0)
  have hr44 : t.regs 90 = some (b32 L.sharedBase) :=
    (holds_mem hat.2.2.2.2 (Flow.mem_factsFrom (by lit_mem))).trans (congrArg some (by pro_values))
  have hr45 : t.regs 91 = some (b32 512) :=
    (holds_mem hat.2.2.2.2 (Flow.mem_factsFrom (by lit_mem))).trans (congrArg some (by pro_values))
  have hsub : t.sub = 0 := hat.2.1
  change Fires Flow.tmemAlloc_0 (eventTmpl Prod L g t _) e20 (some u) at hfire
  rw [tcAlloc_tmpl0 hb hr44 (by omega) (by omega) hr45 hsub] at hfire
  obtain ⟨rfl, -⟩ := hfire
  -- the write at 21
  have h21 : Frame.stateAt (code L) X g 21 = some (some (.inl ⟨.allocWrite, w⟩)) := by
    rw [stateAt_succ_inl he20 h20]
    simp [Prologue.next, hl0]
  obtain ⟨e21, he21⟩ : ∃ e, (X.tr g)[21]? = some e := ⟨_, List.getElem?_eq_getElem hlen⟩
  obtain ⟨t', ins', o', hat', -, hc', hfire'⟩ := Frame.fired_site (fun _ => sound hpre) hX he21 h21
  change kernel.code[Flow.tmemAlloc_0]? = some ins' at hc'
  obtain rfl := Option.some.inj (hc'.symm.trans Flow.code_tmemAlloc_0)
  have hr44' : t'.regs 90 = some (b32 L.sharedBase) :=
    (holds_mem hat'.2.2.2.2 (Flow.mem_factsFrom (by lit_mem))).trans (congrArg some (by pro_values))
  have hr45' : t'.regs 91 = some (b32 512) :=
    (holds_mem hat'.2.2.2.2 (Flow.mem_factsFrom (by lit_mem))).trans (congrArg some (by pro_values))
  change Fires Flow.tmemAlloc_0 (eventTmpl Prod L g t' _) e21 o' at hfire'
  rw [tcAlloc_tmpl1 hb hr44' (by omega) (by omega) hr45' hat'.2.1] at hfire'
  obtain ⟨col, hcol, rfl, -⟩ := hfire'
  exact ⟨col, he20, he21, hcol⟩

/-- **The base word is written before every role event.** A role event of a thread follows its
CTA thread 0's allocation request (event 20) and its store of the address (event 21). -/
theorem base_written_fact (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) {g k : Nat}
    {ev : Event} {r : Prologue.Role} (hg : g < L.threads) (he : X.get (g, k) = some ev)
    (hσ : Frame.stateAt (code L) X g k = some (some (.inr r))) :
    ∃ pca pcw col, X.get (g / L.block * L.block, 20) = some ⟨pca, .tc (.resource .two
        (some ⟨.shared, g / L.block, L.sharedBase⟩) (.alloc 512))⟩ ∧
      X.get (g / L.block * L.block, 21) = some ⟨pcw, .wr
        ⟨⟨.shared, g / L.block, L.sharedBase⟩, 4, false, false, .cta, 0, false⟩ (b32 col).toBytes⟩ ∧
      col < 2 ^ 16 ∧ baseCausality L X (g / L.block * L.block, 21) (g, k) := by
  have hblock : 0 < L.block := by rw [hpre.block]; norm_num
  have hg0 : g / L.block * L.block < L.threads := lt_of_le_of_lt (Nat.div_mul_le_self g L.block) hg
  have hf0 : g / L.block * L.block % L.block = 0 := Nat.mul_mod_left _ _
  have hc0 : g / L.block * L.block / L.block = g / L.block := Nat.mul_div_cancel _ hblock
  have hfirst : Prologue.first L (g / L.block * L.block) = true := (Prologue.first_iff L _).2 hf0
  have hcl : SameCluster L (g / L.block * L.block) g := ⟨hg0, hg, by rw [hc0]⟩
  have hj := Prologue.post_cluster hpre hX (len_of_get he).le hσ
  have hsync := clusterSync_of_post_event hX hblock hpre.oneDimLaunch.1
    (Prologue.cluster_before hpre hX)
    (Prologue.cluster_arrive hpre hX) (Prologue.cluster_wait hpre hX) hcl he hj (i := 21)
    (by rw [Prologue.clusterIndex_first hfirst]; omega)
  obtain ⟨-, i, j, -, hi, h21, -, -⟩ := id hsync
  obtain ⟨col, h20, h21', hcol⟩ :=
    first_alloc hpre hX hg0 hf0 (by simp only at hi h21; omega)
  rw [hc0] at h20 h21'
  exact ⟨_, _, col, h20, h21', hcol, .single (.inr (.inr (.inr (.inl hsync))))⟩

end

end PTX.Kernels.Fp16Gemm8192.Proof
