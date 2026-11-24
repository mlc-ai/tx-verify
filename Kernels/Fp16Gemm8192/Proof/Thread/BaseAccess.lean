-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.AccessAddr
public import Kernels.Fp16Gemm8192.Proof.Thread.PrologueCluster

@[expose] public section

/-! # The writer and the readers of the Tensor Memory base word

A write other than a consumer's is the allocation's write of its column (`write_site`,
`alloc_site`): not at the allocation's first sub-step, which fires the allocation, but at its
second, the prologue's write site. Only lane 0 of warp 0, CTA thread 0, reaches it, as event 21
(`OnPath`). It comes before the thread's first cluster arrival, so it happens before every role
event of its cluster, which follows the first cluster wait (`clusterSync_of_post_event`)
(`base_write_fact`). A read is fired at a site of the read kind, which no prologue site is
(`read_role_fact`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

/-- The allocation's first sub-step fires no write. -/
theorem alloc_zero_notWrite {A : List Assumption} {t : TState} {grp : CtaGroup} {base : Nat}
    {off : Int} {nc : Opnd} (hs : t.sub = 0) :
    NotWrite (eventTmpl A L g t (.tcAlloc grp base off nc)) := by
  simp only [eventTmpl, tcTmpl, hs, ite_true]
  apply ofExec_notWrite
  repeat' first
    | exact trivial
    | (apply PTX.EventFrame.allOk_bind; intro _)
    | split

/-- **The base word's write.** A write other than a consumer's is CTA thread 0's event 21, and it
happens before every role event of its cluster. -/
theorem base_write_fact {X : Execution} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Prod mem0 X) {k : Nat} {e : Event} {d : ThreadD} {a : Acc}
    {bs : List Byte} (hg : g < L.threads) (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (code L) X g k = some (some d)) (hk : e.kind = .wr a bs)
    (hnc : ∀ c, d ≠ .inr (.cons c)) :
    g % L.block = 0 ∧ k = 21 ∧ ∀ h j ev r, X.get (h, j) = some ev →
      Frame.stateAt (code L) X h j = some (some (.inr r)) → SameCluster L g h →
        baseCausality L X (g, k) (h, j) := by
  obtain ⟨t, ins, o, hat, -, hc, hf⟩ := Frame.fired_site (fun _ => sound hpre) hX he hσ
  rcases write_site hc (fires_write_op hf hk) with ⟨c, rfl⟩ | halloc
  · exact absurd rfl (hnc c)
  obtain ⟨p, rfl, hs⟩ := alloc_site hc halloc
  have hs' : p.site = .allocWrite := by
    rcases hs with hs | hs
    · exfalso
      obtain ⟨grp, base, off, nc, hop⟩ : ∃ grp base off nc, ins.op = .tcAlloc grp base off nc := by
        revert halloc
        cases ins.op <;> simp [allocOp]
      have hsub : t.sub = 0 := by
        have := hat.2.1
        simpa [code, Prologue.sub, hs] using this
      have hm := alloc_zero_notWrite (A := Prod) (L := L) (g := g) (grp := grp) (base := base)
        (off := off) (nc := nc) hsub
      rw [hop] at hf
      obtain ⟨epc, ek⟩ := e
      simp only at hk
      subst hk
      cases h : eventTmpl Prod L g t (.tcAlloc grp base off nc) <;> rw [h] at hm hf <;>
        simp only [NotWrite] at hm <;> simp only [Fires] at hf <;> aesop
    · exact hs
  have hk' : k ≤ (X.tr g).length := (len_of_get he).le
  obtain ⟨hidx, -, hcan⟩ := (onPath_all hpre hX hg k hk').1 p hσ
  have hfirst : Prologue.first L g = true := hcan.2.2.1 hs'
  have h21 : k = 21 := by simp [hidx, Prologue.index, hs', hfirst]
  refine ⟨(Prologue.first_iff L g).1 hfirst, h21, fun h j ev r hev hr hcl => ?_⟩
  have hblock : 0 < L.block := by rw [hpre.block]; norm_num
  have hj := Prologue.post_cluster hpre hX (len_of_get hev).le hr
  have hsync := clusterSync_of_post_event hX hblock hpre.oneDimLaunch.1
    (Prologue.cluster_before hpre hX)
    (Prologue.cluster_arrive hpre hX) (Prologue.cluster_wait hpre hX) hcl hev hj
    (i := k) (by rw [Prologue.clusterIndex_first hfirst]; omega)
  exact .single (.inr (.inr (.inr (.inl hsync))))

/-- **Reads are role events.** No prologue site reads. -/
theorem read_role_fact {X : Execution} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Prod mem0 X) {k : Nat} {e : Event} {d : ThreadD} {a : Acc}
    {bs : List (Option Byte)} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (code L) X g k = some (some d)) (hk : e.kind = .rd a bs) : ∃ r, d =
    .inr r := by
  obtain ⟨t, ins, o, -, -, hc, hf⟩ := Frame.fired_site (fun _ => sound hpre) hX he hσ
  have hn := read_kind hc hf hk
  rcases d with p | r
  · cases hs : p.site <;> simp [nextKind, prologueKind, hs] at hn
  · exact ⟨r, rfl⟩

end

end PTX.Kernels.Fp16Gemm8192.Proof
