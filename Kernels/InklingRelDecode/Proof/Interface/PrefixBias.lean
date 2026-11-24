-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.PrefixPro
public import Kernels.InklingRelDecode.Proof.Thread.EvSBiasSpec

@[expose] public section

/-!
# The softmax region's bias loads, in prefix form

A softmax thread's bias load (`Sm.Site.pre j`, `Sm.Site.nxt j`) reads the two bytes of a `Rel`
element (`Sm.shape_pre_spec`, `Sm.shape_nxt_spec`; the entry numbers' meaning is the reach
invariant `treach_stateAt`, which needs no tracking). Those bytes are input bytes, so the event's
own `LaunchRead` gives the launch's bytes, and `Pre.relInput` says they are a `bf16` number. So
the machine does not leave its run at the 128 bias loads: `Sm.next` follows a `bf16` word, and
where the last preload ends the loop (`Sm.afterSetup` with `num_iters = i`) the composed machine
hands over to the epilogue instead (`DComp.leaves`, `DComp.exitNext`). `sm_bias_next_ne` is the
`hnext` of `weakTracked_of` at these states; it uses the thread's own event only.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **A read of two bytes of `Rel` whose launch bytes the event returns is the `bf16` number
there.** -/
theorem rel_read_launch (hpre : Pre Q L mem0) {g k pc : Nat} {r tok head c : Nat}
    {bs : List (Option Byte)} (hr : r < Q.b) (htok : tok < Q.qLen r) (hh : head < heads)
    (hc : c < relPad) (hlen : bs.length = 2)
    (he : X.get (g, k) = some ⟨pc, .rd (Sm.globalAcc (Sm.relAddr Q r tok head c) 2) bs⟩)
    (hL : LaunchRead Q mem0 X (g, k)) :
    rebuild 3 bs = .ok (Value.float .bf16 (Q.rel (Q.qStart r + tok) head c)) := by
  set x := Q.rel (Q.qStart r + tok) head c with hx
  obtain ⟨acc, hacc⟩ : ∃ acc : Acc, acc = Sm.globalAcc (Sm.relAddr Q r tok head c) 2 := ⟨_, rfl⟩
  have hbyte : ∀ j < 2, bs[j]? = some (some ((Value.float .bf16 x).byteAt j)) := by
    intro j hj
    have hq : Q.reads (acc.loc.at j).addr := by
      rw [hacc]
      exact Or.inr (Or.inl ⟨r, hr, tok, htok, head, hh, c, hc, j, hj, by
        simp [Loc.at, Sm.relAddr]⟩)
    rw [← hacc] at he
    obtain ⟨c0, hc1, hc2⟩ := hL pc acc bs he (by simp [hacc, Sm.globalAcc])
      (by simp [hacc, Sm.globalAcc]) j (by simpa [hacc, Sm.globalAcc] using hj) hq
    have hq' := hpre.relInput r hr tok htok head hh c hc j hj
    have hloc : (acc.loc.at j) = ⟨.global, 0, Q.relBase + 2 * ((Q.qStart r + tok) *
        Q.strideRel + head * relPad + c) + j⟩ := by
      rw [hacc]
      simp [Loc.at, Sm.relAddr]
    rw [hloc, hq'] at hc1
    have := Option.some.inj (Option.some.inj hc1)
    rw [this]
    exact hc2
  have hbs : bs = (Value.float .bf16 x).toBytes.map some := by
    apply List.ext_getElem?
    intro j
    by_cases hj : j < 2
    · rw [hbyte j hj, bf16_toBytes]
      interval_cases j <;> simp
    · have h1 : bs[j]? = none := List.getElem?_eq_none (by omega)
      rw [h1, bf16_toBytes]
      simp
      omega
  rw [hbs]
  exact rebuild_scalar (by rw [bf16_bytes]; norm_num) rfl

variable (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound)
    (hT : ∀ g < L.threads, (threadCode L g Q).TmplOk) {g k : Nat} {d : Sm.D} {e : Event}
    (hg : g < L.threads) (he : X.get (g, k) = some e) (hσ : St Q L X g k = some (some (.d (.sm d))))
    (hs : (∃ j, d.site = .pre j) ∨ ∃ j, d.site = .nxt j)
include hpre hX hS hT hg he hσ hs

/-- **A bias load returns a `bf16` number**, at a followed softmax state whose event's own input
bytes are the launch's. -/
theorem sm_bias_read (hL : LaunchRead Q mem0 X (g, k)) :
    ∃ acc bs x, e.kind = .rd acc bs ∧ rebuild 3 bs = .ok (Value.float .bf16 x) := by
  obtain ⟨u, hF⟩ := fired_cont_at hX hS hT hg he hσ (by simp [ExitState])
  have hF' := fired_sm hF
  obtain ⟨-, hm⟩ := treach_stateAt hpre hg hσ
  have hm : SmMeans Q L g d.e := hm
  obtain ⟨-, hy, hz⟩ := ProA.cta_lt hpre hg
  obtain ⟨t, -, hI, -⟩ := id hF'
  rcases hs with ⟨j, hj⟩ | ⟨j, hj⟩
  · obtain ⟨bs, hl, hev⟩ := Sm.shape_pre_spec hpre hm.ent hz hy hF' hj
    obtain ⟨-, hrv, hit, hnb⟩ := Sm.pre_block hm.ent hI hj
    have hbl : ProA.cta L g .x < Q.blocks (ProA.cta L g .z) := by
      have := Sm.lt_blocks_of_iters (r := ProA.cta L g .z) (s := ProA.cta L g .x) (i := 0)
        hpre.splitsPos hit
      simpa using this
    obtain ⟨htok, hh, hc, -⟩ := Sm.biasAddr_spec hpre hm.ent hz hy hI.tid hrv j.isLt hbl hnb
    have he2 := he
    rw [hev] at he2
    exact ⟨_, bs, _, by rw [hev], rel_read_launch hpre hz htok hh hc hl he2 hL⟩
  · obtain ⟨bs, hl, hev⟩ := Sm.shape_nxt_spec hpre hm.ent hz hy hF' hj
    obtain ⟨-, hrv, hit, hnb⟩ := Sm.nxt_block hm.ent hI hj
    have hbl := Sm.lt_blocks_of_iters hpre.splitsPos hit
    obtain ⟨htok, hh, hc, -⟩ := Sm.biasAddr_spec hpre hm.ent hz hy hI.tid hrv j.isLt hbl hnb
    have he2 := he
    rw [hev] at he2
    exact ⟨_, bs, _, by rw [hev], rel_read_launch hpre hz htok hh hc hl he2 hL⟩

/-- **A bias load does not leave the run.** -/
theorem sm_bias_next_ne (hL : LaunchRead Q mem0 X (g, k)) :
    (threadCode L g Q).next (.d (.sm d)) e ≠ some none := by
  obtain ⟨acc, bs, x, hk, hrb⟩ := sm_bias_read hpre hX hS hT hg he hσ hs hL
  rw [next_d]
  change (DComp.smNext L g d e).map (Option.map TSt.d) ≠ some none
  unfold DComp.smNext
  by_cases hlv : DComp.leaves L g d e
  · simp only [hlv, ↓reduceIte]
    unfold DComp.exitNext
    split <;> simp
  · simp only [hlv, ↓reduceIte]
    unfold Sm.next
    rcases hs with ⟨j, hj⟩ | ⟨j, hj⟩
    · simp only [hj, hk, hrb, Sm.isBf16, ↓reduceIte]
      split
      · simp
      · unfold Sm.afterSetup
        split
        · exfalso
          apply hlv
          simp only [DComp.leaves, hj, DComp.bf16Read, hk, hrb, Sm.isBf16]
          exact ⟨by omega, trivial, by assumption⟩
        · split <;> simp
    · simp only [hj, hk, hrb, Sm.isBf16, ↓reduceIte]
      split <;> simp

end
end PTX.Kernels.InklingRelDecode.Proof.Interface
