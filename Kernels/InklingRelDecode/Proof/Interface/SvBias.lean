-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.SvExit
public import Kernels.InklingRelDecode.Proof.Interface.ClassQLoad

@[expose] public section

/-!
# The softmax region's bias loads return the key's bias

A softmax thread's bias load (`Sm.Site.pre j`, `Sm.Site.nxt j`) reads two bytes of `Rel`
(`Sm.shape_pre_spec`, `Sm.shape_nxt_spec`), which are launch bytes (`read_launch_byte`) of the
`bf16` number `Pre.relInput` gives, so the bytes rebuild into that number (`rel_read_value`), and
the number is `Spec.bias` of the key because the load's block is at or after `n_bias`
(`Sm.bias_eq_rel`). `evOk_of`: the premise `Sv.EvOk` of the invariant's steps holds at every
event of a followed thread, given the premise on the S tile's load.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Sv
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Sm
open PTX.Kernels.InklingRelDecode.Proof.Interface

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **A read of two bytes of `Rel` returns the `bf16` number there.** -/
theorem rel_read_value (hpre : Pre Q L mem0) (hX : Consistent L kernel Interface.asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) {g k pc : Nat} {r tok head c : Nat} {bs : List (Option Byte)}
    (hr : r < Q.b) (htok : tok < Q.qLen r) (hh : head < heads) (hc : c < relPad)
    (hlen : bs.length = 2)
    (he : X.get (g, k) = some ⟨pc, .rd (globalAcc (relAddr Q r tok head c) 2) bs⟩) :
    rebuild 3 bs = .ok (Value.float .bf16 (Q.rel (Q.qStart r + tok) head c)) := by
  set x := Q.rel (Q.qStart r + tok) head c with hx
  obtain ⟨acc, hacc⟩ : ∃ acc : Acc, acc = globalAcc (relAddr Q r tok head c) 2 := ⟨_, rfl⟩
  have hrd : X.MemReads (.thread (g, k)) acc bs := by
    rw [hacc]
    exact Or.inl ⟨_, he⟩
  have hbyte : ∀ j < 2, bs[j]? = some (some ((Value.float .bf16 x).byteAt j)) := by
    intro j hj
    have hq : Q.reads (acc.loc.at j).addr := by
      rw [hacc]
      exact Or.inr (Or.inl ⟨r, hr, tok, htok, head, hh, c, hc, j, hj, by
        simp [Loc.at, relAddr]⟩)
    obtain ⟨c0, hc1, hc2⟩ := read_launch_byte hpre hX hf hrd (by simp [hacc, globalAcc])
      (by simp [hacc, globalAcc]) (k := j) (by simpa [hacc, globalAcc] using hj) hq
    have hq' := hpre.relInput r hr tok htok head hh c hc j hj
    have hloc : (acc.loc.at j) = ⟨.global, 0, Q.relBase + 2 * ((Q.qStart r + tok) *
        Q.strideRel + head * relPad + c) + j⟩ := by
      rw [hacc]
      simp [Loc.at, relAddr]
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

/-- The thread layer's invariant of the state before a bias load and the entry numbers' meaning:
the facts every bias load's proof needs. -/
theorem key_eq_pre {Q : Params} {s j h : Nat} :
    keyB Q s 0 h j = s * 128 + h * 64 + j := by
  unfold keyB
  omega

/-- **A preload returns the bias of the key.** -/
theorem biasEv_pre (hpre : Pre Q L mem0) (hX : Consistent L kernel Interface.asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) {g k : Nat} {d : D} {e : Event} {j : Fin 64}
    (hg : g < L.threads) (he : X.get (g, k) = some e)
    (hσ : St Q L X g k = some (some (.d (.sm d)))) (hI : Sm.Inv L g d) (hs : d.site = .pre j) :
    BiasEv Q (ProA.cta L g .z) (ProA.cta L g .x) (ProA.cta L g .y) (g % L.block) d.i j.val e := by
  obtain ⟨-, hm⟩ := hf.reach hg hσ
  obtain ⟨hx, hy, hz⟩ := ProA.cta_lt hpre hg
  obtain ⟨u, hF⟩ := fired_cont hX hf hg he hσ (by simp [ExitState])
  obtain ⟨bs, hl, hev⟩ := Sm.shape_pre_spec hpre hm.ent hz hy (fired_sm hF) hs
  obtain ⟨hn, hrv, hit, hnb⟩ := Sm.pre_block hm.ent hI hs
  obtain ⟨hi0, -⟩ := hI.loop.1 j hs
  have hbl : ProA.cta L g .x < Q.blocks (ProA.cta L g .z) := by
    have := Sm.lt_blocks_of_iters (r := ProA.cta L g .z) (s := ProA.cta L g .x) (i := 0)
      hpre.splitsPos hit
    simpa using this
  obtain ⟨htok, hh, hc, hadr⟩ := Sm.biasAddr_spec hpre hm.ent hz hy hI.tid hrv j.isLt hbl hnb
  intro acc bs' x hk hrb
  rw [hev] at hk
  simp only [Kind.rd.injEq] at hk
  obtain ⟨rfl, rfl⟩ := hk
  have hx' := rel_read_value hpre hX hf hz htok hh hc
    hl (by rw [hev] at he; exact he)
  rw [hrb] at hx'
  have := Except.ok.inj hx'
  rw [this]
  unfold biasB
  rw [hi0, key_eq_pre, bias_eq_rel]
  omega

theorem key_eq_nxt {Q : Params} {s b j h : Nat} :
    keyB Q s b h j = (s + b * Q.splits) * 128 + h * 64 + j := by
  unfold keyB
  ring

/-- **A loop load returns the bias of the key of the next block.** -/
theorem biasEv_nxt (hpre : Pre Q L mem0) (hX : Consistent L kernel Interface.asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) {g k : Nat} {d : D} {e : Event} {j : Fin 64}
    (hg : g < L.threads) (he : X.get (g, k) = some e)
    (hσ : St Q L X g k = some (some (.d (.sm d)))) (hI : Sm.Inv L g d) (hs : d.site = .nxt j) :
    BiasEv Q (ProA.cta L g .z) (ProA.cta L g .x) (ProA.cta L g .y) (g % L.block) (d.i + 1)
      j.val e := by
  obtain ⟨-, hm⟩ := hf.reach hg hσ
  obtain ⟨hx, hy, hz⟩ := ProA.cta_lt hpre hg
  obtain ⟨u, hF⟩ := fired_cont hX hf hg he hσ (by simp [ExitState])
  obtain ⟨bs, hl, hev⟩ := Sm.shape_nxt_spec hpre hm.ent hz hy (fired_sm hF) hs
  obtain ⟨hn, hrv, hit, hnb⟩ := Sm.nxt_block hm.ent hI hs
  have hbl := Sm.lt_blocks_of_iters hpre.splitsPos hit
  obtain ⟨htok, hh, hc, hadr⟩ := Sm.biasAddr_spec hpre hm.ent hz hy hI.tid hrv j.isLt hbl hnb
  intro acc bs' x hk hrb
  rw [hev] at hk
  simp only [Kind.rd.injEq] at hk
  obtain ⟨rfl, rfl⟩ := hk
  have hx' := rel_read_value hpre hX hf hz htok hh hc
    hl (by rw [hev] at he; exact he)
  rw [hrb] at hx'
  have := Except.ok.inj hx'
  rw [this]
  unfold biasB
  rw [key_eq_nxt, bias_eq_rel]
  have := Nat.mul_le_mul_right 128 hnb
  omega

/-- **The premise `EvOk` of the invariant's steps** at an event of a followed softmax thread, given
the premise on the S tile's load. -/
theorem evOk_of (hpre : Pre Q L mem0) (hX : Consistent L kernel Interface.asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) {g k : Nat} {d : D} {e : Event}
    (hg : g < L.threads) (he : X.get (g, k) = some e)
    (hσ : St Q L X g k = some (some (.d (.sm d)))) (hI : Sm.Inv L g d)
    (hscore : d.site = .ldS →
      ScoreEv Q (ProA.cta L g .z) (ProA.cta L g .x) (ProA.cta L g .y) (g % L.block) d.i e) :
    EvOk Q (ProA.cta L g .z) (ProA.cta L g .x) (ProA.cta L g .y) (g % L.block) d e := by
  unfold EvOk
  cases hs : d.site with
  | pre j => exact biasEv_pre hpre hX hf hg he hσ hI hs
  | nxt j => exact biasEv_nxt hpre hX hf hg he hσ hI hs
  | ldS => exact hscore hs
  | _ => trivial

end
end PTX.Kernels.InklingRelDecode.Proof.Sv
