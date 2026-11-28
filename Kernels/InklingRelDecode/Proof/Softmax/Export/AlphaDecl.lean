-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Iface.LateValues
public import Kernels.InklingRelDecode.Flow.Sites.Part000
import Kernels.InklingRelDecode.Proof.Softmax.Data.ExpFront
import Lemmas.Flow.OutPre
import Kernels.InklingRelDecode.Proof.Softmax.Data.DeclLib
import Kernels.InklingRelDecode.Proof.Softmax.Data.AlphaNum
import Kernels.InklingRelDecode.Proof.Softmax.Data.RoundNum
import Kernels.InklingRelDecode.Proof.Softmax.Data.ExpLib

/-! # The rescale difference and products are not declined

Pcs 1842 (`m - mu`), 1843 (`scale * (m - mu)`) and 1848 (`1525 * -scale`) lie in the run from the
shuffle of pc 1838: the state is the one after a prefix of the run's items (the rescale run and
the first two items of the exponent window), whose registers are typed by the window's inputs. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
open PTX PTX.Proof PTX.Flow PTX.Assumption Data

variable {Q : Params} {L : Launch} {g : Nat}

set_option maxRecDepth 100000

/-- The rescale run and the first two items of the exponent window. -/
noncomputable def adItems : List XItem := Lib.alphaItems ++ Gen.ex1_items0.take 2

/-- The registers of the run's start. -/
noncomputable def adV (L : Launch) (m sent recv : Value) (v : Value) (r : Nat) : Value :=
  if r = 499 then v else alphaV L m sent recv r

private theorem ad_reads : xReadsB [1520, 1521, 1914, 498, 499] adItems = true := by
  decide +kernel
private theorem ad_local : xLocalB adItems = true := by decide +kernel
private theorem ad_req (V : Nat → Value) : xReq V adItems = true := by
  rw [adItems, xReq_append, req_alpha]
  rfl

private theorem ad_at : OAt kernel Assumptions.all L g 1839 adItems :=
  OAt.append Lib.alpha_at ⟨(Gen.ex1_at0 L g).1, (Gen.ex1_at0 L g).2.1, trivial⟩

private theorem ad_take (k : Nat) (hk : k ≤ 8) : adItems.take k = Lib.alphaItems.take k :=
  List.take_append_of_le_length (by simpa [Lib.alphaItems, Lib.alphaRest] using hk)

private theorem ad_full {V : Nat → Value} {k r : Nat} (hk : k ≤ 8)
    (h : r ∉ xWrites (Lib.alphaItems.drop k)) :
    xFinal V (adItems.take k) r = xFinal V Lib.alphaItems r := by
  rw [ad_take k hk]
  conv_rhs => rw [← List.take_append_drop k Lib.alphaItems, xFinal_append]
  exact (Lib.xFinal_other h).symm

private theorem ad_alpha {m sent recv : Value} {v : Value} {r : Nat}
    (hr : r = 168 ∨ r = 507 ∨ r = 1523) :
    xFinal (adV L m sent recv v) Lib.alphaItems r =
      Lib.alphaVal (scaleW L) m (Lib.mxWord m sent recv) r :=
  alpha_fin (by simp [adV, alphaV]) (by simp [adV, alphaV]) (by simp [adV, alphaV])
    (by simp [adV, alphaV]) hr

/-- **The difference and the products of the rescale and the first exponent items are not
declined.** -/
public theorem alpha_decl {m : Mem0} {X : Execution} {t : TState}
    (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (hS : ∀ k a vals sh, X.get (g, k) = some ⟨Flow.tmemLoad_0, .tc (.ld a vals sh)⟩ →
      ∀ x ∈ vals, SK.fl.Has x)
    (h5 : g % L.block < 128 → ∀ k mode sent b c recv ok,
      X.get (g, k) = some ⟨1838, .shfl mode sent b c recv ok⟩ → SK.ni.Has sent ∧ SK.ni.Has recv)
    (hl : Iface.LaneState L X g t) (h1 : 1839 ≤ t.pc) (h2 : t.pc ≤ 1848)
    (hpc : t.pc = 1842 ∨ t.pc = 1843 ∨ t.pc = 1848) {i : Instr}
    (hc : kernel.code[t.pc]? = some i) : execIdealFloat L g t i.op ≠ none := by
  obtain ⟨m, sent, recv, vH, V, t0, hm, -, -, hE, hV, hAt, ht⟩ :=
    exp_front hp hX hf hS h5 hl h1 (by omega)
  obtain ⟨h0, -, -, hft, hF⟩ := hAt
  have hd : ∀ r ∈ [1520, 1521, 1914, 498, 499],
      t0.regs r = some (adV L m sent recv (vH 499) r) := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · simpa [adV, alphaV] using holds_mem hF (by simp)
    · simpa [adV, alphaV] using holds_mem hF (by simp)
    · simpa [adV, alphaV] using holds_mem hF (by simp)
    · simpa [adV, alphaV] using holds_mem hF (by simp)
    · simpa [adV] using holds_mem hF
        (List.mem_append_right _ (mem_factsFrom (show 499 ∈ kHx by decide +kernel)))
  have hlen : adItems.length = 10 := by decide +kernel
  obtain ⟨j, hj, hjpc, hregs⟩ := xItems_pre (V := adV L m sent recv (vH 499))
    (dom := [1520, 1521, 1914, 498, 499]) (by rw [h0]; exact ad_at) hft hd ad_reads
    (ad_req _) ad_local ht
    (fun t1 t' e1 hr => by
      have := (Lib.rtg_fwd (L := L) (g := g) (lo := 1839) (hi := 2234)
        (Lib.entryOk_fwd exp_entry_ok) hr (by omega) (by omega)).1
      omega) (by omega) (by omega)
  have mk : ∀ r, r ∈ kE0 → r = 168 ∨ r = 498 ∨ r = 1914 ∨ r = 1523 → V r =
      Lib.alphaVal (scaleW L) m (Lib.mxWord m sent recv) r := fun r h1 h2 => by
    rw [hV r h1]; simp [h2]
  have hV1523 : V 1523 = xFinal (adV L m sent recv (vH 499)) Lib.alphaItems 1523 := by
    rw [ad_alpha (Or.inr (Or.inr rfl)), mk 1523 (by decide +kernel) (by simp)]
  have hV168 : V 168 = xFinal (adV L m sent recv (vH 499)) Lib.alphaItems 168 := by
    rw [ad_alpha (Or.inl rfl), mk 168 (by decide +kernel) (by simp)]
  have hV1914 : V 1914 = m := by rw [mk 1914 (by decide +kernel) (by simp), alphaVal_m]
  have hV499 : V 499 = vH 499 := by
    have := hV 499 (by decide +kernel)
    simpa using this
  have x1914 : xFinal (adV L m sent recv (vH 499)) (adItems.take 3) 1914 = m := by
    rw [Lib.xFinal_other (by decide +kernel)]; simp [adV, alphaV]
  have x1523 : xFinal (adV L m sent recv (vH 499)) (adItems.take 3) 1523 = V 1523 := by
    rw [ad_full (by omega) (by decide +kernel), hV1523]
  have x1914' : xFinal (adV L m sent recv (vH 499)) (adItems.take 3) 1914 = V 1914 := by
    rw [x1914, hV1914]
  rcases hpc with e | e | e
  · have hj3 : j = 3 := by omega
    subst hj3
    have a1914 := hregs 1914 (by decide +kernel)
    have a1523 := hregs 1523 (by decide +kernel)
    rw [x1914] at a1914
    rw [x1523] at a1523
    rw [e, Flow.code_1842] at hc
    cases hc
    exact decl_sub a1914 a1523 hm hE.mu
  · have hj4 : j = 4 := by omega
    subst hj4
    have a498 := hregs 498 (by decide +kernel)
    have a1524 := hregs 1524 (by decide +kernel)
    rw [Lib.xFinal_other (by decide +kernel)] at a498
    have e1524 : xFinal (adV L m sent recv (vH 499)) (adItems.take 4) 1524 =
        okVal (.bits 32 0) (subE false (xFinal (adV L m sent recv (vH 499)) (adItems.take 3) 1914)
          (xFinal (adV L m sent recv (vH 499)) (adItems.take 3) 1523)) := rfl
    rw [e1524, x1914, x1523] at a1524
    simp only [adV, alphaV] at a498
    rw [e, Flow.code_1843] at hc
    cases hc
    exact decl_mul_pw a498 a1524 (scaleW_has hp) (sub_has hm hE.mu)
  · have hj9 : j = 9 := by omega
    subst hj9
    have a1525 := hregs 1525 (by decide +kernel)
    have a499 := hregs 499 (by decide +kernel)
    rw [Lib.xFinal_other (by decide +kernel)] at a499
    have e1525 : xFinal (adV L m sent recv (vH 499)) (adItems.take 9) 1525 =
        Gen.ex1_v1847 (xFinal (adV L m sent recv (vH 499)) Lib.alphaItems) := rfl
    have h47 : SK.fl.Has (Gen.ex1_v1847 V) :=
      selp2_has (k := .fl) (by decide) (by decide) (by decide) (by decide) hE.pm hE.mu
    have ec : Gen.ex1_v1847 (xFinal (adV L m sent recv (vH 499)) Lib.alphaItems) =
        Gen.ex1_v1847 V := by
      simp only [Gen.ex1_v1847, ← hV1523, ← hV168]
      rw [hV1914, Lib.xFinal_other (by decide +kernel)]
      simp [adV, alphaV]
    rw [e1525, ec] at a1525
    simp only [adV] at a499
    rw [e, Flow.code_1848] at hc
    cases hc
    exact decl_mul_fl a1525 (by simpa [hV499] using a499) h47 hE.ng

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
