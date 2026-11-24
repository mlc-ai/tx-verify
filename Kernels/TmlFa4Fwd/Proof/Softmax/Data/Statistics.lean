-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Data.StatScalar
public import Kernels.TmlFa4Fwd.Proof.Softmax.Data.Rescale
import Kernels.TmlFa4Fwd.Flow.Code.Part088
import Kernels.TmlFa4Fwd.Flow.Code.Part107
import Kernels.TmlFa4Fwd.Flow.Code.Part118
import Kernels.TmlFa4Fwd.Proof.Softmax.DataStoreBytes
import Tactics.KernelRfl

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Data
open PTX.Flow PTX.Proof
noncomputable section
set_option maxRecDepth 100000

private def op (base src : Nat) (off : Int) : Op := .mem
  { kind := .store, space := some (.shared .cta), sem := .weak, elem := .int .b 32,
    addr := ⟨.reg base 32, off⟩, srcs := [.reg src] }

private theorem bytes {p L g} (d : D) {t e o a bs base src off}
    (hc : kernel.code[d.site.pc]? = some { guard := none, op := op base src off })
    (live : src ∈ liveD (livePc d)) (hat : (codeD p L g).AtD d t)
    (hf : Fires d.site.pc ((codeD p L g).tmpl (some d) t) e o) (hk : e.kind = .wr a bs)
    (hb : (valueOfD p L g d src).bytes = 4) : bs = (valueOfD p L g d src).toBytes := by
  change Fires _ (match kernel.code[d.site.pc]? with
    | some ins => eventTmpl Assumptions.all L g t ins.op | none => .ub .pcOutOfRange) e o at hf
  rw [hc] at hf
  change Fires _ (eventTmpl _ _ _ _ (.mem
    { kind := .store, space := some (.shared .cta), sem := .weak, elem := .int .b 32,
      addr := ⟨.reg base 32, off⟩, srcs := [.reg src] })) e o at hf
  rw [eventTmpl, memTmpl_store (sp := .shared) (base := base) (w := 32)
    (by rfl) rfl rfl rfl (by simp)] at hf
  change Fires _ (storeTmpl L g t .shared 32 base off [.reg src]) e o at hf
  obtain ⟨_, _, _, _, hregs⟩ := hat
  have hv := regs_of_factsFrom hregs live
  unfold storeTmpl at hf
  split at hf
  · rw [hf.1] at hk; cases hk
  · cases hs : t.sub with
    | zero =>
      simp only [hs, List.getElem?_cons_zero, readValue, readReg, hv,
        storeValue_of_bytes (w := 32) (by simpa using hb), bind, Except.bind, pure,
        Except.pure] at hf
      rw [hf.1] at hk
      exact (Kind.wr.inj hk).2.symm
    | succ n =>
      simp only [hs, List.getElem?_cons_succ, List.getElem?_nil] at hf
      rw [hf.1] at hk; cases hk

theorem final_bytes (p L g v k acc) (j : Fin 2) {t e o a bs}
    (hat : (codeD p L g).AtD ⟨.fin j,v,k,acc⟩ t)
    (hf : Fires (Site.fin j).pc ((codeD p L g).tmpl (some ⟨.fin j,v,k,acc⟩) t) e o)
    (hk : e.kind = .wr a bs) :
    bs = (if j = 0 then Value.float .f32 v.rs else mxVal v).toBytes := by
  match j with
  | 0 =>
    exact bytes (p := p) (L := L) (g := g) ⟨.fin 0,v,k,acc⟩
      (base := 5814) (src := 7257) (off := 368)
      Flow.code_7614 (by change 7257 ∈ liveD 7614; decide +kernel) hat hf hk
      (bytes_fin (p := p) (L := L) (g := g) v k acc 0).1
  | 1 =>
    exact bytes (p := p) (L := L) (g := g) ⟨.fin 1,v,k,acc⟩
      (base := 5814) (src := 7256) (off := 1392)
      Flow.code_7615 (by change 7256 ∈ liveD 7615; decide +kernel) hat hf hk
      (bytes_fin (p := p) (L := L) (g := g) v k acc 1).2

/-- The factor store writes the actual operand bytes, including the literal encoding of one. -/
theorem factor_word (p L g v k acc) (plain : Bool) {t e o a bs}
    (hat : (codeD p L g).AtD ⟨.stat plain,v,k,acc⟩ t)
    (hf : Fires (Site.stat plain).pc ((codeD p L g).tmpl (some ⟨.stat plain,v,k,acc⟩) t) e o)
    (hk : e.kind = .wr a bs) :
    ∃ w, bs = w.toBytes ∧ Reads w (factor p v (bif plain then .plain else .bias)) ∧
      FactorWord w (factor p v (bif plain then .plain else .bias)) := by
  cases plain
  · exact ⟨_, bytes (p := p) (L := L) (g := g) ⟨.stat false,v,k,acc⟩
      (base := 4571) (src := 1362) (off := 368)
      Flow.code_5682 (by change 1362 ∈ liveD 5682; decide +kernel) hat hf hk
      (bytes_statB (p := p) (L := L) (g := g) v k acc),
      stat_bias p L g v k acc, word_bias p L g v k acc⟩
  · exact ⟨_, bytes (p := p) (L := L) (g := g) ⟨.stat true,v,k,acc⟩
      (base := 5518) (src := 1492) (off := 368)
      Flow.code_6890 (by change 1492 ∈ liveD 6890; decide +kernel) hat hf hk
      (bytes_statP (p := p) (L := L) (g := g) v k acc),
      stat_plain p L g v k acc, word_plain p L g v k acc⟩

/-- The factor store's word reads as the factor. -/
theorem factor_bytes (p L g v k acc) (plain : Bool) {t e o a bs}
    (hat : (codeD p L g).AtD ⟨.stat plain,v,k,acc⟩ t)
    (hf : Fires (Site.stat plain).pc ((codeD p L g).tmpl (some ⟨.stat plain,v,k,acc⟩) t) e o)
    (hk : e.kind = .wr a bs) :
    ∃ w, bs = w.toBytes ∧ Reads w (factor p v (bif plain then .plain else .bias)) :=
  let ⟨w, h1, h2, _⟩ := factor_word p L g v k acc plain hat hf hk
  ⟨w, h1, h2⟩

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Data
