-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.ClcQuery

@[expose] public section

/-! # A consumer exits after reading a response that claims no CTA

From the query that finds no CTA to the exit (`Consumer.D.doomed`), a consumer's trace holds a
successful poll of its CTA's response barrier and the read of such a response (`FailRead`); the
query relation (`QueryRel`) gives that read at the query. So its exit follows it
(`consumer_exit`, in `ConsumerOutFacts`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxHeartbeats 8000000

/-- Whether an instruction returns or exits. -/
def retOp : Op → Bool
  | .ret | .exit => true
  | _ => false

/-- The kernel returns or exits only at its exit site (decided on the code). -/
theorem kernel_ret_pcs : OpPcs kernel.code retOp Flow.exit.toList = true :=
  OpPcsFast.opPcs (by decide +kernel)

theorem ret_pc {pc : Nat} {ins : Instr} (hc : kernel.code[pc]? = some ins)
    (hq : ins.op = .ret ∨ ins.op = .exit) : pc ∈ Flow.exit.toList :=
  OpPcs.mem kernel_ret_pcs hc (by rcases hq with hq | hq <;> rw [hq] <;> rfl)

/-- A successful poll of the CTA's response barrier followed by the read of a response that
claims no CTA. -/
def FailRead (L : Launch) (g : Nat) (es : List Event) : Prop :=
  ∃ j pc p acq sc pcr, ∃ src : Acc, ∃ bs rr,
    es[j]? = some ⟨pc, .wait (clcResp L g) p true acq sc⟩ ∧ es[j + 1]? = some ⟨pcr, .rd src bs⟩ ∧
    src.loc = respLoc L g ∧ src.size = 16 ∧ Flow.responseOf bs = some rr ∧ ¬ Loader.claims rr

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

theorem FailRead.snoc {es : List Event} (h : FailRead L g es) (e : Event) :
    FailRead L g (es ++ [e]) := by
  obtain ⟨j, pc, p, acq, sc, pcr, src, bs, rr, hw, hr, h1, h2, h3, h4⟩ := h
  have hl : j + 1 < es.length := (List.getElem?_eq_some_iff.mp hr).1
  refine ⟨j, pc, p, acq, sc, pcr, src, bs, rr, ?_, ?_, h1, h2, h3, h4⟩
  · rw [List.getElem?_append_left (by omega)]; exact hw
  · rw [List.getElem?_append_left hl]; exact hr

/-- The read the query relation holds at stage 2 or 3, of a response that claims no CTA. -/
theorem QueryRel.failRead {n : Nat} {v : Value} {es : List Event} (h : QueryRel L g n v es)
    (hn : 2 ≤ n) {r : ClcResponse} (hv : ∀ r0, v = .clc r0 → r = r0) (hr : ¬ Loader.claims r)
    (e : Event) : FailRead L g (es ++ [e]) := by
  obtain ⟨j, pc, p, acq, sc, pcr, a, bs, rr, hj, hw, hrd, ha, hs, hres, hvv⟩ := h.2 hn
  obtain rfl := hv rr hvv
  exact FailRead.snoc ⟨j, pc, p, acq, sc, pcr, a, bs, r, hw, hrd, ha, hs, hres, hr⟩ e

namespace Consumer

/-- From the query that finds no CTA to the exit. -/
def D.doomed (d : D) : Prop := match d.site with
  | .setMaxReg | .clcWait | .clcLoad | .clcStatus | .clcFirst => False
  | .finalDrain | .exitArrive | .exitWait | .relinquish | .ldBase | .dealloc | .exit => True
  | _ => d.x = Loader.none32

/-- Find a site from its position being in a list: `simp` names the site at a position of the
list, and `decide` rules out every other site whose position is in it. -/
macro "site_of_pc " d:ident hpc:ident : tactic => `(tactic| (
  obtain ⟨site, mm, n, m', n', cp, ap, resp, x, acc, base⟩ := $d:ident
  simp only at $hpc:ident ⊢
  cases site
  all_goals first
    | (exfalso; revert $hpc:ident; simp only [Site.pc]; decide +revert)
    | (simp; done)))

theorem exit_step {d d' : D} {t : TState} {ins : Instr} {e : Event} {o : Option TState}
    {pre : List Event} (hat : (code L g).AtD (.inr (.cons d)) t)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e o) (hn : next L g d e = some (some d'))
    (hq : QueryRel L g d.clcStage d.resp pre) (hx : d.doomed → FailRead L g pre) :
    d'.doomed → FailRead L g (pre ++ [e]) := by
  intro hd
  obtain ⟨site, mm, n, m', n', cp, ap, resp, x, acc, base⟩ := d
  cases site
  case clcStatus =>
    simp only [next] at hn
    split at hn
    · rename_i q r hk
      simp only [Option.some.injEq] at hn
      subst hn
      have hv := (query_site hat hc hf hk).2
      cases hs : r.firstCta.isSome
      · simp only [hs, Bool.false_eq_true, ↓reduceIte] at hd
        have hnone : r.firstCta = none := by simpa using hs
        exact QueryRel.failRead hq (by simp [D.clcStage]) hv (by simp [Loader.claims, hnone]) e
      · simp [hs, D.doomed] at hd
    · cases hn
  case clcFirst =>
    simp only [next] at hn
    split at hn
    · rename_i q r hk
      simp only [Option.some.injEq] at hn
      subst hn
      have hv := (query_site hat hc hf hk).2
      simp only [D.doomed] at hd
      exact QueryRel.failRead hq (by simp [D.clcStage]) hv (by simp [Loader.claims, hd]) e
    · cases hn
  all_goals refine FailRead.snoc (hx ?_) e
  all_goals clear hx hq hat hc hf
  all_goals simp only [next] at hn
  clc_sweep hn
  all_goals simp_all [D.doomed]

/-- A consumer exits only at its exit site. -/
theorem exit_site {d : D} {t : TState} {ins : Instr} {e : Event} {o : Option TState}
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e o) (hk : e.kind = .exit) :
    d.site = .exit := by
  have hpc := ret_pc hc (fires_exit_op hf hk)
  clear hc hf hk
  site_of_pc d hpc

end Consumer

/-- Only a role exits: the prologue has no exit site. -/
theorem exit_role {X : Execution} (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (hg : g < L.threads) {k : Nat} {e : Event} (he : X.get (g, k) = some e) {d : ThreadD}
    (hσ : (code L g).toMachine.after (some (code L g).init) ((X.tr g).take k) = some (some d))
    (hk : e.kind = .exit) : ∃ r, d = .inr r := by
  obtain ⟨o, hf⟩ := (Frame.trace (fun _ => sound hpre) hX hg).fired_at he hσ
  obtain ⟨t, ins, -, -, hc, hfire⟩ := Code.fired_site (sound hpre hg) hf
  rcases d with ⟨site, w⟩ | r
  · exfalso; have hpc := ret_pc hc (fires_exit_op hfire hk)
    clear hc hfire hf hσ; change site.pc ∈ Flow.exit.toList at hpc; revert hpc
    cases site <;> simp only [Prologue.Site.pc] <;> decide +revert
  · exact ⟨r, rfl⟩

end
end PTX.Kernels.Fp16Gemm8192.Proof
