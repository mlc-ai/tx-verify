-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof2.Common.Sound
public import Kernels.InklingRelDecode.Proof2.Ref.Input
public import Kernels.InklingRelDecode.Proof.Thread.EvSEnt
public import Kernels.InklingRelDecode.Proof.Thread.EvDEpiSync

@[expose] public section

/-! # The softmax–epilogue fragment: reference, expectation, step, source

**Reference** (`SmRef`): at a softmax state the entry numbers mean what `Sm.EntMeans` says for the
thread's request, split and KV head (`ctaid.z`, `ctaid.x`, `ctaid.y`). Every successor keeps the
entry numbers (`Interface`-free: `sm_next_e`), and the loop's exit enters the epilogue, whose
reference is empty.

**Expectation** (`SmExpect`, `EpiExpect`): a bias load returns the bytes of a `bf16` number; the
epilogue's Tensor Memory load returns 64 values. Under them the fragment does not stop
(`sm_next_ne`, `epi_next_ne`): these are the fragment's only kind stops. Every other returned
value (the S tile, the shuffled words, the O tile, the row sum's shared word) is followed whatever
it is (rule M1); where it makes a step fault the thread dies, which `StepGood` allows.

**Sources.** A bias load: the read-only input source (`sm_expect`), with the address in closed
form from the entry numbers (`Sm.shape_pre_spec`, `Sm.shape_nxt_spec`) and `Pre.relInput`. The
epilogue's load: its shape alone (`Epi.shape_ld`). No fact about another event of the execution is
used. -/

namespace PTX.Kernels.InklingRelDecode.Proof2
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.InklingRelDecode
open PTX.Kernels.InklingRelDecode.Proof.ProA (cta)

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-! ### Reference and expectation -/

/-- **The softmax states' reference**: the entry numbers mean what `EntMeans` says. -/
def SmRef (Q : Params) (L : Launch) (g : Nat) (d : Proof.Sm.D) : Prop :=
  Proof.Sm.EntMeans Q (cta L g .z) (cta L g .x) (cta L g .y) d.e

/-- A bias load returns a `bf16` number. -/
def SmExpect (d : Proof.Sm.D) (e : Event) : Prop :=
  ∀ j, (d.site = .pre j ∨ d.site = .nxt j) → ∀ a bs, e.kind = .rd a bs →
    ∃ x, rebuild 3 bs = .ok x ∧ Proof.Sm.isBf16 x = true

/-- The epilogue's Tensor Memory load returns 64 values. -/
def EpiExpect (d : Proof.Epi.D) (e : Event) : Prop :=
  d.site = .ld → ∀ a vals sh, e.kind = .tc (.ld a vals sh) → vals.length = 64

/-! ### The fragment does not stop -/

theorem afterSetup_e {d d' : Proof.Sm.D} (h : Proof.Sm.afterSetup L g d = some (some d')) :
    d'.e = d.e := by
  unfold Proof.Sm.afterSetup at h
  split at h
  · cases h
  · split at h <;> (simp only [Option.some.injEq] at h; subst h; rfl)

theorem toBar20_e {d d' : Proof.Sm.D} (h : Proof.Sm.toBar20 d = some (some d')) : d'.e = d.e := by
  unfold Proof.Sm.toBar20 at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    rfl
  · cases h

/-- **The softmax region's successor keeps the entry numbers.** -/
theorem sm_next_e {d d' : Proof.Sm.D} {e : Event} (h : Proof.Sm.next L g d e = some (some d')) :
    d'.e = d.e := by
  unfold Proof.Sm.next at h
  repeat' split at h
  all_goals first
    | (simp only [Option.some.injEq, reduceCtorEq] at h; done)
    | (simp only [Option.some.injEq] at h; subst h; rfl)
    | (have := afterSetup_e h; exact this)
    | (have := toBar20_e h; exact this)

theorem exitNext_ne {d : Proof.Sm.D} : Tail.exitNext L g d ≠ some none := by
  unfold Tail.exitNext
  split <;> simp

open scoped Classical in
/-- **A softmax state does not stop** when a bias load returns a `bf16` number. -/
theorem sm_next_ne {d : Proof.Sm.D} {e : Event} (hE : SmExpect d e) :
    Tail.next L g (.sm d) e ≠ some none := by
  show (if Proof.DComp.leaves L g d e then Tail.exitNext L g d
    else (Proof.Sm.next L g d e).map (Option.map .sm)) ≠ some none
  split
  · exact exitNext_ne
  · rename_i hl
    intro hn
    obtain ⟨pc, k⟩ := e
    cases hs : d.site with
    | pre j =>
      have hb := hE j (.inl hs)
      cases k with
      | rd a bs =>
        obtain ⟨x, hx, hbf⟩ := hb a bs rfl
        simp only [Proof.Sm.next, hs, hx, hbf, Proof.DComp.leaves, Proof.DComp.bf16Read,
          Proof.Sm.afterSetup] at hn hl
        repeat' split at hn
        all_goals first | (simp_all; done) | (have := j.isLt; simp_all; omega)
      | _ => simp [Proof.Sm.next, hs] at hn
    | nxt j =>
      have hb := hE j (.inr hs)
      cases k with
      | rd a bs =>
        obtain ⟨x, hx, hbf⟩ := hb a bs rfl
        simp only [Proof.Sm.next, hs, hx, hbf] at hn
        repeat' split at hn
        all_goals simp_all
      | _ => simp [Proof.Sm.next, hs] at hn
    | _ =>
      simp only [Proof.Sm.next, hs, Proof.DComp.leaves, Proof.Sm.afterArrive,
        Proof.Sm.afterSetup, Proof.Sm.toBar20] at hn hl
      repeat' split at hn
      all_goals simp_all [Proof.DComp.isArrive]

/-- **An epilogue state does not stop** when the Tensor Memory load returns 64 values. -/
theorem epi_next_ne {d : Proof.Epi.D} {e : Event} (hE : EpiExpect d e) :
    Tail.next L g (.epi d) e ≠ some none := by
  intro hn
  obtain ⟨pc, k⟩ := e
  simp only [Tail.next] at hn
  cases hs : d.site with
  | ld =>
    cases k with
    | tc op =>
      cases op with
      | ld a vals sh =>
        have hl := hE hs a vals sh rfl
        simp [Proof.Epi.next, hs, hl] at hn
      | _ => simp [Proof.Epi.next, hs] at hn
    | _ => simp [Proof.Epi.next, hs] at hn
  | _ =>
    simp only [Proof.Epi.next, Proof.Epi.stNext, hs] at hn
    repeat' split at hn
    all_goals simp_all

/-! ### The source of the bias words -/

theorem inputReadOnly_bias_pre (j : Fin 64) :
    Assumptions.inputReadSites.contains (Proof.Sm.Site.pre j).pc = true := by
  revert j; decide

theorem inputReadOnly_bias_nxt (j : Fin 64) :
    Assumptions.inputReadSites.contains (Proof.Sm.Site.nxt j).pc = true := by
  revert j; decide

/-- **A two-byte read at an input site of a `Rel` element returns the `bf16` number there.** -/
theorem rel_input (hpre : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) {i : EvId}
    {pc : Nat} {r tok head c : Nat} {bs : List (Option Byte)} (hr : r < Q.b)
    (htok : tok < Q.qLen r) (hh : head < heads) (hc : c < relPad) (hlen : bs.length = 2)
    (hs : Assumptions.inputReadSites.contains pc = true)
    (he : X.get i = some ⟨pc, .rd (Proof.Sm.globalAcc (Proof.Sm.relAddr Q r tok head c) 2) bs⟩) :
    ∃ x, rebuild 3 bs = .ok x ∧ Proof.Sm.isBf16 x = true := by
  set v := Value.float .bf16 (Q.rel (Q.qStart r + tok) head c) with hv
  have hvb : v.bytes = 2 := by simp [hv, Value.bytes, FloatFmt.bytes]
  have hbs : bs = v.toBytes.map some := by
    refine Frame.bytes_of_pointwise (by rw [hlen, hvb]) fun j hj => ?_
    have hj2 : j < 2 := by rw [← hvb]; exact hj
    exact (hX.asm _ inputReadOnly_mem) i pc _ bs he hs j
      (by simpa [Proof.Sm.globalAcc] using hj2) _
      (by simpa [Loc.at, Proof.Sm.globalAcc, Proof.Sm.relAddr] using
        hpre.relInput r hr tok htok head hh c hc j hj2)
  refine ⟨v, ?_, rfl⟩
  rw [hbs]
  exact rebuild_scalar (by rw [hvb]; decide) rfl

/-- The softmax machine's `Fired` from a concrete state of a softmax state of the fragment. -/
theorem sm_fired {d : Proof.Sm.D} {t : TState} {ins : Instr} {e : Event} {o : Option TState}
    (hat : (Proof.Sm.code Proof.Sm.asms L g d).AtD d t) (hi : Proof.Sm.Inv L g d)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Assumptions.all L g t ins.op) e o) :
    Proof.Sm.Fired L g d e o := by
  refine ⟨t, hat, hi, ?_⟩
  rw [hat.1]
  simpa only [Code.tmpl, hc] using hf

/-- The epilogue machine's `Fired` from a concrete state of an epilogue state of the fragment. -/
theorem epi_fired {d : Proof.Epi.D} {t : TState} {ins : Instr} {e : Event} {o : Option TState}
    (hat : (Proof.Epi.code Proof.Epi.asms L g d).AtD d t) (hi : Proof.Epi.Inv d)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Assumptions.all L g t ins.op) e o) :
    Proof.Epi.Fired L g d e o := by
  refine ⟨t, hat, hi, ?_⟩
  rw [hat.1]
  simpa only [Code.tmpl, hc] using hf

/-- A read's event continues the thread. -/
theorem cont_of_rd {pc : Nat} {mt : Tmpl} {e : Event} {o : Option TState} (hf : Fires pc mt e o)
    {a : Acc} {bs : List (Option Byte)} (hk : e.kind = .rd a bs) : ∃ u, o = some u := by
  cases o with
  | some u => exact ⟨u, rfl⟩
  | none => rcases fires_none_ends hf with ⟨f, hk'⟩ | hk' <;> rw [hk] at hk' <;> cases hk'

/-- **The expectation of a softmax state holds**: its bias loads read the launch's `bf16`
numbers. -/
theorem sm_expect (hpre : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    {d : Proof.Sm.D} {e : Event} {t : TState} {ins : Instr} {o : Option TState} {i : EvId}
    (hg : g < L.threads) (he : X.get i = some e)
    (hat : (Proof.Sm.code Proof.Sm.asms L g d).AtD d t) (hi : Proof.Sm.Inv L g d)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Assumptions.all L g t ins.op) e o)
    (hR : SmRef Q L g d) : SmExpect d e := by
  intro j hj a bs hk
  obtain ⟨u, rfl⟩ := cont_of_rd hf hk
  have hF := sm_fired hat hi hc hf
  obtain ⟨-, hy, hz⟩ := Proof.ProA.cta_lt hpre hg
  rcases hj with hj | hj
  · obtain ⟨bs', hl, hev⟩ := Proof.Sm.shape_pre_spec hpre hR hz hy hF hj
    obtain ⟨-, hrv, hit, hnb⟩ := Proof.Sm.pre_block hR hi hj
    have hbl : cta L g .x < Q.blocks (cta L g .z) := by
      simpa using Proof.Sm.lt_blocks_of_iters (r := cta L g .z) (s := cta L g .x) (i := 0)
        hpre.splitsPos hit
    obtain ⟨htok, hh, hcol, -⟩ := Proof.Sm.biasAddr_spec hpre hR hz hy hi.tid hrv j.isLt hbl hnb
    rw [hev] at hk he
    simp only [Kind.rd.injEq] at hk
    obtain ⟨-, rfl⟩ := hk
    have hsite : Assumptions.inputReadSites.contains (Proof.Sm.evPc d.site) = true := by
      show Assumptions.inputReadSites.contains d.site.pc = true
      rw [hj]
      exact inputReadOnly_bias_pre j
    exact rel_input hpre hX hz htok hh hcol hl hsite he
  · obtain ⟨bs', hl, hev⟩ := Proof.Sm.shape_nxt_spec hpre hR hz hy hF hj
    obtain ⟨-, hrv, hit, hnb⟩ := Proof.Sm.nxt_block hR hi hj
    have hbl := Proof.Sm.lt_blocks_of_iters hpre.splitsPos hit
    obtain ⟨htok, hh, hcol, -⟩ := Proof.Sm.biasAddr_spec hpre hR hz hy hi.tid hrv j.isLt hbl hnb
    rw [hev] at hk he
    simp only [Kind.rd.injEq] at hk
    obtain ⟨-, rfl⟩ := hk
    have hsite : Assumptions.inputReadSites.contains (Proof.Sm.evPc d.site) = true := by
      show Assumptions.inputReadSites.contains d.site.pc = true
      rw [hj]
      exact inputReadOnly_bias_nxt j
    exact rel_input hpre hX hz htok hh hcol hl hsite he

/-- **The expectation of an epilogue state holds**: its Tensor Memory load returns 64 values. -/
theorem epi_expect {d : Proof.Epi.D} {e : Event} {t : TState} {ins : Instr} {o : Option TState}
    (hat : (Proof.Epi.code Proof.Epi.asms L g d).AtD d t) (hi : Proof.Epi.Inv d)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Assumptions.all L g t ins.op) e o) : EpiExpect d e := by
  intro hs a vals sh hk
  obtain ⟨u, rfl⟩ : ∃ u, o = some u := by
    cases o with
    | some u => exact ⟨u, rfl⟩
    | none => rcases fires_none_ends hf with ⟨f, hk'⟩ | hk' <;> rw [hk] at hk' <;> cases hk'
  obtain ⟨vals', hl, hev⟩ := Proof.Epi.shape_ld (epi_fired hat hi hc hf) hs
  rw [hev] at hk
  simp only [Kind.tc.injEq, TcKind.ld.injEq] at hk
  rw [← hk.2.1]
  exact hl

end
end PTX.Kernels.InklingRelDecode.Proof2
