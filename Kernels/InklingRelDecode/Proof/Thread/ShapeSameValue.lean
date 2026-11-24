-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.DStartHandoff
public import Kernels.InklingRelDecode.Proof.Thread.DStartStart
public import Kernels.InklingRelDecode.Proof.Thread.EvDProSync

@[expose] public section

/-!
# The early shared words are written with one value

Every thread of the default partition executes the prologue's two stores of the early shared
words: the role table (`st8`, an immediate at `global_smem + 213336`) and the pair
`(num_pre, num_iters)` (`st9_0`, `st9_1`, the two elements of one `st.shared.v2.b32` at
`global_smem + 212992`). The stored registers are closed forms of the launch coordinates of the
thread's CTA and the parameters (`exit_values` of `ProBSpec`), not of the thread index. So two
store events of one site, from two threads of one CTA, are the same event: the same footprint and
the same bytes (`early_store_same`). This is what the safety layer's same-value-write exemption
(`SameValueWrites`) needs.

The premise is the one `ProBSpec` has: the three words the prologue loaded are the request's
(`WordsMatch`, from `Pre.cuInput` and `Pre.seqInput`; the protocol layer owes it). The inherited
registers of a prologue state are `DStart.inh`.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.ProA
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {g g' : Nat} {d d' : D} {e e' : Event}
  {u u' : TState}

/-- The launch coordinates of a thread are those of its CTA. -/
theorem cta_eq_of_block (h : g / L.block = g' / L.block) (a : Dim) : cta L g a = cta L g' a := by
  unfold cta
  rw [h]

/-- **The role table is stored by every thread with one value**: two `st8` events of one CTA are
the same event. -/
theorem st8_same (hF : Fired L g d e (some u)) (hF' : Fired L g' d' e' (some u'))
    (hs : d.site = .st8) (hs' : d'.site = .st8) (hc : g / L.block = g' / L.block) : e = e' := by
  obtain ⟨v, hv, he⟩ := shape_st8 hF hs
  obtain ⟨v', hv', he'⟩ := shape_st8 hF' hs'
  have hvv : v = v' := Except.ok.inj (hv.symm.trans hv')
  rw [he, he', hs, hs', hc, hvv]

/-- **The words `(num_pre, num_iters)` are the same for every thread of a CTA**: the registers
the prologue stores are closed forms of the CTA's coordinates. -/
theorem st9_words_same (hpre : Pre P L mem0) (hg : g < L.threads) (hg' : g' < L.threads)
    {dt dt' : Dat} (ha : ArgsOk L g dt.pro) (ha' : ArgsOk L g' dt'.pro)
    (hs : dt.pro.w71 = P.splits) (hs' : dt'.pro.w71 = P.splits)
    (hm : WordsMatch P (cta L g .z) dt) (hm' : WordsMatch P (cta L g' .z) dt')
    (hc : g / L.block = g' / L.block) :
    numPreW L g dt = numPreW L g' dt' ∧ numItersW L g dt = numItersW L g' dt' := by
  obtain ⟨h1, h2⟩ := st9_values hpre hg ha hs hm
  obtain ⟨h1', h2'⟩ := st9_values hpre hg' ha' hs' hm'
  rw [h1, h2, h1', h2', cta_eq_of_block hc .z, cta_eq_of_block hc .x]
  exact ⟨rfl, rfl⟩

/-- **The pair `(num_pre, num_iters)` is stored by every thread with one value**: two `st9_0`
events of one CTA are the same event. -/
theorem st9_0_same (hpre : Pre P L mem0) (hg : g < L.threads) (hg' : g' < L.threads)
    (ha : ArgsOk L g d.dt.pro) (ha' : ArgsOk L g' d'.dt.pro)
    (hs : d.dt.pro.w71 = P.splits) (hs' : d'.dt.pro.w71 = P.splits)
    (hm : WordsMatch P (cta L g .z) d.dt) (hm' : WordsMatch P (cta L g' .z) d'.dt)
    (hF : Fired L g d e (some u)) (hF' : Fired L g' d' e' (some u'))
    (hd : d.site = .st9_0) (hd' : d'.site = .st9_0) (hc : g / L.block = g' / L.block) :
    e = e' := by
  obtain ⟨v, hv, he⟩ := shape_st9_0 hF hd
  obtain ⟨v', hv', he'⟩ := shape_st9_0 hF' hd'
  rw [(st9_words_same hpre hg hg' ha ha' hs hs' hm hm' hc).1] at hv
  have hvv : v = v' := Except.ok.inj (hv.symm.trans hv')
  rw [he, he', hd, hd', hc, hvv]

/-- Two `st9_1` events of one CTA are the same event. -/
theorem st9_1_same (hpre : Pre P L mem0) (hg : g < L.threads) (hg' : g' < L.threads)
    (ha : ArgsOk L g d.dt.pro) (ha' : ArgsOk L g' d'.dt.pro)
    (hs : d.dt.pro.w71 = P.splits) (hs' : d'.dt.pro.w71 = P.splits)
    (hm : WordsMatch P (cta L g .z) d.dt) (hm' : WordsMatch P (cta L g' .z) d'.dt)
    (hF : Fired L g d e (some u)) (hF' : Fired L g' d' e' (some u'))
    (hd : d.site = .st9_1) (hd' : d'.site = .st9_1) (hc : g / L.block = g' / L.block) :
    e = e' := by
  obtain ⟨v, hv, he⟩ := shape_st9_1 hF hd
  obtain ⟨v', hv', he'⟩ := shape_st9_1 hF' hd'
  rw [(st9_words_same hpre hg hg' ha ha' hs hs' hm hm' hc).2] at hv
  have hvv : v = v' := Except.ok.inj (hv.symm.trans hv')
  rw [he, he', hd, hd', hc, hvv]

/-- The sites of the prologue's two stores of the early shared words. -/
def EarlySite (s : Site) : Prop := s = .st8 ∨ s = .st9_0 ∨ s = .st9_1

/-- An event fired at an early store site is a write. -/
theorem early_store_wr (hF : Fired L g d e (some u)) (hE : EarlySite d.site) :
    ∃ pc a bs, e = ⟨pc, .wr a bs⟩ := by
  rcases hE with h | h | h
  · obtain ⟨v, -, he⟩ := shape_st8 hF h
    exact ⟨_, _, _, he⟩
  · obtain ⟨v, -, he⟩ := shape_st9_0 hF h
    exact ⟨_, _, _, he⟩
  · obtain ⟨v, -, he⟩ := shape_st9_1 hF h
    exact ⟨_, _, _, he⟩

/-- **Two store events of the early shared words, from two threads of one CTA at the same store
site, are the same event** (the same footprint, the same bytes), for threads of the default
partition whose prologue state holds the inherited registers of the launch (`DStart.inh`) and
whose loaded words are the request's. -/
theorem early_store_same (hpre : Pre P L mem0) (hg : g < L.threads) (hg' : g' < L.threads)
    (hw : g % L.block < 128) (hw' : g' % L.block < 128) {tm tm' : Nat}
    (hpro : d.dt.pro = DStart.inh L g P tm) (hpro' : d'.dt.pro = DStart.inh L g' P tm')
    (hm : WordsMatch P (cta L g .z) d.dt) (hm' : WordsMatch P (cta L g' .z) d'.dt)
    (hF : Fired L g d e (some u)) (hF' : Fired L g' d' e' (some u'))
    (hsite : d.site = d'.site) (hE : EarlySite d.site) (hc : g / L.block = g' / L.block) :
    e = e' := by
  have ha : ArgsOk L g d.dt.pro := by
    rw [hpro]
    exact DStart.argsOk_inh hpre hg hw tm
  have ha' : ArgsOk L g' d'.dt.pro := by
    rw [hpro']
    exact DStart.argsOk_inh hpre hg' hw' tm'
  have hs : d.dt.pro.w71 = P.splits := by
    rw [hpro]
    exact DStart.inh_w71 hpre
  have hs' : d'.dt.pro.w71 = P.splits := by
    rw [hpro']
    exact DStart.inh_w71 hpre
  rcases hE with h | h | h
  · exact st8_same hF hF' h (hsite.symm.trans h) hc
  · exact st9_0_same hpre hg hg' ha ha' hs hs' hm hm' hF hF' h (hsite.symm.trans h) hc
  · exact st9_1_same hpre hg hg' ha ha' hs hs' hm hm' hF hF' h (hsite.symm.trans h) hc

end
end PTX.Kernels.InklingRelDecode.Proof.ProA
