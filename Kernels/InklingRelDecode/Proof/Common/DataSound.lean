-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.DataBounds
import Kernels.InklingRelDecode.Proof.Lib.Coordinates
import Kernels.InklingRelDecode.Proof.Prologue.Checked
import Kernels.InklingRelDecode.Proof.Softmax.StepAt
import Kernels.InklingRelDecode.Proof.Epilogue.StepAt
public import Kernels.InklingRelDecode.Proof.Common.ValueThread
import Lemmas.Flow.GlueU
import Lemmas.Flow.Scalars

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Flow PTX.Proof Arith32

set_option maxRecDepth 100000

private theorem sub_word (a b : Value) (h : ∃ v, Prologue.Control.subValue b a = .bits 32 v) :
    b32 (Lib.word (Prologue.Control.subValue b a)).toNat = Prologue.Control.subValue b a := by
  obtain ⟨v,hv⟩ := h
  cases b <;> first | contradiction |
    (change Value.bits 32 _ = Value.bits 32 (sub32 _ _)
     simp [Prologue.Control.subValue,Lib.word,Value.regBits,sub32,truncBits_idem])

private theorem word_small (n : Nat) (h : n<2^32) : b32 n = b32 (n%2^32) := by
  rw [Nat.mod_eq_of_lt h]

private theorem entry_values {Q L m g w d} (hp : Pre Q L m) (hg : g<L.threads)
    (words : Prologue.Control.Words d) (r : Nat) (key : r ∈ Softmax.Control.ctlLive 574) :
    Softmax.Control.valueOf (dataEntry Q L g w d) L g {} r =
      Prologue.Control.valueOf Q L g w d r := by
  have ks : Softmax.Control.ctlLive 574 = [3,177,462,463,464,478,481,483,485,486,487,490,491,
    527,532,533,610,623,624,666,792,1912,2019,2023,2024] := by decide +kernel
  have coords := Lib.coordinate_bounds hp hg
  obtain ⟨hx,hy,_⟩ := coords
  have split := hp.splitsRange
  have ntok := hp.nTokRange
  have stride := hp.scalarsRange.2.1
  change (L.ctaidOf (g/L.block)).get .x < Q.splits at hx
  change (L.ctaidOf (g/L.block)).get .y < 2 at hy
  rw [ks] at key
  simp only [List.mem_cons,List.not_mem_nil,or_false] at key
  rcases key with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|
    rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact word_small ((L.ctaidOf (g/L.block)).get .x) (by omega)
  · exact sub_word _ _ words.2
  · change b32 (BitVec.toNat _) = Value.bits 32 _
    simp [b32, Prologue.Control.past]
  · change b32 (BitVec.toNat _) = Value.bits 32 _
    simp [b32]
  · change b32 (BitVec.toNat _) = Value.bits 32 _
    simp [b32]
  · change b32 (BitVec.toNat _) = Value.bits 32 _
    simp [b32]
  · exact word_small (((L.ctaidOf (g/L.block)).get .y)*6) (by omega)
  · change Softmax.Control.basePlus w 256 = Lib.addBase w 256
    cases w <;> rfl
  · exact word_small Q.strideRel (by omega)
  · exact word_small Q.splits (by omega)
  · exact word_small Q.nTok (by omega)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · change Softmax.Control.u32 ((_ + 0*_) * 128) = _
    simp only [Nat.zero_mul,Nat.add_zero]; rfl
  · rfl
  · rfl
  · rfl

/-- The constants of the softmax entry (registers 482, 484, 483 and 199) hold at the handoff: the
prologue's control state keeps them to its last site. -/
theorem data_start {Q L g w} {d : Prologue.Control.D} {e : Softmax.Control.Entry} {t : TState}
    (choose : dataExit Q L g w d = some e) (hat : (Prologue.Control.checkedCode Q L g w).AtD d t) :
    Holds t.regs (Softmax.Data.startF e) := by
  unfold dataExit at choose
  split at choose <;> try contradiction
  rename_i hs
  obtain rfl := Option.some.inj choose
  have pc : d.site.pc = 574 := hs ▸ rfl
  obtain ⟨-, -, -, -, regs⟩ := hat
  change Holds _ (factsFrom (Prologue.Control.ctlLive d.site.pc) _) at regs
  rw [pc] at regs
  have k : [482, 484, 483, 199] ⊆ Prologue.Control.ctlLive 574 := by decide +kernel
  exact ⟨holds_mem regs (mem_factsFrom (k (by simp))), holds_mem regs (mem_factsFrom (k (by simp))),
    holds_mem regs (mem_factsFrom (k (by simp))), holds_mem regs (mem_factsFrom (k (by simp))),
    trivial⟩

theorem data_handoff {Q L m g w} (hp : Pre Q L m) (hg : g<L.threads) :
    Code.Handoff (Prologue.Control.checkedCode Q L g w) (fun e => Softmax.Control.code e L g)
      (dataExit Q L g w) := by
  intro d e t choose hat inv
  unfold dataExit at choose
  split at choose <;> try contradiction
  rename_i hs
  obtain rfl := Option.some.inj choose
  have pc : d.site.pc = 574 := hs ▸ rfl
  have words : Prologue.Control.Words d :=
    ⟨inv.2.1 (by rw [pc]; decide), inv.2.2 (by rw [pc]; decide)⟩
  obtain ⟨a,b,c,f,regs⟩ := hat
  constructor
  · refine ⟨a.trans pc,?_,c,f,holds_of_pointwise fun r hr => ?_⟩
    · change t.sub=d.site.sub at b
      rwa [hs] at b
    · rw [entry_values hp hg words r hr]
      change Holds _ (factsFrom (Prologue.Control.ctlLive d.site.pc) _) at regs
      rw [pc] at regs
      have keys : (Softmax.Control.ctlLive 574).isSublist (Prologue.Control.ctlLive 574) := by
        decide +kernel
      exact holds_mem regs (mem_factsFrom ((List.isSublist_iff_sublist.mp keys).subset hr))
  · exact soft_initial_inv hp hg words

private theorem epi_values (e : Softmax.Control.Entry) (ok : e.Ok) (L : Launch) (g i : Nat)
    (v : Softmax.Control.Carry)
    (r : Nat) (hr : r ∈ Epilogue.Control.ctlLive 2565) :
    Softmax.Control.valueOf e L g ⟨.epilogue,i,v⟩ r =
      Epilogue.Control.valueOf (epiEntry e (g%L.block)) L g (b32 0) r := by
  have fields : Epilogue.Control.ctlLive 2565 = [3,173,175,462,463,464,478,491,496,497,533,610,
      624,1760,1956,2023,2024] := by
    decide +kernel
  rw [fields] at hr
  rw [epiEntry_eq ok]
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact Eq.refl (.pred (decide (g%L.block<32)) : Value)
  · exact Eq.refl (.pred (decide (e.blocks=0 ∨ 2^31≤e.blocks)) : Value)
  · exact Eq.refl (.pred (Softmax.Control.validRow e (g%L.block)) : Value)
  · exact Eq.refl (b32 (g%L.block))
  · exact Eq.refl e.base
  · exact Eq.refl (b32 (g%L.block/32))
  · exact Eq.refl (b32 e.split)
  · change Softmax.Control.basePlus e.base 256 = Lib.addBase e.base 256
    cases e.base <;> rfl
  · exact Eq.refl (b32 (Softmax.Control.token (g%L.block)))
  · exact Eq.refl (Softmax.Control.u32 (e.head + Softmax.Control.headInGroup (g%L.block)))
  · exact Eq.refl (b32 e.tokens)
  · exact Eq.refl e.firstWord
  · exact Eq.refl (b32 ((L.sharedBase+213328)%2^32))
  · exact Eq.refl (b32 0)
  · exact Eq.refl (b64 (g%L.block/16%2*64))
  · exact Eq.refl (b64 e.outBase)
  · exact Eq.refl (b64 e.lseBase)

theorem epi_handoff {L g e} : Code.Handoff (Softmax.Control.code e L g)
    (fun _ : Unit => Epilogue.Control.code (epiEntry e (g%L.block)) L g) epiExit := by
  intro d _ t pick ht inv
  obtain ⟨s,i,v⟩ := d
  change (if s=.epilogue then some () else none) = some _ at pick
  split at pick <;> try contradiction
  rename_i hs
  subst s
  obtain ⟨pc,sub,acc,flt,regs⟩ := ht
  refine ⟨⟨pc,sub,acc,flt,holds_of_pointwise fun r hr => ?_⟩,trivial⟩
  have keys : (Epilogue.Control.ctlLive 2565).isSublist (Softmax.Control.ctlLive 2565) := by
    decide +kernel
  change Holds _ (factsFrom (Softmax.Control.ctlLive 2565) _) at regs
  exact (epi_values e inv.entry L g i v r hr) ▸ holds_mem regs
    (mem_factsFrom ((List.isSublist_iff_sublist.mp keys).subset hr))

theorem soft_steps {e L g} : ∀ d, (softCode e L g).StepAtU d :=
  Code.glue_stepsU (fun d _ => Softmax.Control.stepAt d)
    (fun _ d => Epilogue.Control.stepAt d) epi_handoff

/-- The steps of the value machine of the softmax and the epilogue. -/
theorem softD_steps {e : Softmax.Control.Entry} {L : Launch} {g : Nat} :
    ∀ d, (softDCode e L g).StepAtU d :=
  Code.glue_stepsU (fun d _ => Softmax.Data.stepAtS d) (fun _ d => Epilogue.Control.stepAt d) (by
    intro d i t hx ht hi
    obtain ⟨pc, sub, acc, flt, regs⟩ := ht
    exact epi_handoff d.c i t hx ⟨pc, sub, acc, flt,
      ((holds_append _ _ _).mp ((holds_append _ _ _).mp regs).1).1⟩ hi)

theorem data_steps {Q L m g w} (hp : Pre Q L m) (hg : g<L.threads) :
    ∀ d, (dataCode Q L g w).StepAtU d :=
  Code.glue_stepsU (fun d _ => Prologue.Control.checked_stepAt hp d)
    (fun _ d => soft_steps d) (by
      intro d e t hx ht hi
      obtain ⟨a,b⟩ := data_handoff hp hg d e t hx ht hi
      exact ⟨a,b,rfl⟩)

end PTX.Kernels.InklingRelDecode.Proof
