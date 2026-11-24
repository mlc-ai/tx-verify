-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.DCompNext

@[expose] public section

/-!
# The default-partition thread as one site machine

`stepAt` proves `Code.StepAt` for every state of `code L g Q` (`DCompBase.lean`) by delegating to
the regions' machines and linking them at the four places where the thread passes from one region
to the next:

* a common-start state by `DStart.stepAt`; the shuffle's event leads to the prologue's first
  state, whose concrete state is `DStart.good_toProA`'s;
* a prologue state by `ProA.stepAt` (`ProA.next` keeps the inherited registers: `next_pro`); the
  last site's event (`barrier.sync 1`, pc 573) leads to the softmax region's first state by
  `SmEntry.ProA_to_Sm`;
* a softmax state by `smStepAt` (`DCompTail.lean`: the region's step lemmas and `SmObligations`);
  the event that ends the loop (`leaves`) leads through the bridge's first part:
  `SmObligations.exit` runs the thread to pc 2560, `Br.bridge` runs the five local instructions
  (pcs 2560-2564) to the epilogue's first state, the poll of `o_final` (pc 2565), or shows the
  thread dead where a float step has no outcome;
* an epilogue state by `Epi.stepAt_all`.

`sound` is the machine's `Code.Sound`, `machine_sound` its `Machine.Sound`.

## What the machine owes `SmObligations` (the softmax region)

`SmObligations Q L mem0 g` (`DCompTail.lean`): the `Code.StepAt` of `Sm.code` at the sites of the
score stage, and the exit link (the thread's run from the loop's last event to pc 2560 and the
range of the bridge's numbers). Everything else of the softmax region is proved.

## What the protocol layer owes

The machine does not follow the code at the places `next` returns `some none`; for each, the
protocol layer proves the fact that excludes it:

* the load of the Tensor Memory base word (`DStart.Site.ld0`, pc 13) returns one 32-bit word
  below `2 ^ 32` (the allocation stored `b32 col`, `col < 2 ^ 16`), and a load whose bytes
  rebuild to no value is a fault (`next = none`, the thread is dead);
* the shuffle of the common start (`DStart.Site.shfl`, pc 17) returns the warp index
  `g % block / 32` as a 32-bit value;
* the prologue's three loads (`cu_seqlens_q[req]`, `cu_seqlens_q[req + 1]`, `seq_lens[req]`)
  return single 32-bit words (`ProA.word32`), the three satisfy `ProA.WordsOk` (`ProA.next`), and
  they are the request's words (`ProA.WordsMatch Q (ctaid.z)`: `Pre.cuInput`, `Pre.seqInput`);
  `proNext` follows the last prologue event only if they are;
* the prologue's block-table loads return single 32-bit words and its 64 query loads two-byte
  values (`ProA.next`), as `Pre.btInput` and `Pre.qInput` give; its shuffles return the warp
  index;
* the softmax region's bias loads return `bf16` numbers (`Sm.isBf16`; `Pre.relInput`), its
  broadcasts the warp index, its S-tile load 64 four-byte words (`Sm.next`);
* the epilogue's broadcast returns the warp index and its load returns 64 words (`Epi.next`);
* where the bridge's float steps have no outcome (`Br.In.NoFault` fails), `next = none` and the
  thread is dead (`Machine.Dead`): the kernel's theorems exclude it. For an empty row (`l = 0`,
  `mx = -inf`, `num_iters = 0`) the `lg2` of zero must have an outcome; the development notes's
  table
  "thread-layer gaps" records this.

The machine's `init` is the thread's first event (`DStart.D.start`): the allocation for a thread of
warp 0, the first `bar.sync 0` for the others.

## Hypotheses of `sound`

`Pre Q L mem0`, `g < L.threads` (the thread belongs to the launch), `g % L.block < 128` (the
thread is of warp 0 to 3: the default partition) and `SmObligations Q L mem0 g`. -/

namespace PTX.Kernels.InklingRelDecode.Proof.DComp
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {L : Launch} {g : Nat} {Q : Params} {mem0 : Mem0}

/-! ### The common start -/

/-- A common-start state. -/
theorem stepAt_dstart (d : DStart.D) : (code L g Q).StepAt (.dstart d) where
  site hi := (DStart.stepAt (L := L) (g := g) Q d).site hi.1
  step := by
    intro t e u ins h hi hc hf
    have h' : (DStart.code L g Q).AtD d t := h
    rcases (DStart.stepAt (L := L) (g := g) Q d).step ins h' hi.1 hc hf with
      (hn | ⟨d', t', hn, hr, hg'⟩) | ⟨hn, hd⟩
    · refine .inl (.inl ?_)
      have hn' : DStart.next L g d e = some none := hn
      show dstartNext L g Q d e = some none
      simp [dstartNext, hn']
    · have hn' : DStart.next L g d e = some (some d') := hn
      by_cases hd' : d'.site = DStart.Site.toProA
      · obtain ⟨s, tm⟩ := d'
        simp only at hd'
        subst hd'
        have hgp := DStart.good_toProA hg'.2 hg'
        refine .inl (.inr ⟨.pro (ProA.D.start (DStart.inh L g Q (ProA.shW tm)) tm), t', ?_, hr,
          hgp.1, ⟨hgp.2, ProA.shW tm, ProA.shW_lt tm, rfl⟩⟩)
        show dstartNext L g Q d e = _
        simp [dstartNext, hn']
      · refine .inl (.inr ⟨.dstart d', t', ?_, hr, hg'.1, ⟨hg'.2, hd'⟩⟩)
        show dstartNext L g Q d e = _
        simp [dstartNext, hn', hd']
    · refine .inr ⟨?_, hd⟩
      have hn' : DStart.next L g d e = none := hn
      show dstartNext L g Q d e = none
      simp [dstartNext, hn']

/-! ### The prologue -/

/-- A prologue state. -/
theorem stepAt_pro (hpre : Pre Q L mem0) (hg : g < L.threads) (d : ProA.D) :
    (code L g Q).StepAt (.pro d) where
  site hi := ProA.site_ok hi.1
  step := by
    intro t e u ins h hi hc hf
    have h' : (ProA.code L g d.dt.pro).AtD d t := h
    by_cases hb : d.site = ProA.Site.bar18
    · obtain ⟨s, dt⟩ := d
      simp only at hb
      subst hb
      by_cases hm : ProA.WordsMatch Q (ProA.cta L g .z) dt ∧ ProA.wGood dt = true
      · obtain ⟨hm, hgw⟩ := hm
        obtain ⟨tm, -, hpro⟩ := hi.2
        have hs : dt.pro.w71 = Q.splits := by
          rw [show dt.pro = DStart.inh L g Q tm from hpro]
          exact DStart.inh_w71 hpre
        have hp3 : dt.pro.rest 3 = .pred (decide (g % L.block < 32)) := by
          rw [show dt.pro = DStart.inh L g Q tm from hpro]
          exact DStart.inh_rest3
        obtain ⟨h1, h2⟩ := SmEntry.ProA_to_Sm hpre hg hi.1.args hs hm hp3 (ProA.wGood_col hgw)
          (ProA.wGood_w hgw) hpre.nTokPos h' hc hf
        refine .inl (.inr ⟨.sm (SmEntry.d0 (SmEntry.entOf Q L g dt)), u, ?_, .refl,
          ⟨h1.1, h1.2.1, h1.2.2.1, h1.2.2.2.1, h1.2.2.2.2⟩, h2⟩)
        show proNext L g Q ⟨.bar18, dt⟩ e = _
        simp [proNext, hm, hgw]
      · refine .inl (.inl ?_)
        show proNext L g Q ⟨.bar18, dt⟩ e = some none
        simp only [proNext, ↓reduceIte, hm]
    · rcases (ProA.stepAt d.dt.pro d).step ins h' hi.1 hc hf with
        (hn | ⟨d', t', hn, hr, ha, hi'⟩) | ⟨hn, hd⟩ <;> change ProA.next L g d e = _ at hn
      · refine .inl (.inl ?_)
        show proNext L g Q d e = some none
        simp [proNext, hb, hn]
      · obtain ⟨tm, htm, hpro⟩ := hi.2
        refine .inl (.inr ⟨.pro d', t', ?_, hr, ha, ⟨hi', tm, htm,
          (next_pro hn).trans hpro⟩⟩)
        show proNext L g Q d e = _
        simp [proNext, hb, hn]
      · refine .inr ⟨?_, hd⟩
        show proNext L g Q d e = none
        simp [proNext, hb, hn]

/-! ### The softmax region and the bridge -/

/-- A softmax state. -/
theorem stepAt_sm (hpre : Pre Q L mem0) (hso : SmObligations Q L mem0 g) (d : Sm.D) :
    (code L g Q).StepAt (.sm d) where
  site hi := (smStepAt hpre hso d).site hi
  step := by
    intro t e u ins h hi hc hf
    have h' : (Sm.code Sm.asms L g d).AtD d t := h
    by_cases hl : leaves L g d e
    · obtain ⟨hok, t', hr, ht'⟩ := hso.exit hpre hi h' hc hf hl
      have ht2 : At t' 2560 (Br.exitFacts (exitIn L g d)) := by
        rw [exitFacts_eq]
        exact ht'
      obtain ⟨hmain, hdead⟩ := Br.bridge (L := L) (g := g) (exitIn L g d) hok ht2
      by_cases hnf : (exitIn L g d).NoFault
      · obtain ⟨t'', hr2, ht''⟩ := hmain hnf
        refine .inl (.inr ⟨.epi (Epi.D.entry (Br.prm (exitIn L g d)) (exitIn L g d).skip), t'',
          ?_, hr.trans hr2, ⟨ht''.1, ht''.2.1, ht''.2.2.1, ht''.2.2.2.1, ht''.2.2.2.2⟩,
          Epi.entry_inv _ (Br.prm_ok _ hok) (Or.inl rfl) _, rfl⟩)
        show smNext L g d e = _
        cases hsk : (exitIn L g d).skip <;>
          simp [smNext, hl, exitNext, hnf, hsk, Epi.D.start, Epi.D.startSk]
      · refine .inr ⟨?_, dead_of_rtg hr (hdead hnf)⟩
        show smNext L g d e = none
        simp [smNext, hl, exitNext, hnf]
    · rcases (smStepAt hpre hso d).step ins h' hi hc hf with
        (hn | ⟨d', t', hn, hr, hg'⟩) | ⟨hn, hd⟩
      · refine .inl (.inl ?_)
        have hn' : Sm.next L g d e = some none := hn
        show smNext L g d e = some none
        simp [smNext, hl, hn']
      · have hn' : Sm.next L g d e = some (some d') := hn
        refine .inl (.inr ⟨.sm d', t', ?_, hr, hg'⟩)
        show smNext L g d e = _
        simp [smNext, hl, hn']
      · refine .inr ⟨?_, hd⟩
        have hn' : Sm.next L g d e = none := hn
        show smNext L g d e = none
        simp [smNext, hl, hn']

/-! ### The epilogue -/

/-- An epilogue state. -/
theorem stepAt_epi (d : Epi.D) : (code L g Q).StepAt (.epi d) where
  site hi := (Epi.stepAt_all (L := L) (g := g) d d).site hi
  step := by
    intro t e u ins h hi hc hf
    have h' : (Epi.code Epi.asms L g d).AtD d t := h
    rcases (Epi.stepAt_all (L := L) (g := g) d d).step ins h' hi hc hf with
      (hn | ⟨d', t', hn, hr, hg'⟩) | ⟨hn, hd⟩
    · refine .inl (.inl ?_)
      have hn' : Epi.next d e = some none := hn
      show (Epi.next d e).map (Option.map St.epi) = some none
      simp [hn']
    · have hn' : Epi.next d e = some (some d') := hn
      refine .inl (.inr ⟨.epi d', t', ?_, hr, hg'.1, hg'.2.1, hg'.2.2⟩)
      show (Epi.next d e).map (Option.map St.epi) = _
      simp [hn']
    · refine .inr ⟨?_, hd⟩
      have hn' : Epi.next d e = none := hn
      show (Epi.next d e).map (Option.map St.epi) = none
      simp [hn']

/-! ### The machine -/

/-- **Every state of the default-partition thread's machine meets its obligation.** -/
theorem stepAt (hpre : Pre Q L mem0) (hg : g < L.threads) (hso : SmObligations Q L mem0 g)
    (d : St) : (code L g Q).StepAt d := by
  cases d with
  | dstart d => exact stepAt_dstart d
  | pro d => exact stepAt_pro hpre hg d
  | sm d => exact stepAt_sm hpre hso d
  | epi d => exact stepAt_epi d

/-- **The default-partition thread's machine is sound.** A thread of warp 0 to 3 of a launch that
satisfies `Pre` starts in the machine's first state (`DStart.start`), and every state meets its
obligation (`stepAt`) given the softmax region's obligations. -/
theorem sound (hpre : Pre Q L mem0) (hg : g < L.threads) (hw : g % L.block < 128)
    (hso : SmObligations Q L mem0 g) : (code L g Q).Sound where
  start := by
    obtain ⟨t, hr, ht, hi⟩ := DStart.start hpre hg hw
    refine ⟨t, hr, ⟨ht.1, ht.2.1, ht.2.2.1, ht.2.2.2.1, ht.2.2.2.2⟩, hi, ?_⟩
    unfold DStart.D.start
    split_ifs <;> simp
  steps := stepAt hpre hg hso

/-- **The default-partition thread as one `Flow.Machine` with `Machine.Sound`**: the abstract
states are `St` (`.dstart`, `.pro`, `.sm`, `.epi`) with the extra state `none`, which stands for
any state that performs an event (the machine uses it after an event whose continuation it does
not follow). -/
theorem machine_sound (hpre : Pre Q L mem0) (hg : g < L.threads) (hw : g % L.block < 128)
    (hso : SmObligations Q L mem0 g) : (code L g Q).toMachine.Sound :=
  (sound hpre hg hw hso).machine

end
end PTX.Kernels.InklingRelDecode.Proof.DComp
