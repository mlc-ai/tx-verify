-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.Lk5Defs
public import Kernels.InklingRelDecode.Proof.Interface.RdDPred
public import Kernels.InklingRelDecode.Proof.Interface.ClassCopyPage
public import Kernels.InklingRelDecode.Proof.Thread.Lk5VEpi

@[expose] public section

/-!
# The shuffles of a default-partition thread, counted along its trace

A default-partition thread makes one shuffle in the common start, one in each block the prologue
preloads (`num_pre` of them), `smBase i + smOff` in the softmax region up to iteration `i`, and one
in the epilogue unless the split has no block. `cntF` is that count as a function of the state
(the thread's CTA fixes `num_pre` and `num_iters`, `NP` and `NI`); `cnt_inv` proves that the
number of shuffle events before each state is `cntF` of the state, along the trace, with the side
facts `cntSide` (the middle of an iteration is reached from the second on; the epilogue's load
branch is taken only where the split has a block, and its flag is the CTA's).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface.Lk
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.InklingRelDecode.Proof.Mbar (wordsSo_all)

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-- `num_pre` of the thread's CTA. -/
def NP (Q : Params) (L : Launch) (g : Nat) : Nat :=
  ProA.numPre Q (ProA.cta L g .z) (ProA.cta L g .x)

/-- `num_iters` of the thread's CTA. -/
def NI (Q : Params) (L : Launch) (g : Nat) : Nat := Q.numIters (ProA.cta L g .z) (ProA.cta L g .x)

/-- **The shuffles of a default-partition thread before a state.** -/
def cntF (Q : Params) (L : Launch) (g : Nat) : TSt → Nat
  | .d (.dstart d) => DStart.dsW d
  | .d (.pro d) => 1 + ProA.proW L g d
  | .d (.sm d) => 1 + NP Q L g + Sm.smW d
  | .d (.epi d) => 1 + NP Q L g + Sm.smBase (NI Q L g) + Epi.epW d
  | .w _ => 0

/-- The flag of the epilogue's branch `num_iters < 1` of the thread's CTA. -/
def skC (Q : Params) (L : Launch) (g : Nat) : Bool :=
  decide (toSigned 32 (BitVec.ofNat 64 (NI Q L g)) < 1)

/-- **The side facts of the count.** -/
def cntSide (Q : Params) (L : Launch) (g : Nat) : TSt → Prop
  | .d (.sm d) => Sm.smMid d.site = true → 1 ≤ d.i
  | .d (.epi d) => (Epi.epLoad d.site = true → d.sk = false) ∧ d.sk = skC Q L g
  | _ => True

/-! ### The shuffle states of each region -/

theorem ds_shfl (s : DStart.Site) : shflPc s.pc = DStart.dsShfl s := by
  cases s <;> decide +kernel

theorem pro_shfl : ∀ s : ProA.Site, shflPc s.pc = ProA.proShfl s := by
  intro s
  cases s <;> decide +kernel

theorem pre_shfl : ∀ j : Fin 64, shflPc (Sm.Site.pre j).pc = false := by decide +kernel

theorem nxt_shfl : ∀ j : Fin 64, shflPc (Sm.Site.nxt j).pc = false := by decide +kernel

theorem sm_shfl (s : Sm.Site) : shflPc s.pc = Sm.smShfl s := by
  cases s with
  | pre j => rw [pre_shfl]; rfl
  | nxt j => rw [nxt_shfl]; rfl
  | _ => decide +kernel

theorem epi_shfl (s : Epi.Site) : shflPc s.pc = Epi.epShfl s := by
  cases s with
  | stO k =>
    have : ∀ k : Fin 64, shflPc (Epi.Site.stO k).pc = false := by decide +kernel
    rw [this]; rfl
  | _ => decide +kernel

/-! ### One step -/

/-- The count of a softmax state at an event that leaves the loop. -/
theorem leaves_smW {d : Sm.D} {e : Event} (hl : DComp.leaves L g d e) :
    Sm.smW d = Sm.smBase d.e.r26 ∧ Sm.smShfl d.site = false := by
  obtain ⟨s, en, i, m, l, cw, cv, w, v, sv, pf, stg⟩ := d
  cases s <;> simp only [DComp.leaves] at hl <;>
    first
    | exact absurd hl id
    | (simp only [Sm.smW, Sm.smOff, Sm.smShfl, hl.2, and_true]; simp)
    | (simp only [Sm.smW, Sm.smOff, Sm.smShfl, hl.2.2, and_true]; simp)
    | (simp only [Sm.smW, Sm.smOff, Sm.smShfl, and_true]
       rw [hl.2, Sm.smBase_succ])

/-- `num_iters` of a softmax state is the CTA's. -/
theorem r26_eq (hpre : Pre Q L mem0) (hf : ThreadFacts Q L mem0 X) {k : Nat} {d : Sm.D}
    {e : Event} (hX : Consistent L kernel asms mem0 X) (hg : g < L.threads)
    (he : X.get (g, k) = some e) (hσ : St Q L X g k = some (some (.d (.sm d)))) :
    d.e.r26 = NI Q L g := by
  have hI : Sm.Inv L g d := by
    obtain ⟨t, ins, o, -, hinv, -, -⟩ := Frame.fired_site hf.sound hX he hσ
    exact hinv.2
  have hr := (hf.reach hg hσ).2
  have h25 : d.e.r25 = NI Q L g := hr.ent.r25
  have hlt : NI Q L g < 2 ^ 31 := by
    have hr := (ProA.cta_lt hpre hg).2.2
    have h1 := SmEntry.iters_lt Q (ProA.cta L g .z) (ProA.cta L g .x) hpre.splitsPos
    have h2 := hpre.seqRange _ hr
    unfold Params.blocks at h1
    unfold NI
    omega
  rw [hI.ok.r26, h25]
  simp only [hlt, ↓reduceIte]

/-- **One step of a default-partition thread** keeps the count and the side facts. -/
theorem cnt_step (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hg : g < L.threads) {k : Nat} {e : Event} {s t : DComp.St}
    (he : X.get (g, k) = some e) (hσ : St Q L X g k = some (some (.d s)))
    (hn : DComp.next L g Q s e = some (some t)) (hS : cntSide Q L g (.d s)) :
    cntF Q L g (.d t) = cntF Q L g (.d s) + (if shflSt (.d s) then 1 else 0) ∧
      cntSide Q L g (.d t) := by
  cases s with
  | dstart d =>
    change DComp.dstartNext L g Q d e = _ at hn
    unfold DComp.dstartNext at hn
    obtain ⟨d', hd', rfl⟩ := map_map_eq_some_some hn
    have h1 := DStart.dsW_next hd'
    have hsh : shflSt (.d (.dstart d)) = DStart.dsShfl d.site := ds_shfl d.site
    rw [hsh]
    split
    · rename_i hs
      refine ⟨?_, trivial⟩
      simp only [cntF, DStart.dsW, hs, ↓reduceIte] at h1 ⊢
      rw [← h1]
      rfl
    · rename_i hs
      exact ⟨h1, trivial⟩
  | pro d =>
    have hsh : shflSt (.d (.pro d)) = ProA.proShfl d.site := pro_shfl d.site
    rw [hsh]
    change DComp.proNext L g Q d e = _ at hn
    unfold DComp.proNext at hn
    split at hn
    · rename_i hb
      split at hn
      · rename_i hm
        simp only [Option.some.injEq] at hn
        subst hn
        obtain ⟨hdef, tm, -, hpro⟩ := hf.reach hg hσ
        have ha : ProA.ArgsOk L g d.dt.pro := by
          rw [hpro]; exact DStart.argsOk_inh hpre hg hdef tm
        have hw : d.dt.pro.w71 = Q.splits := by rw [hpro]; exact DStart.inh_w71 hpre
        have hnp := ProA.npOf_eq hpre hg ha hw hm.1
        obtain ⟨s, dt⟩ := d
        simp only at hb
        subst hb
        refine ⟨?_, fun h => by simp [SmEntry.d0, Sm.smMid] at h⟩
        simp only [cntF, ProA.proW_q dt (by decide : ProA.inBlk .bar18 = false)]
        simp only at hnp
        rw [hnp]
        simp [Sm.smW, SmEntry.d0, Sm.smBase, Sm.smOff, ProA.proShfl, NP]
      · cases hn
    · obtain ⟨d', hd', rfl⟩ := map_map_eq_some_some hn
      have hG := (pgSo_all hpre hX hf k _ hσ).1
      obtain ⟨s, dt⟩ := d
      refine ⟨?_, trivial⟩
      simp only [cntF]
      rw [ProA.proW_next hd' hG]
      omega
  | sm d =>
    have hsh : shflSt (.d (.sm d)) = Sm.smShfl d.site := sm_shfl d.site
    rw [hsh]
    change DComp.smNext L g d e = _ at hn
    unfold DComp.smNext at hn
    split at hn
    · rename_i hl
      unfold DComp.exitNext at hn
      split at hn
      · simp only [Option.some.injEq] at hn
        subst hn
        obtain ⟨h1, h2⟩ := leaves_smW hl
        have h26 := r26_eq hpre hf hX hg he hσ
        have hr := (hf.reach hg hσ).2
        have h25 : d.e.r25 = NI Q L g := hr.ent.r25
        split
        · rename_i hk
          refine ⟨?_, ?_⟩
          · simp [cntF, h1, h2, h26, Epi.epW, Epi.D.startSk, Epi.D.entry]
          · refine ⟨fun h => by simp [Epi.D.startSk, Epi.D.entry, Epi.epLoad] at h, ?_⟩
            simp only [Epi.D.startSk, Epi.D.entry, skC]
            simp only [Br.In.skip, DComp.exitIn, h25] at hk
            simp [hk]
        · rename_i hk
          refine ⟨?_, ?_⟩
          · simp [cntF, h1, h2, h26, Epi.epW, Epi.D.start, Epi.D.entry]
          · refine ⟨fun h => by simp [Epi.D.start, Epi.D.entry, Epi.epLoad] at h, ?_⟩
            simp only [Epi.D.start, Epi.D.entry, skC]
            simp only [Br.In.skip, DComp.exitIn, h25] at hk
            simp [hk]
      · cases hn
    · obtain ⟨d', hd', rfl⟩ := map_map_eq_some_some hn
      obtain ⟨h1, h2⟩ := Sm.smW_next hd' hS
      refine ⟨?_, h2⟩
      simp only [cntF, h1]
      omega
  | epi d =>
    have hsh : shflSt (.d (.epi d)) = Epi.epShfl d.site := epi_shfl d.site
    rw [hsh]
    change (Epi.next d e).map (Option.map DComp.St.epi) = _ at hn
    obtain ⟨d', hd', rfl⟩ := map_map_eq_some_some hn
    obtain ⟨hS1, hS2⟩ := hS
    obtain ⟨h1, h2⟩ := Epi.epW_next hd' hS1
    have hsk : d'.sk = d.sk := by
      obtain ⟨s, pr, o, sk⟩ := d
      cases s <;> simp only [Epi.next] at hd' <;> (repeat' split at hd') <;>
        first
        | (cases hd'; done)
        | (simp only [Option.some.injEq] at hd'; subst hd'; rfl)
        | (simp only [Option.some.injEq] at hd'; subst hd'
           unfold Epi.stNext; split <;> rfl)
    refine ⟨?_, h2, hsk.trans hS2⟩
    simp only [cntF, h1]
    omega

/-- **The shuffles before each state of a default-partition thread are `cntF` of the state.** -/
theorem cnt_inv (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hg : g < L.threads) :
    ∀ k, k ≤ (X.tr g).length → ∀ {s : DComp.St}, St Q L X g k = some (some (.d s)) →
      cnt Execution.isShfl X g k = cntF Q L g (.d s) ∧ cntSide Q L g (.d s) := by
  intro k
  induction k with
  | zero =>
    intro _ s hσ
    rcases pred_d (Nat.zero_le _) hσ with ⟨-, rfl⟩ | ⟨k0, -, -, h, -⟩
    · refine ⟨?_, trivial⟩
      simp only [cnt, List.take_zero, List.countP_nil, cntF, DComp.code, DStart.D.start]
      split <;> rfl
    · omega
  | succ k ih =>
    intro hk s hσ
    rcases pred_d hk hσ with ⟨h0, -⟩ | ⟨k0, e, s0, hk0, he, hσ0, hn⟩
    · omega
    · have hk0' : k0 = k := by omega
      subst hk0'
      obtain ⟨hc, hS⟩ := ih (by omega) hσ0
      have he' : X.get (g, k0) = some e := he
      obtain ⟨h1, h2⟩ := cnt_step hpre hX hf hg he' hσ0 hn hS
      refine ⟨?_, h2⟩
      rw [cnt_succ _ he, hc, isShfl_state hX hf hg he' hσ0, h1]

end
end PTX.Kernels.InklingRelDecode.Proof.Interface.Lk
