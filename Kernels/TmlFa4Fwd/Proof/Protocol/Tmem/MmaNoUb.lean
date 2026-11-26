-- SPDX-License-Identifier: Apache-2.0
module

import Lemmas.Kernel.FrameU

public import Kernels.TmlFa4Fwd.Proof.Common.Inj
public import Core.Assembly.Execution
public import Core.Data.Types
public import Core.Data.Value
public import Core.Source.Instr
public import Core.Thread.Run
public import Kernels.TmlFa4Fwd.Assumptions
public import Kernels.TmlFa4Fwd.Proof.Lib.WarpIndex
public import Kernels.TmlFa4Fwd.Proof.Common.Roles
public import Kernels.TmlFa4Fwd.Proof.Epilogue.Machine
public import Kernels.TmlFa4Fwd.Proof.Lib.AfterTiles
public import Kernels.TmlFa4Fwd.Proof.Mma.Fits
public import Kernels.TmlFa4Fwd.Proof.Mma.Machine
public import Kernels.TmlFa4Fwd.Proof.Mma.Ref
public import Kernels.TmlFa4Fwd.Proof.Mma.Sim
public import Kernels.TmlFa4Fwd.Proof.SmWarp.Export.Follow
public import Kernels.TmlFa4Fwd.Spec
public import Lemmas.Flow.Code
public import Lemmas.Kernel.Frame
import Kernels.TmlFa4Fwd.Flow.Code.Part030
import Kernels.TmlFa4Fwd.Flow.Code.Part031
import Kernels.TmlFa4Fwd.Flow.Code.Part041
import Kernels.TmlFa4Fwd.Flow.Code.Part042
import Kernels.TmlFa4Fwd.Proof.Common.NoUb
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Kernels.TmlFa4Fwd.Proof.Epilogue.NoUb
import Kernels.TmlFa4Fwd.Proof.Epilogue.Export.Safe
import Lemmas.Flow.MemAl
import Kernels.TmlFa4Fwd.Proof.Lib.NoUbLive
import Kernels.TmlFa4Fwd.Proof.Mma.Export.Safe
import Kernels.TmlFa4Fwd.Proof.Mma.Export.SafeCm
import Kernels.TmlFa4Fwd.Proof.Mma.Export.SafePre
import Kernels.TmlFa4Fwd.Proof.Mma.Export.SafeRd
import Kernels.TmlFa4Fwd.Proof.Mma.Export.DescOf
import Kernels.TmlFa4Fwd.Proof.Mma.Export.Desc
import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.Word
import Std.Tactic.BVDecide.Normalize.Prop

import Lemmas.Kernel.NoUbFollowedSites
import Kernels.TmlFa4Fwd.Proof.Common.SharedSites
import Kernels.TmlFa4Fwd.Proof.Common.DataSound

@[expose] public section

/-! # No event of the MMA warp is undefined behaviour

`Frame.noUb_of_followed_live` for the lanes of warp 12 (`mma_noUb`), followed with `Mma.Ref` by
`Mma.good`.

`safe`: the startup's fence path (`start_safe`), the allocation prefix (`Mma.pre_safe`), and per
role site: the scheduler's reads at 4-aligned cuQ words (`word_safe`, the output warp's
`rd_aligned`), the request reads (`read_safe`), the read of the allocation word
(`alloc_read_safe`), the polls, elections and the relinquish (`sync_safe`), the commits
(`commit_safe`), the 64 MMA issues (`mma_safe`, with the descriptor words of `mma_desc`) and the
deallocation (`dealloc_safe`, with the word 0 of `ta_zero`); no other site's shape admits
undefined behaviour. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Mma
open PTX PTX.Proof PTX.Flow
open PTX.Flow.Arith32

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

set_option maxHeartbeats 4000000 in
/-- **The scheduler's reads are no undefined behaviour**: their cuQ words are 4-aligned. -/
theorem word_safe (hp : Pre p L m) {d : D} {ns nv : Nat} (hF : MFits p L g d ns nv) {t : TState}
    {ins : Instr} {e : Event} {o : Option TState} (h : (code p L g (ent p L)).AtD d t)
    (hc : kernel.code[(code p L g (ent p L)).pc d]? = some ins)
    (hf : Fires ((code p L g (ent p L)).pc d) (eventTmpl Assumptions.all L g t ins.op) e o)
    (hs : ∃ k, d.site = .word k) (f : Fault) : e.kind ≠ .ub f := by
  replace h : At t d.site.pc (facts p L g (ent p L) d) := h
  replace hc : kernel.code[d.site.pc]? = some ins := hc
  obtain ⟨k, hs⟩ := hs
  have he : d.site.early = false := by rw [hs]; rfl
  obtain ⟨-, hFE, -⟩ := mfits_main he hF
  have hal := Epilogue.rd_aligned hp hFE (.inl ⟨k, by simp only [toE, hs, Site.epi]⟩)
  obtain ⟨site, v⟩ := d
  simp only at hs
  subst hs
  intro hk
  have hu := fires_ub hf hk
  cases k <;>
  · obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
    refine ldGlobal_ok' rfl rfl rfl rfl rfl rfl (by decide) (reg_of h (by lit_mem)) ?_ f hu
    exact hal

set_option maxHeartbeats 8000000 in
/-- **No event a role state of the MMA warp fires under its reference values is undefined
behaviour.** -/
theorem role_safe (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X)
    (hg : g < L.threads) (h12 : Prologue.warpIndex L g = 12) {k : Nat} {d : D}
    {n : Cls → Nat} {e : Event} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (thread p L) X g k = some (some (minj p L g d n)))
    (hF : MFits p L g d (n .shfl) (n .vote)) (f : Fault) : e.kind ≠ .ub f := by
  have hk : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp
    (show (X.tr g)[k]? = _ from he)).1
  obtain ⟨t, ins, o, hat, -, hc, hf⟩ :=
    strict_fired_site hp hX he hσ rfl
  have hev := (mfired hp hX he hσ).1
  have hDk : DOk L d := mma_desc hp hX hg h12 k hk.le _ hσ
  obtain ⟨s, v⟩ := d
  replace hat : (code p L g (ent p L)).AtD ⟨s, v⟩ t := hat
  replace hc : kernel.code[(code p L g (ent p L)).pc ⟨s, v⟩]? = some ins := hc
  replace hf : Fires ((code p L g (ent p L)).pc ⟨s, v⟩) (eventTmpl Assumptions.all L g t ins.op)
    e o := hf
  cases s
  case word kk => exact word_safe hp hF hat hc hf ⟨kk, rfl⟩ f
  case q0 => exact read_safe hp hF hat hc hf (.inl rfl) f
  case q1 => exact read_safe hp hF hat hc hf (.inr (.inl rfl)) f
  case uk => exact read_safe hp hF hat hc hf (.inr (.inr rfl)) f
  case ldAlloc => exact alloc_read_safe hp hat hc hf rfl f
  case wt kk => exact sync_safe hp hat hc hf (.inl ⟨kk, rfl⟩) f
  case mw b l => exact sync_safe hp hat hc hf (.inr (.inl ⟨b, l, rfl⟩)) f
  case eq b => exact sync_safe hp hat hc hf (.inr (.inr (.inl ⟨b, rfl⟩))) f
  case ep b => exact sync_safe hp hat hc hf (.inr (.inr (.inr (.inl ⟨b, rfl⟩)))) f
  case ce c => exact sync_safe hp hat hc hf (.inr (.inr (.inr (.inr (.inl ⟨c, rfl⟩))))) f
  case relinq l => exact sync_safe hp hat hc hf (.inr (.inr (.inr (.inr (.inr ⟨l, rfl⟩))))) f
  case cm c => exact commit_safe hp hg hat hc hf ⟨c, rfl⟩ f
  case qk b j => exact mma_safe hp hg hat hc hf hDk (.inl ⟨b, j, rfl⟩) f
  case pv b j => exact mma_safe hp hg hat hc hf hDk (.inr ⟨b, j, rfl⟩) f
  case dealloc l =>
    exact dealloc_safe hp hat hc hf (ta_zero hp hX hFw hg h12 hk.le hσ rfl) f
  all_goals
    intro hk'
    obtain ⟨pc, kind⟩ := e
    simp only at hk'
    subst hk'
    simp [Ev, Epilogue.Ev, Site.toE] at hev

/-- At the first pass's tile count the MMA warp dies only where the output warp does: the two
coordinate divisions are the same terms. -/
theorem afterTiles_none {d : D} {x : BitVec 64} (h : afterTiles p L g d x = none) :
    Epilogue.afterTiles p L g (toE d) x = none := by
  unfold afterTiles at h
  unfold Epilogue.afterTiles
  dsimp only [scAt] at h ⊢
  exact afterTiles_none_of rfl rfl rfl rfl h

set_option maxHeartbeats 4000000 in
theorem tiles_none {d : D} {e : Event} (hs : d.site = .tiles false)
    (h : succ p L g d e = none) : Epilogue.succ p L g (toE d) e = none := by
  obtain ⟨site, v⟩ := d
  simp only at hs
  subst hs
  obtain ⟨pc, kind⟩ := e
  revert h
  cases kind <;> simp only [succ, Epilogue.succ, toE, Site.epi, reduceCtorEq, imp_self]
  rename_i md a b c r o
  cases r <;> (try simp only [reduceCtorEq, imp_self])
  rename_i w x
  intro h
  split at h
  · rename_i heq0
    simp only [Value.bits.injEq] at heq0
    obtain ⟨rfl, rfl⟩ := heq0
    simp only [Bool.false_eq_true, ↓reduceIte, Option.map_eq_none_iff] at h ⊢
    exact afterTiles_none (d := ⟨.tiles false, v⟩) h
  · cases h

set_option maxHeartbeats 8000000 in
/-- **A role state of the MMA warp dies only at the exit** on an event that is no undefined
behaviour: the scheduler's steps as the output warp's (`Epilogue.next_none`, through `succ_scan`
and `tiles_none`), the used-K read by its reference, the allocation word's read by `ld_word`. -/
theorem role_live (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X)
    (hg : g < L.threads) (h12 : Prologue.warpIndex L g = 12) {k : Nat} {d : D}
    {n : Cls → Nat} {e : Event} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (thread p L) X g k = some (some (minj p L g d n)))
    (hJ : RefCounts p L g (d, rc n)) (hF : MFits p L g d (n .shfl) (n .vote))
    (hub : ∀ f, e.kind ≠ .ub f) (hn : succ p L g d e = none) : e.kind = .exit := by
  have hReads := cuQReadsFromLaunch hp hX
  have IH : ∀ n, GoodUpTo p L X n := fun _ h j hin _ => good hp hX hReads hin.1 hin.2 j
  have hE := mexpect hp hX hReads hg h12 he hσ hJ hF (fun _ => IH _)
  have hev := (mfired hp hX he hσ).1
  by_cases hsc : d.site.scan = true
  · have hsch : (d.site.sched || d.site == .tiles false) = true := by
      obtain ⟨s, v⟩ := d
      cases s <;> simp only [Site.scan, Bool.false_eq_true] at hsc <;>
        first | rfl | (rename_i l; cases l <;> rfl)
    have hE' := mexpect_sched hsch hE
    have hne := sched_early hsch
    obtain ⟨-, hFE, -⟩ := mfits_main hne.1 hF
    refine Epilogue.next_none hp hg hFE hE' (ev_toE hsc hev) hub ?_
    show Epilogue.succ p L g (toE d) e = none
    by_cases ht : d.site = .tiles false
    · exact tiles_none ht hn
    · have hs' : d.site.sched = true := by
        obtain ⟨s, v⟩ := d
        cases s <;> simp only [Site.scan, Bool.false_eq_true] at hsc <;> first
          | rfl | (rename_i l; cases l <;> first | rfl | exact absurd rfl ht)
      rw [succ_scan hs'] at hn
      simpa using hn
  obtain ⟨s, v⟩ := d
  obtain ⟨pc, kind⟩ := e
  cases s
  case exit l => simpa [Ev] using hev
  case q0 | q1 | uk =>
    all_goals simp only [Ev] at hev
    all_goals rcases hev with ⟨bs, hk⟩ | ⟨f, hk⟩
    all_goals try exact absurd hk (hub f)
    all_goals subst hk
    all_goals simp only [MExpect, Site.sched, Bool.true_or, Epilogue.Expect, toE, Site.epi,
      forall_const] at hE
    all_goals simp [succ, hE, word32] at hn
  case ldAlloc =>
    simp only [Ev] at hev
    rcases hev with ⟨a, bs, hk⟩ | ⟨f, hk⟩
    · subst hk
      rw [ld_word hp hX hFw hg h12 hσ he] at hn
      simp [succ, rebuild_zero] at hn
    · exact absurd hk (hub f)
  all_goals try (simp [Site.scan] at hsc; done)
  all_goals simp only [Ev] at hev
  all_goals shape_destruct hev
  all_goals first
    | exact absurd ‹_› (hub _)
    | (simp [succ, word32] at hn; done)
    | (simp [succ, word32] at hn
       repeat' split at hn
       all_goals simp_all)

set_option maxHeartbeats 8000000 in
/-- **No event of a lane of the MMA warp is undefined behaviour.** -/
theorem mma_noUb (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X)
    (hg : g < L.threads) (h12 : Prologue.warpIndex L g = 12) {k : Nat} {e : Event}
    (he : X.get (g, k) = some e) (f : Fault) : e.kind ≠ .ub f := by
  have hReads := cuQReadsFromLaunch hp hX
  refine Frame.noUb_of_followed_sites (C := thread p L) (J := Ref p L) hX
    (fun k => good hp hX hReads hg h12 k) ?_ ?_ he f
  · intro k σ e he hσ hR f
    obtain ⟨σ, n⟩ := σ
    rcases σ with s | ⟨i, d⟩
    · exact start_safe hp hX he hσ hR.1 f
    cases i with
    | mma =>
      rcases d with s0 | ⟨⟨⟩, d⟩
      · obtain ⟨t, ins, o, hat, hinv, hc, hf⟩ :=
          strict_fired_site hp hX he hσ rfl
        exact pre_safe hp hat hinv.2 hc hf f
      · obtain ⟨-, hF⟩ := hR (ub_zero hX he hσ)
        exact role_safe hp hX hFw hg h12 he hσ hF f
    | _ => exact hR.elim
  · intro k σ e he hσ hR hub hn
    obtain ⟨σ, n⟩ := σ
    rcases σ with s | ⟨i, d⟩
    · exact start_live hp hX he hσ hR.1 hn
    cases i with
    | mma =>
      have hn' := role_next_none hn
      rcases d with s0 | ⟨⟨⟩, d⟩
      · obtain ⟨t, ins, o, hat, hinv, hc, hf⟩ :=
          strict_fired_site hp hX he hσ rfl
        exfalso
        cases s0 <;> simp [frag, M, G, Code.glue, S] at hn'
        exact absurd hinv.2 (by simp [Start.exit])
      · obtain ⟨hJ, hF⟩ := hR (ub_zero hX he hσ)
        have hs : succ p L g d e = none := by
          simpa [frag, M, G, Code.glue, code] using hn'
        exact role_live hp hX hFw hg h12 he hσ hJ hF hub hs
    | _ => exact hR.elim

end
end PTX.Kernels.TmlFa4Fwd.Proof.Mma
