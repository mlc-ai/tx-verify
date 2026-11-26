-- SPDX-License-Identifier: Apache-2.0
module

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
public import Kernels.TmlFa4Fwd.Proof.LdWarp.Fits
public import Kernels.TmlFa4Fwd.Proof.LdWarp.Sim
public import Kernels.TmlFa4Fwd.Proof.Loader.Machine
public import Kernels.TmlFa4Fwd.Proof.Loader.Ref
public import Kernels.TmlFa4Fwd.Spec
public import Lemmas.Flow.Code
public import Lemmas.Kernel.Frame
public import Lemmas.Tcgen05.TcFence
import Kernels.TmlFa4Fwd.Flow.Code.Part002
import Kernels.TmlFa4Fwd.Flow.Code.Part003
import Kernels.TmlFa4Fwd.Flow.Code.Part027
import Kernels.TmlFa4Fwd.Flow.Code.Part028
import Kernels.TmlFa4Fwd.Proof.Lib.InputRead
import Kernels.TmlFa4Fwd.Proof.Common.NoUb
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Kernels.TmlFa4Fwd.Proof.Common.SharedSites
import Kernels.TmlFa4Fwd.Proof.Epilogue.NoUb
import Kernels.TmlFa4Fwd.Proof.Epilogue.Export.Safe
import Kernels.TmlFa4Fwd.Proof.LdWarp.Mem
import Kernels.TmlFa4Fwd.Proof.LdWarp.Page
import Kernels.TmlFa4Fwd.Proof.LdWarp.Src
import Kernels.TmlFa4Fwd.Proof.LdWarp.Warp
import Lemmas.Flow.MemAl
import Lemmas.Kernel.NoUbFollowedSites
import Kernels.TmlFa4Fwd.Proof.Loader.Safe
import Kernels.TmlFa4Fwd.Proof.Loader.SafeRd
import Kernels.TmlFa4Fwd.Proof.Loader.SafeSt
import Kernels.TmlFa4Fwd.Proof.Loader.Mem.AddrTrace
import Kernels.TmlFa4Fwd.Proof.Loader.Mem.CpOk
import Kernels.TmlFa4Fwd.Proof.Loader.Mem.CpPrime
import Kernels.TmlFa4Fwd.Proof.Loader.Mem.CpSteady
import Kernels.TmlFa4Fwd.Proof.Loader.Mem.CpWarm
import Kernels.TmlFa4Fwd.Proof.Loader.Mem.Tc
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # No event of the loader warps is undefined behaviour

`Frame.noUb_of_followed_sites` for the lanes of warps 14 and 15 (`ld_noUb`), followed with
`LdWarp.Ref` by `LdWarp.good`.

`safe`: the startup's fence path (`start_safe`), and per role site: the scheduler's reads at
4-aligned cuQ words (`word_safe`, the output warp's `rd_aligned`), the request reads
(`read_safe`), the page-table reads (`pg_safe`), the local stores (`lst_safe`), the elections
(`elect_safe`), the 192 row copies (`cp_safe_prime`, `cp_safe_warm`, `cp_safe_steady`, with the
row-address pattern of `ld_aok`) and the 14 tensor copies (`tc_safe`); no other site's shape
admits undefined behaviour.

`live`: a role state dies only at the exit: the scheduler's steps as the output warp's
(`Epilogue.next_none`, through `succ_scan` and `tiles_none`), the request reads and the used-K read
by their reference, the page-table reads by the launch's page table (`pg_rebuild`), the local
reads by the lane's stores (`local_rebuild`); every other site has a successor for every event of
its shape. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Loader
open PTX PTX.Proof PTX.Flow
open PTX.Flow.Arith32

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g w : Nat} {ent : Nat → Value}

set_option maxHeartbeats 4000000 in
/-- **The scheduler's reads are no undefined behaviour**: their cuQ words are 4-aligned. -/
theorem word_safe (hp : Pre p L m) {d : D} {ns nv nc : Nat} (hF : LFits p L g d ns nv nc)
    {t : TState} {ins : Instr} {e : Event} {o : Option TState}
    (h : (code p L g w ent).AtD d t) (hc : kernel.code[(code p L g w ent).pc d]? = some ins)
    (hf : Fires ((code p L g w ent).pc d) (eventTmpl Assumptions.all L g t ins.op) e o)
    (hs : ∃ k, d.site = .word k) (f : Fault) : e.kind ≠ .ub f := by
  replace hc : kernel.code[d.site.pc]? = some ins := hc
  obtain ⟨k, hs⟩ := hs
  have hsch : d.site.sched = true := by rw [hs]; rfl
  obtain ⟨-, hFE, -, -⟩ := sched_fits hsch hF
  have hal := Epilogue.rd_aligned hp hFE (.inl ⟨k, by simp only [toE, hs, Site.epi]⟩)
  obtain ⟨site, v, kk⟩ := d
  simp only at hs
  subst hs
  intro hk
  have hu := fires_ub hf hk
  cases k <;>
  · obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
    refine ldGlobal_ok' rfl rfl rfl rfl rfl rfl (by decide) (lreg h (by lit_mem) rfl) ?_ f hu
    exact hal

set_option maxHeartbeats 8000000 in
/-- **No event a role state of a loader lane fires under its reference values is undefined
behaviour.** -/
theorem role_safe (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hw14 : w = 14 ∨ w = 15) (hg : g < L.threads) (hw : Prologue.warpIndex L g = w) {k : Nat}
    {b : Bool} {d : D} {n : Cls → Nat} {e : Event} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (thread p L) X g k = some (some (LdWarp.linj p L g b d n)))
    (hF : LFits p L g d (n .shfl) (n .vote) (n (.load .commit)))
    (f : Fault) : e.kind ≠ .ub f := by
  obtain ⟨t, ins, o, hat, hinv, hc, hf⟩ :=
    strict_fired_site hp hX he hσ rfl
  have hev := (LdWarp.lfired hp hX he hσ).1
  have hA : AOk d.v := LdWarp.ld_aok hp hX hw14 hg hw he hσ
  obtain ⟨s, v, kk⟩ := d
  replace hat : (code p L g (wOf b) (ent p L)).AtD ⟨s, v, kk⟩ t := hat
  replace hc : kernel.code[(code p L g (wOf b) (ent p L)).pc ⟨s, v, kk⟩]? = some ins := hc
  replace hf : Fires ((code p L g (wOf b) (ent p L)).pc ⟨s, v, kk⟩)
    (eventTmpl Assumptions.all L g t ins.op) e o := hf
  replace hinv : kk = 0 ∨ s.midOk kk := hinv
  have hk0 : s.midOk kk = False → kk = 0 := fun h => by
    rcases hinv with h' | h'
    · exact h'
    · rw [h] at h'; exact h'.elim
  cases s
  case word kw => exact word_safe hp hF hat hc hf ⟨kw, rfl⟩ f
  case q0 => exact read_safe hp hF hat hc hf (.inl rfl) (hk0 rfl) f
  case q1 => exact read_safe hp hF hat hc hf (.inr (.inl rfl)) (hk0 rfl) f
  case uk => exact read_safe hp hF hat hc hf (.inr (.inr rfl)) (hk0 rfl) f
  case pgLd per it => exact LdWarp.pg_safe hp hF rfl (hk0 rfl) hat hc hf f
  case pgSt per it => exact lst_safe hp hat (hk0 rfl) hc hf (.inl ⟨per, it, rfl⟩) f
  case rwSt per it => exact lst_safe hp hat (hk0 rfl) hc hf (.inr (.inl ⟨per, it, rfl⟩)) f
  case ptS per bb it =>
    exact lst_safe hp hat (hk0 rfl) hc hf (.inr (.inr ⟨per, bb, it, rfl⟩)) f
  case te tt i => exact elect_safe hc hf (.inl ⟨tt, i, rfl⟩) f
  case de => exact elect_safe hc hf (.inr rfl) f
  case cp per bb i c =>
    cases per
    · exact cp_safe_prime hp hA hat hc hf f
    · exact cp_safe_warm hp hA hat hc hf f
    · exact cp_safe_steady hp hA hat hc hf f
  case tc tt c => exact tc_safe hp hg hat hc hf f
  all_goals
    intro hk'
    obtain ⟨pc, kind⟩ := e
    simp only at hk'
    subst hk'
    simp [Ev, Epilogue.Ev, Site.toE] at hev

/-- At the first pass's tile count the loader dies only where the output warp does: the two
coordinate divisions are the same terms. -/
theorem afterTiles_none {d : D} {x : BitVec 64} (h : afterTiles p L g d x = none) :
    Epilogue.afterTiles p L g (toE d) x = none := by
  unfold afterTiles at h
  unfold Epilogue.afterTiles
  dsimp only [scAt] at h ⊢
  exact afterTiles_none_of rfl rfl rfl rfl h

set_option maxHeartbeats 4000000 in
theorem tiles_none {d : D} {e : Event} (hs : d.site = .tiles false)
    (h : succ p L g w d e = none) : Epilogue.succ p L g (toE d) e = none := by
  obtain ⟨site, v, kk⟩ := d
  simp only at hs
  subst hs
  obtain ⟨pc, kind⟩ := e
  revert h
  cases kind <;> simp only [succ, Epilogue.succ, toE, Site.epi, reduceCtorEq, imp_self]
  rename_i md a b c r o
  cases r <;> (try simp only [reduceCtorEq, imp_self])
  rename_i wd x
  intro h
  split at h
  · rename_i heq0
    simp only [Value.bits.injEq] at heq0
    obtain ⟨rfl, rfl⟩ := heq0
    simp only [Bool.false_eq_true, ↓reduceIte, Option.map_eq_none_iff] at h ⊢
    exact afterTiles_none (d := ⟨.tiles false, v, kk⟩) h
  · cases h

set_option maxHeartbeats 8000000 in
/-- **A role state of a loader lane dies only at the exit** on an event that is no undefined
behaviour. -/
theorem role_live (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hw14 : w = 14 ∨ w = 15) (hg : g < L.threads) (hw : Prologue.warpIndex L g = w) {k : Nat}
    {b : Bool} {d : D} {n : Cls → Nat} {e : Event} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (thread p L) X g k = some (some (LdWarp.linj p L g b d n)))
    (hbw : wOf b = w) (hJ : Loader.Ref p L g w (d, LdWarp.lcn n))
    (hF : LFits p L g d (n .shfl) (n .vote) (n (.load .commit)))
    (hub : ∀ f, e.kind ≠ .ub f) (hn : succ p L g w d e = none) : e.kind = .exit := by
  have hReads := cuQReadsFromLaunch hp hX
  have hall : ∀ k, LdWarp.Good p L w X g k := LdWarp.good hp hX hw14 hg hw
  have hnb : ∀ j < k, ¬ Frame.Bad (thread p L) (LdWarp.Ref p L w) X (g, j) :=
    fun j _ => LdWarp.not_bad_of_good hall j
  have hE := (LdWarp.lexpect hp hX hReads hg hw he hσ hbw hJ hF (fun hce => by
    have := upTo_of_prev (fun _ => LdWarp.ref_init) he hce
      (fun j _ hjw => LdWarp.not_bad_of_good (LdWarp.good hp hX hw14 hjw.1 hjw.2) j.2)
    rwa [countColl ((X.tr g).take k), (counts hσ).1, (counts hσ).2] at this) hnb).1
  have hev0 := (LdWarp.lfired hp hX he hσ).1
  have hev : Ev p L g w d e := by rw [← hbw]; exact hev0
  by_cases hsc : d.site.scan = true
  · obtain ⟨-, hFE, -, -⟩ : 32 * n (.load .commit) ≤ n .shfl ∧
        Epilogue.Fits p L g (toE d) (n .shfl - 32 * n (.load .commit)) (n .vote) ∧ True ∧ True := by
      by_cases ht : d.site = .tiles false ∨ d.site = .tiles true
      · have hl : lc d.site = .p1 ∨ lc d.site = .p2 := by
          rcases ht with ht | ht <;> rw [ht] <;> simp [lc]
        obtain ⟨dE, hFE, hle, h1, -, -⟩ := lband hF (by rcases hl with h | h <;> simp [h])
        have := h1 (by rcases hl with h | h <;> rw [h] <;> simp)
        subst this
        exact ⟨hle, hFE, trivial, trivial⟩
      · have hsch : d.site.sched = true := by
          obtain ⟨s, v, kk⟩ := d
          cases s <;> simp_all [Site.scan, Site.sched]
        obtain ⟨h1, h2, -, -⟩ := sched_fits hsch hF
        exact ⟨h1, h2, trivial, trivial⟩
    have hE' : Epilogue.Expect p L g (toE d) (n .shfl - 32 * n (.load .commit)) e := by
      obtain ⟨s, v, kk⟩ := d
      obtain ⟨pc, kind⟩ := e
      cases s <;> simp only [Site.scan, Bool.false_eq_true] at hsc <;>
        simp only [LExpect] at hE <;> exact hE (by simp [Site.scan])
    by_cases ht : d.site = .tiles true
    · exfalso
      obtain ⟨s, v, kk⟩ := d
      simp only at ht
      subst ht
      obtain ⟨pc, kind⟩ := e
      simp only [Ev, Epilogue.Ev, Site.toE] at hev
      obtain ⟨r, ok, hk⟩ := hev
      subst hk
      simp only [succ] at hn
      split at hn <;> simp at hn
    refine Epilogue.next_none hp hg hFE hE' (LdWarp.ev_toE hsc hev) hub ?_
    show Epilogue.succ p L g (toE d) e = none
    by_cases ht' : d.site = .tiles false
    · exact tiles_none ht' hn
    · have hs' : d.site.sched = true := by
        obtain ⟨s, v, kk⟩ := d
        cases s <;> simp only [Site.scan, Bool.false_eq_true] at hsc <;> first
          | rfl | (rename_i l; cases l <;> first | rfl | exact absurd rfl ht | exact absurd rfl ht')
      rw [succ_scan hs'] at hn
      simpa using hn
  obtain ⟨s, v, kk⟩ := d
  obtain ⟨pc, kind⟩ := e
  cases s
  case exit => simpa [Ev] using hev
  case q0 | q1 =>
    all_goals simp only [Ev] at hev
    all_goals rcases hev with ⟨bs, hk⟩ | ⟨f, hk⟩
    all_goals try exact absurd hk (hub f)
    all_goals subst hk
    all_goals simp only [LExpect, Site.sched, Bool.true_or, Epilogue.Expect, toE,
      Site.epi, forall_const] at hE
    all_goals simp [succ, hE, word32] at hn
  case uk =>
    simp only [Ev] at hev
    rcases hev with ⟨bs, hk⟩ | ⟨f, hk⟩
    · subst hk
      simp only [LExpect] at hE
      simp [succ, hE, word32] at hn
    · exact absurd hk (hub f)
  case pgLd per it =>
    simp only [Ev] at hev
    rcases hev with ⟨bs, hk⟩ | ⟨f, hk⟩
    · subst hk
      obtain ⟨x, hx⟩ := LdWarp.pg_rebuild hp hX he hσ hF rfl _ bs rfl
      simp [succ, hx, word32] at hn
    · exact absurd hk (hub f)
  case ptP per bb it | ptR per bb it | lw per bb h =>
    all_goals
      subst hbw
      obtain ⟨a, bs, x, hk, hx⟩ := LdWarp.local_rebuild hp hX he hσ hJ hnb rfl
      simp only at hk
      subst hk
      simp only [succ, hx, word32] at hn
      first | cases hn | (split at hn <;> cases hn)
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
/-- **No event of a lane of the loader warps is undefined behaviour.** -/
theorem ld_noUb (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hg : g < L.threads) (hw14 : Prologue.warpIndex L g = 14 ∨ Prologue.warpIndex L g = 15)
    {k : Nat} {e : Event} (he : X.get (g, k) = some e) (f : Fault) : e.kind ≠ .ub f := by
  set w := Prologue.warpIndex L g with hw
  refine Frame.noUb_of_followed_sites (C := thread p L) (J := LdWarp.Ref p L w)
    hX (fun k => LdWarp.good hp hX hw14 hg hw.symm k) ?_ ?_ he f
  · intro k σ e he hσ hR f
    obtain ⟨σ, n⟩ := σ
    rcases σ with s | ⟨i, d⟩
    · exact start_safe hp hX he hσ hR.1 f
    cases i with
    | loader b =>
      obtain ⟨-, hR'⟩ := hR
      obtain ⟨-, hF⟩ := hR' (ub_zero hX he hσ)
      exact role_safe hp hX hw14 hg hw.symm he hσ hF f
    | _ => exact hR.elim
  · intro k σ e he hσ hR hub hn
    obtain ⟨σ, n⟩ := σ
    rcases σ with s | ⟨i, d⟩
    · exact start_live hp hX he hσ hR.1 hn
    cases i with
    | loader b =>
      have hn' := role_next_none hn
      obtain ⟨hbw, hR'⟩ := hR
      obtain ⟨hJ, hF⟩ := hR' (ub_zero hX he hσ)
      have hs : succ p L g w d e = none := by
        rw [← hbw]; simpa [frag, Loader.F, code] using hn'
      exact role_live hp hX hw14 hg hw.symm he hσ hbw hJ hF hub hs
    | _ => exact hR.elim

end
end PTX.Kernels.TmlFa4Fwd.Proof.Loader
