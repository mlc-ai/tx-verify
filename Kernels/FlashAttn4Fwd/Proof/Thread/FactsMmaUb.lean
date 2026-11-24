-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.MmaCountsSite
public import Kernels.FlashAttn4Fwd.Proof.Thread.Machine
public import Lemmas.Flow.TmplOkSync
public import Lemmas.Flow.TmplOkOff

@[expose] public section

/-! # The MMA warp's sites are not undefined behaviour

At every site of the MMA warp, the instruction's event is not undefined behaviour
(`Mma.tmpl_ok`, the MMA warp's part of `Cross.SitesTmplOk`):

* the polls, the commits, the hand-off arrival and the MMAs fire the event of their site
  (`site_event`), which is no undefined behaviour;
* the register request, the relinquishment and the return are plain (`plainOk_tmpl`);
* the elections have the immediate full mask (`elect_imm_ok`) and the broadcasts shuffle a
  32-bit register with the full mask (`shfl_imm_ok`);
* the two `bar.sync 2, 416` are barrier events (`fires_barSyncN_imm`);
* the allocation and the read-back address the base word of the thread's CTA, a 4-aligned shared
  word (`tcAlloc_off_ok`, `ld_off_ok`);
* the deallocation reads 512 columns and the carried address, which has a bit pattern there
  (`tcDealloc_regBits_ok`; the machine's `BaseOk`, part of its state invariant). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Mma
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

/-- An event site's event is no undefined behaviour. -/
theorem ev_ok (hpre : Pre P L mem0) (hg : g < L.threads) {d : D} {t : TState} {ins : Instr}
    (h : Holds t.regs (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hn : ∀ f, ¬ Ev L g d ⟨d.site.pc, .ub f⟩) (f : Fault) :
    eventTmpl asms L g t ins.op ≠ .ub f :=
  not_ub_of_fires (fun f hf => hn f (site_event hpre hg h hc hf)) f

set_option maxHeartbeats 1000000 in
/-- **No site of the MMA warp has an undefined-behaviour template**, at a state whose carried
address has a bit pattern at the deallocation (`BaseOk`). -/
theorem tmpl_ok (hpre : Pre P L mem0) (hg : g < L.threads) {d : D} {t : TState} {ins : Instr}
    (hs : t.sub = d.site.sub) (h : Holds t.regs (facts L g d))
    (hbase : BaseOk d) (hc : kernel.code[d.site.pc]? = some ins) (f : Fault) :
    eventTmpl asms L g t ins.op ≠ .ub f :=
    by
  have hb : L.block % 32 = 0 := by rw [hpre.block]
  have hsb := sb_bounds hpre
  obtain ⟨site, i, tt, base, pro⟩ := d
  cases site with
  | qWait k => exact ev_ok hpre hg h hc (fun f => by simp [Ev]) f
  | kvWait k => exact ev_ok hpre hg h hc (fun f => by simp [Ev]) f
  | pWait k => exact ev_ok hpre hg h hc (fun f => by simp [Ev]) f
  | p2Wait k lead => exact ev_ok hpre hg h hc (fun f => by simp [Ev]) f
  | waitDealloc => exact ev_ok hpre hg h hc (fun f => by simp [Ev]) f
  | arrivePeer => exact ev_ok hpre hg h hc (fun f => by simp [Ev]) f
  | commit c => exact ev_ok hpre hg h hc (fun f => by simp [Ev]) f
  | mma b j => exact ev_ok hpre hg h hc (fun f => by simp [Ev, isMma]) f
  | setMaxReg =>
    code_at hc
    subst hc
    exact plainOk_tmpl hb (by decide) f
  | relinquish =>
    code_at hc
    subst hc
    exact plainOk_tmpl hb rfl f
  | exit =>
    code_at hc
    subst hc
    exact plainOk_tmpl hb rfl f
  | elM b => fin_cases b <;> code_at hc <;> subst hc <;> exact elect_imm_ok f
  | elC c => fin_cases c <;> code_at hc <;> subst hc <;> exact elect_imm_ok f
  | shflQ =>
    code_at hc
    subst hc
    exact shfl_imm_ok (p := none) (.inr rfl) hb (reg_of h (by table_decide) (by mma_values; rfl)) f
  | shfl k =>
    fin_cases k <;> code_at hc <;> subst hc <;>
      exact shfl_imm_ok (p := none) (.inr rfl) hb
        (reg_of h (by table_decide) (by mma_values; rfl)) f
  | bar0 =>
    code_at hc
    subst hc
    refine not_ub_of_fires (pc := 0) (fun f hf => ?_) f
    have he := fires_barSyncN_imm (id := 2) (n := 416) (by omega) (by omega) (by omega)
      (by omega) (by rw [hpre.block]; omega) hf
    cases he
  | bar1 =>
    code_at hc
    subst hc
    refine not_ub_of_fires (pc := 0) (fun f hf => ?_) f
    have he := fires_barSyncN_imm (id := 2) (n := 416) (by omega) (by omega) (by omega)
      (by omega) (by rw [hpre.block]; omega) hf
    cases he
  | alloc =>
    code_at hc
    subst hc
    exact tcAlloc_off_ok (off := 328) hb
      (reg_of h (r := 337) (v := b32 L.sharedBase) (by table_decide) (by mma_values))
      (by omega) (by omega)
      (reg_of h (r := 861) (by table_decide) (by mma_values)) f
  | allocWrite =>
    code_at hc
    subst hc
    exact tcAlloc_off_ok (off := 328) hb
      (reg_of h (r := 337) (v := b32 L.sharedBase) (by table_decide) (by mma_values))
      (by omega) (by omega)
      (reg_of h (r := 861) (by table_decide) (by mma_values)) f
  | ldBase =>
    code_at hc
    subst hc
    exact ld_off_ok (off := 328) (reg_of h (r := 337) (v := b32 L.sharedBase) (by table_decide)
      (by mma_values)) (by omega) (by omega) hs f
  | dealloc =>
    code_at hc
    subst hc
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (hbase rfl)
    exact tcDealloc_regBits_ok hb (reg_of h (r := 379) (v := base) (by table_decide)
      (by mma_values)) hx (reg_of h (r := 960) (by table_decide) (by mma_values)) f

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Mma

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow

/-- **The MMA warp's part of `Cross.SitesTmplOk`**: at an MMA state of the composed machine,
the site's instruction has no undefined-behaviour template. -/
theorem Cross.SitesTmplOk_mma {P : Params} {L : Launch} {mem0 : Mem0} (hpre : Pre P L mem0)
    {g : Nat} (hg : g < L.threads) (d : Mma.D) (t : TState) (ins : Instr)
    (hat : (code L g).AtD (.inr (.mma d)) t) (hi : (code L g).inv (.inr (.mma d)))
    (hc : kernel.code[(code L g).pc (.inr (.mma d))]? = some ins) (f : Fault) :
    eventTmpl asms L g t ins.op ≠ .ub f :=
  Mma.tmpl_ok hpre hg hat.2.1 hat.2.2.2.2 hi.2 hc f

end PTX.Kernels.FlashAttn4Fwd.Proof
