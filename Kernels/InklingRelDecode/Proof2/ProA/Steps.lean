-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof2.ProA.Machine
public import Lemmas.Flow.Transfer
public import Lemmas.Flow.Kill
public import Kernels.InklingRelDecode.Proof.Thread.ProASound

@[expose] public section

/-! # The prologue's obligations

Every state other than the exit satisfies its step obligation: the last barrier by
`step_issue` into the exit, the third request word by its own proof (`stepAt_ld2`: the flat
machine stops there on words without `WordsOk`, this one follows them), every other site from
the flat machine's obligation at the flat site it regroups (`Code.stepAt_map` along `D.old`; the
successor equation holds because `Site.old` inverts `Site.ofOld`). -/

namespace PTX.Kernels.InklingRelDecode.Proof2.ProA
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.InklingRelDecode
open PTX.Kernels.InklingRelDecode.Proof.ProA (Dat Inh)

noncomputable section
set_option maxRecDepth 100000

variable {L : Launch} {g : Nat}

/-- The flat machine's program counter of the site a site regroups. -/
theorem pc_old (s : Site) (hx : s ≠ .exit) : s.pc = s.old.pc := by
  cases s with
  | ld k | el k | init k | arr k | psh k | ldq k | st9 k => fin_cases k <;> rfl
  | pb b j | lb b j | pel b j | ptc b j | stq b j => fin_cases b <;> fin_cases j <;> rfl
  | exit => exact absurd rfl hx
  | _ => rfl

theorem sub_old (s : Site) : s.sub = s.old.sub := by
  cases s with
  | ld k | el k | init k | arr k | psh k | ldq k | st9 k => fin_cases k <;> rfl
  | pb b j | lb b j | pel b j | ptc b j | stq b j => fin_cases b <;> fin_cases j <;> rfl
  | _ => rfl

theorem old_ofOld (s : OSite) : (Site.ofOld s).old = s := by cases s <;> rfl

theorem ofOld_ne_exit (s : OSite) : Site.ofOld s ≠ .exit := by cases s <;> nofun

/-- The successor equation away from the last barrier and the exit. -/
theorem next_old (dt : Dat) {s : Site} (h1 : s ≠ .bar18) (h2 : s ≠ .exit) (h3 : s ≠ .ld 2)
    (e : Event) :
    Proof.ProA.next L g ⟨s.old, dt⟩ e = (next0 L g ⟨s, dt⟩ e).map (Option.map D.old) := by
  have hid : (D.old ∘ fun d' : Proof.ProA.D => (⟨Site.ofOld d'.site, d'.dt⟩ : D)) = id := by
    funext d'; obtain ⟨s', dt'⟩ := d'; simp [D.old, old_ofOld]
  have key : next0 L g ⟨s, dt⟩ e = (Proof.ProA.next L g ⟨s.old, dt⟩ e).map
      (Option.map fun d' => ⟨Site.ofOld d'.site, d'.dt⟩) := by
    cases s with
    | ld k => fin_cases k <;> first | rfl | exact absurd rfl h3
    | _ => first | rfl | exact absurd rfl h1 | exact absurd rfl h2
  rw [key, Option.map_map, Option.map_comp_map, hid, Option.map_id, Option.map_id]
  rfl

open PTX.Kernels.InklingRelDecode.Proof.ProA in
/-- **The third request word.** The machine records any 32-bit word; the division of pc 59 that
reads it continues to the first election when it has a rule, and kills the thread otherwise. -/
theorem stepAt_ld2 (P : Inh) (dt : Dat) : (code0 L g P).StepAt ⟨.ld 2, dt⟩ := by
  have hflat := Proof.ProA.stepAt (L := L) (g := g) P ⟨.ldSk, dt⟩
  refine ⟨fun hi => hflat.site hi, ?_⟩
  intro t e u ins hat hi hc hf
  obtain ⟨a, ha1, ha2, ha3, ha4, ha5⟩ : ∃ a : MemAccess,
      kernel.code[41]? = some ⟨none, .mem a⟩ ∧ a.kind = .load ∧ a.nc = false ∧
      a.ext = .same ∧ a.regs = [612] :=
    ⟨_, Flow.code_41, rfl, rfl, rfl, rfl⟩
  obtain rfl := Option.some.inj (hc.symm.trans ha1)
  obtain ⟨r, bs, rfl, rfl⟩ := fires_load ha2 ha3 hf ha4
  have h : At t 41 (factsAt L g 41 dt) :=
    ⟨hat.1, hat.2.1, hat.2.2.1, hat.2.2.2.1, hat.2.2.2.2⟩
  rw [ha5]
  cases hv : rebuild 3 bs with
  | error f =>
    exact .inr ⟨by simp [next0, hv], Machine.dead_of_fault (f := f) (by simp [afterLoad, hv])⟩
  | ok v =>
    cases hw : word32 v with
    | none => exact .inl (.inl (by simp [next0, hv, hw]))
    | some x =>
      obtain ⟨hvx, hxl⟩ := word32_spec hw
      subst hvx
      have hU : At (afterLoad t [612] bs) 42 (factsAt L g 42 { dt with sk := x }) := by
        rw [afterLoad_ok h.2.1 h.2.2.1 hv]
        refine ⟨by show t.pc + 1 = 42; rw [h.1], rfl, rfl, h.2.2.2.1, ?_⟩
        have hframe : ∀ r, r ∉ [612] → (setRegs t [612] ([] ++ [b32 x])).regs r = t.regs r := by
          intro r hr
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          simp [setRegs, setReg, Function.update_of_ne hr]
        frame_fp h.2.2.2.2, hframe
        simp only [Flow.factsFrom, List.map_cons, List.map_nil]
        simp [setReg, valueOf, table, PTX.Flow.lookupLit, v_r151, b32]
      have hseg := ((SegD.of_seg (Seg.comp (seg_42_54 L g { dt with sk := x })
        (seg_54_59 L g { dt with sk := x })))).comp ((segD_59_60 L g { dt with sk := x }).comp
        (SegD.of_seg (Seg.comp (seg_60_72 L g { dt with sk := x }) (Seg.comp (seg_72_84 L g
        { dt with sk := x }) (Seg.comp (seg_84_96 L g { dt with sk := x }) (Seg.comp (seg_96_108
        L g { dt with sk := x }) (Seg.comp (seg_108_120 L g { dt with sk := x })
        (seg_120_130 L g { dt with sk := x }))))))))
      by_cases hd : div59 L g { dt with sk := x } = true
      · obtain ⟨t', hr, ht'⟩ := (hseg _ hU).1 ⟨trivial, hd, trivial⟩
        have hi' : Proof.ProA.Inv L g ⟨.el0, { dt with sk := x }⟩ :=
          Inv.mv hi _ _ rfl rfl (fun j _ => hi.qz j (Nat.zero_le _)) hi.qb
        exact .inl (.inr ⟨⟨.el 0, { dt with sk := x }⟩, t', by simp [next0, hv, hw, hd],
          run_rtg hr, ⟨ht'.1, ht'.2.1, ht'.2.2.1, ht'.2.2.2.1, ht'.2.2.2.2⟩, hi'⟩)
      · exact .inr ⟨by simp [next0, hv, hw, hd], (hseg _ hU).2 fun hc => hd hc.2.1⟩

theorem stepAt0 (P : Inh) (d : D) (hx : d.site ≠ .exit) : (code0 L g P).StepAt d := by
  obtain ⟨s, dt⟩ := d
  by_cases hl : s = .ld 2
  · subst hl; exact stepAt_ld2 P dt
  by_cases hb : s = .bar18
  · subst hb
    refine Code.StepAt.of (fun _ => ⟨_, Flow.code_573, rfl, trivial⟩) ?_
    exact Code.step_issue Flow.code_573 (by intro _ _ _; advances) (dn := ⟨.exit, dt⟩)
      (fun _ => rfl) rfl rfl ⟨fun _ => ⟨0, (Seg.refl _ _).weaken_end fun _ h =>
        holds_factsFrom_mono h (by show ∀ r ∈ Flow.live 574, r ∈ Flow.live 573; decide)⟩,
        rfl, rfl, id⟩
  · refine Code.stepAt_map (C := Proof.ProA.code L g P) (C' := code0 L g P) D.old (pc_old s hx)
      (by show Proof.ProA.factsAt L g s.pc dt = Proof.ProA.factsAt L g s.old.pc dt
          rw [pc_old s hx]) (sub_old s) rfl Iff.rfl ?_ (next_old dt hb hx hl)
      (Proof.ProA.stepAt P _)
    intro e d' h
    have hne : d'.site ≠ .exit := by
      have key : next0 L g ⟨s, dt⟩ e = (Proof.ProA.next L g ⟨s.old, dt⟩ e).map
          (Option.map fun d' => ⟨Site.ofOld d'.site, d'.dt⟩) := by
        cases s with
        | ld k => fin_cases k <;> first | rfl | exact absurd rfl hl
        | _ => first | rfl | exact absurd rfl hb | exact absurd rfl hx
      change next0 L g ⟨s, dt⟩ e = some (some d') at h
      rw [key] at h
      rcases ho : Proof.ProA.next L g ⟨s.old, dt⟩ e with _ | _ | d0 <;> rw [ho] at h <;>
        simp at h
      subst h; exact ofOld_ne_exit _
    exact ⟨id, pc_old _ hne, by
      show Proof.ProA.factsAt L g d'.site.pc d'.dt = Proof.ProA.factsAt L g d'.site.old.pc d'.dt
      rw [pc_old _ hne], sub_old _, rfl⟩

/-- The pcs of the prologue's loads. -/
def loadPcs : List Nat :=
  [34, 37, 41, 197, 220, 241, 262, 283, 304] ++ (List.range 64).map (fun k => 388 + 2 * k)

theorem loadPcs_plain : loadPcs.all
    (fun pc => (kernel.code[pc]?).any fun ins : Instr => plainLoad ins.op) = true := by
  decide +kernel

theorem load_pc {s : Site} (h : s.isLoad = true) : s.pc ∈ loadPcs := by
  cases s with
  | ld k => fin_cases k <;> decide
  | lb b j => fin_cases b <;> fin_cases j <;> decide
  | ldq k =>
    simp only [loadPcs, Site.pc, List.mem_append, List.mem_map, List.mem_range]
    exact .inr ⟨k.val, k.isLt, rfl⟩
  | _ => simp [Site.isLoad] at h

/-- **Every state other than the exit obeys its obligation**: `next0`'s, with the loads whose
bytes do not rebuild killing the thread. -/
theorem stepAt (P : Inh) (d : D) (hx : d.site ≠ .exit) : (code L g P).StepAt d :=
  Code.StepAt.kill (C := code0 L g P) (kill := kill) (stepAt0 P d hx)
    (fun {t e u} ins _ _ hc hf hk => by
      simp only [kill, Bool.and_eq_true] at hk
      obtain ⟨hl, hk⟩ := hk
      have hp := List.all_eq_true.mp loadPcs_plain _ (load_pc hl)
      change kernel.code[d.site.pc]? = some ins at hc
      rw [hc] at hp
      refine dead_of_load_error (by simpa using hp) hf fun a bs he => ?_
      rw [he] at hk
      simp only at hk
      split at hk
      · exact ⟨_, ‹_›⟩
      · cases hk)

end
end PTX.Kernels.InklingRelDecode.Proof2.ProA
