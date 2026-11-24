-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof2.Safety.ProShfl
public import Lemmas.Flow.PollMeet
public import Lemmas.Flow.ElectMask

@[expose] public section

/-! # The loader's elections, counted by iteration

The loader's loop makes four elections per iteration (`el0` … `el3`, one per pair of copies),
whatever lane they return; the startup and the dispatch make none. So at a loader state of
iteration `i` in the loop the thread's elections are `4 (i - num_pre)` plus the iteration's
elections before the site (`elDoneS`). The elections are at the positions `elPcs`
(`kernel_el_pcs`); no startup or dispatch site is one of them.

* `LE`, `le_step`: the count at a loader state, kept by every loader step;
* `EL`, `el_inv`: along every thread, no election before a role and the loader's count in it. -/

namespace PTX.Kernels.InklingRelDecode.Proof2
open PTX PTX.Proof PTX.Flow PTX.Frame

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-! ### The election positions -/

def elPcs : List Nat :=
  [130, 135, 139, 143, 147, 151, 155, 159, 163, 167, 171, 175, 203, 213, 223, 228, 245, 255, 265,
    270, 287, 297, 307, 312, 2388, 2393, 2403, 2409, 2477, 2525, 2551]

theorem kernel_el_pcs : OpPcsFast kernel.code electOp elPcs = true := by decide +kernel

theorem elect_pc {t : TState} {pc : Nat} {ins : Instr} {e : Event} {o : Option TState}
    (hc : kernel.code[pc]? = some ins) (hf : Fires pc (eventTmpl Assumptions.all L g t ins.op) e o)
    (he : isElectEv e = true) : pc ∈ elPcs := by
  refine OpPcsFast.mem kernel_el_pcs hc ?_
  cases hop : electOp ins.op
  · obtain ⟨pc', k⟩ := e
    cases k <;> simp [isElectEv] at he
    exact absurd rfl (fires_notElect (eventTmpl_notElect hop) hf _ _ _)
  · rfl

local macro "site_none" : tactic =>
  `(tactic| (intro s h; revert h; cases s <;> (try (rename_i j; revert j)) <;> decide +kernel))

theorem startup_el : ∀ s : Startup.Site, s.pc ∈ elPcs → False := by
  intro s h; revert h
  cases s with
  | enter r => cases r <;> decide
  | _ => decide

theorem worker_el : ∀ s : Proof.Worker.Site, s.pc ∈ elPcs → False := by site_none

/-- The thread's elections among the events `es`. -/
abbrev electN (es : List Event) : Nat := es.countP isElectEv

/-! ### The loader -/

/-- The iteration's elections before a loop site. -/
def elDoneS : Proof.Loader.Site → Nat
  | .cp0a | .cp0b | .wb2 | .el1 => 1
  | .cp1a | .cp1b | .ldb1 | .wb3 | .el2 => 2
  | .cp2a | .cp2b | .wb4 | .el3 => 3
  | .cp3a | .cp3b => 4
  | _ => 0

/-- **The loader's elections at state `d`**: none before the loop, `4 (i - num_pre)` plus the
iteration's before the site in it. -/
structure LE (Q : Params) (L : Launch) (g : Nat) (d : Proof.Loader.D) (es : List Event) :
    Prop where
  pre : d.site.inLoop = false → d.site ≠ .bar1 → d.site ≠ .setMaxInc → electN es = 0
  loop : d.site.inLoop = true → electN es = 4 * (d.i - npOf Q L g) + elDoneS d.site

theorem electN_snoc (es : List Event) (e : Event) :
    electN (es ++ [e]) = electN es + if isElectEv e then 1 else 0 := by
  simp only [electN, List.countP_append, List.countP_singleton]

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
set_option linter.unusedSimpArgs false in
/-- **One step of the loader keeps its elections.** -/
theorem le_step {d d' : Proof.Loader.D} {e : Event} {es : List Event}
    (hR : LE Q L g d es) (hK : LdCnt Q L g d es) (hsh : Proof.EvW.LdShape Q L g d e)
    (hn : Proof.Loader.next L g d e = some (some d')) :
    LE Q L g d' (es ++ [e]) := by
  obtain ⟨site, pro, i, n, p0, p1, ln⟩ := d
  have hpre := hR.pre
  have hloop := hR.loop
  have hlo := hK.lo
  have hi0 := hK.i0
  simp only at hpre hloop hlo hi0
  cases site
  all_goals simp only [Proof.EvW.LdShape] at hsh
  all_goals first
    | (obtain ⟨b, hb, rfl⟩ := hsh)
    | (obtain ⟨inst, ld, rfl⟩ := hsh)
    | (obtain ⟨ac, bs, rfl, -⟩ := hsh)
    | (obtain ⟨ok, rfl⟩ := hsh)
    | (obtain ⟨inst, rfl⟩ := hsh)
    | subst hsh
    | skip
  all_goals simp only [Proof.Loader.next, Proof.Loader.afterIter, Proof.Loader.readI,
    Proof.Loader.readN] at hn
  all_goals (repeat' split at hn)
  all_goals first
    | (cases hn; done)
    | (simp only [Option.some.injEq] at hn
       subst hn
       constructor <;> intro h1 <;> (try intro h2 h3) <;>
         simp_all [electN_snoc, isElectEv, elDoneS, Proof.Loader.Site.inLoop] <;> omega)

/-! ### Along a thread -/

/-- **The elections along a thread**: none in the startup and the dispatch before any role, the
loader's count in its role. -/
def EL (Q : Params) (L : Launch) (g : Nat) : (thread Q L g).D → List Event → Prop
  | (.inl _, _), es => electN es = 0
  | (.inr ⟨.inl (.worker _), .worker _⟩, _), es =>
    es.countP (Execution.isBarId 1) ≤ 1 → electN es = 0
  | (.inr ⟨.inl (.worker _), .loader d _⟩, _), es => LE Q L g d es
  | _, _ => True

set_option maxHeartbeats 400000 in
/-- **The elections along every thread.** -/
theorem el_inv (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hg : g < L.threads) :
    ∀ k, k < (X.tr g).length → ∀ σ, Frame.stateAt (thread Q L) X g k = some (some σ) →
      EL Q L g σ ((X.tr g).take k) := by
  have hb : L.block = 256 := hp.block
  intro k
  induction k with
  | zero =>
    intro _ σ hσ
    rw [Frame.stateAt_zero, thread_init_eq] at hσ
    obtain rfl := Option.some.inj (Option.some.inj hσ)
    rfl
  | succ k ih =>
    intro hk σ' hσ'
    have hlt : k < (X.tr g).length := by omega
    obtain ⟨e, he⟩ : ∃ e, (X.tr g)[k]? = some e := ⟨_, List.getElem?_eq_getElem hlt⟩
    have hσ'0 := hσ'
    rw [Frame.stateAt_succ he] at hσ'
    have hF := good_all' hp hX hg k
    have htake : (X.tr g).take (k + 1) = (X.tr g).take k ++ [e] := by
      rw [List.take_add_one, he, Option.toList_some]
    rcases hk0 : Frame.stateAt (thread Q L) X g k with _ | _ | σ
    · rw [hk0] at hσ'; cases hσ'
    · exact absurd hk0 hF.1
    · rw [hk0] at hσ'
      have hn : (thread Q L g).next σ e = some (some σ') := hσ'
      have hR0 := ih hlt σ hk0
      obtain ⟨t, ins, o, hat, hi, hc, hf⟩ :=
        Frame.fired_site (fun g hg => thread_sound hp hg) hX he hk0
      have hnE : ¬ Ends e := not_ends_of_lt hX hg he hk
      have hget : X.get (g, k) = some e := he
      have hno : (thread Q L g).pc σ ∉ elPcs → isElectEv e = false := by
        intro hpc
        cases hq : isElectEv e
        · rfl
        · exact absurd (elect_pc hc hf hq) hpc
      have hc1 := countP_take_mono (Execution.isBarId 1) (X.tr g) (show k ≤ k + 1 by omega)
      rw [htake] at hc1 ⊢
      obtain ⟨x, n⟩ := σ
      rcases x with st | ⟨_ | r, d⟩
      · -- the startup
        have he0 : isElectEv e = false := hno (fun h => startup_el st.site h)
        have h0 : electN ((X.tr g).take k ++ [e]) = 0 := by
          rw [electN_snoc, show electN ((X.tr g).take k) = 0 from hR0, he0]; rfl
        rw [next_start] at hn
        obtain ⟨s', -, rfl⟩ := mm_some hn
        simp only [Code.enter]
        split
        · rename_i j _
          rcases j with (_ | _) | _
          · trivial
          · intro _; exact h0
          · trivial
        · exact h0
      · rename_i i
        obtain ⟨d', hd'⟩ := next_same_role hn
        obtain ⟨x', n'⟩ := σ'
        simp only at hd'
        subst hd'
        cases i with
        | dp tm bw => trivial
        | worker w =>
          rw [next_worker] at hn
          obtain ⟨σw', hσw, he'⟩ := mm_some hn
          simp only [Prod.mk.injEq, Sum.inr.injEq, heq_eq_eq, Sigma.mk.injEq, true_and] at he'
          obtain ⟨he1, -⟩ := he'
          subst he1
          have hkk : k + 1 < (X.tr g).length := hk
          cases d with
          | worker ww =>
            have he0 : isElectEv e = false := hno (fun h => worker_el ww.site h)
            have hR0' : _ ≤ 1 → electN _ = 0 := hR0
            have h0 : ((X.tr g).take k).countP (Execution.isBarId 1) ≤ 1 →
                electN ((X.tr g).take k ++ [e]) = 0 := by
              intro h1; rw [electN_snoc, hR0' h1, he0]; rfl
            cases σw' with
            | worker w' => exact fun h1 => h0 (by omega)
            | loader d' P' =>
              have hs := (w_next_loader hσw).resolve_right (by
                rintro ⟨_, h, -⟩; cases h)
              have hrc := role_count hp hX hg hk rfl hσ'0
              simp only [wph, ldPh, hs] at hrc
              rw [htake] at hrc
              refine ⟨fun _ _ _ => h0 (by simp at hrc; omega), fun h => ?_⟩
              rw [hs] at h; cases h
            | _ => trivial
          | loader d P =>
            rcases role_succ (σ := .loader d P) rfl hσw with ⟨-, hph⟩ | ⟨P', rfl⟩
            · have hs : d.site ≠ .setMaxInc := by intro h; simp [wph, ldPh, h] at hph
              rw [Proof.EvW.next_loader_map P hs] at hσw
              obtain ⟨d', hld, he2⟩ := Proof.EvW.map_map_some hσw
              subst he2
              have hR0' : LE Q L g d ((X.tr g).take k) := hR0
              have hK : LdCnt Q L g d ((X.tr g).take k) := kc_inv hp hX hg k hlt _ hk0
              exact le_step hR0' hK (ld_shape hp hX hget hnE hk0) hld
            · intro _
              exfalso
              have := loop_c1 hp hX hg hk rfl hk0 hσ'0
              rw [htake] at this
              omega
          | mma d P =>
            rcases role_succ (σ := .mma d P) rfl hσw with ⟨-, hph⟩ | ⟨P', rfl⟩
            · have hs : d.site ≠ .setMaxRegInc := by intro h; simp [wph, mmPh, h] at hph
              rw [Proof.EvW.next_mma_map P hs] at hσw
              obtain ⟨d', -, he2⟩ := Proof.EvW.map_map_some hσw
              subst he2
              trivial
            · intro _
              exfalso
              have := loop_c1 hp hX hg hk rfl hk0 hσ'0
              rw [htake] at this
              omega
          | idle d =>
            rcases role_succ (σ := .idle d) rfl hσw with ⟨-, hph⟩ | ⟨P', rfl⟩
            · have hs : d.site ≠ .inc := by intro h; simp [wph, idPh, h] at hph
              rw [Proof.EvW.next_idle_map hs] at hσw
              obtain ⟨a, -, he2⟩ := Proof.EvW.map_map_some hσw
              subst he2
              trivial
            · intro _
              exfalso
              have := loop_c1 hp hX hg hk rfl hk0 hσ'0
              rw [htake] at this
              omega
          | exit x =>
            obtain ⟨x', rfl⟩ := exit_succ hσw
            trivial
      · exact hF.2 _ hk0 |>.elim

end
end PTX.Kernels.InklingRelDecode.Proof2
