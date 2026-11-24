-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.LkMachine
public import Kernels.InklingRelDecode.Proof.Interface.ShapeTrace
public import Kernels.InklingRelDecode.Proof.Protocol.MbarWords
public import Kernels.InklingRelDecode.Proof.Interface.ShapeWords

@[expose] public section

/-!
# Warp lockstep: the prologue's guards

The three guards that steer the prologue (`ProA.v_p53`, `v_p63`, `v_p72`) are functions of one
register, `%r31 = min (num_old, num_iters)`, which depends on the thread's `num_splits`, its
`ctaid.x` and the three request words `cu_seqlens_q[req]`, `cu_seqlens_q[req + 1]`, `seq_lens[req]`.
Two lanes of a warp have the same `num_splits` and `ctaid.x`, and at one site the same request
words: before the loads (the first site, `setmaxnreg.inc`) they are the zeros of the first state;
after the loads they are the request's (`WordsSo`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface.Lk
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.InklingRelDecode.Proof.Lk (ProAgree proSy syAt)
open PTX.Kernels.InklingRelDecode.Proof.Mbar (wordsSo_all)

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-- The register `%r31` depends on the thread only through its CTA's `ctaid.x` and the four
numbers `num_splits` and the request words. -/
theorem r31_congr {h : Nat} {dt dt' : ProA.Dat} (hx : ProA.cta L g .x = ProA.cta L h .x)
    (h1 : dt.pro.w71 = dt'.pro.w71) (h2 : dt.sk = dt'.sk) (h3 : dt.cu0 = dt'.cu0)
    (h4 : dt.cu1 = dt'.cu1) : ProA.v_r31 L g dt = ProA.v_r31 L h dt' := by
  have hc : ProA.wCta L g Dim.x = ProA.wCta L h Dim.x := by
    simp only [ProA.wCta]
    have := hx
    simp only [ProA.cta] at this
    rw [this]
  simp only [ProA.v_r31, ProA.v_r219, ProA.v_r218, ProA.v_r217, ProA.v_r175, ProA.v_r174,
    ProA.v_r17, ProA.v_r71, ProA.v_r23, ProA.v_r168, ProA.v_r167, ProA.v_r166, ProA.v_r21,
    ProA.v_r20, ProA.v_r149, ProA.v_r150, ProA.v_r151, ProA.v_r26, ProA.v_r25, ProA.v_r176,
    ProA.v_r173, ProA.v_r172, ProA.v_r171, ProA.v_r170, ProA.v_r169, hc, h1, h2, h3, h4]

/-- **The guards agree when `%r31` does.** -/
theorem guards_of_r31 {h : Nat} {dt dt' : ProA.Dat}
    (h31 : ProA.v_r31 L g dt = ProA.v_r31 L h dt') :
    ProA.v_p53 L g dt = ProA.v_p53 L h dt' ∧ ProA.v_p63 L g dt = ProA.v_p63 L h dt' ∧
      ProA.v_p72 L g dt = ProA.v_p72 L h dt' := by
  simp only [ProA.v_p53, ProA.v_p63, ProA.v_p72, h31, and_self]

/-- The synchronizing sites of the prologue are the first one and the sites after the loads. -/
theorem proSy_site {d : ProA.D} (h : proSy d = true) : d.site = .sMax ∨ d.site.afterSk = true := by
  obtain ⟨s, dt⟩ := d
  simp only [proSy] at h ⊢
  revert h
  cases s <;> first
    | (intro _; left; rfl)
    | (intro _; right; rfl)
    | (intro h; exfalso; revert h; decide +kernel)

/-- The request words of the first state are zero. -/
def SMaxZ : TSt → Prop
  | .d (.pro d) => d.site = .sMax → d.dt.cu0 = 0 ∧ d.dt.cu1 = 0 ∧ d.dt.sk = 0
  | _ => True

theorem smaxz_step {s s' : TSt} {e : Event} (hn : (threadCode L g Q).next s e = some (some s'))
    (hi : SMaxZ s) : SMaxZ s' := by
  cases s with
  | w s0 =>
    rw [next_w] at hn
    obtain ⟨a, -, rfl⟩ := map_map_eq_some_some hn
    trivial
  | d s0 =>
    rw [next_d] at hn
    obtain ⟨a, ha, rfl⟩ := map_map_eq_some_some hn
    cases a with
    | pro d' =>
      show d'.site = .sMax → d'.dt.cu0 = 0 ∧ d'.dt.cu1 = 0 ∧ d'.dt.sk = 0
      intro hs
      cases s0 with
      | dstart d0 =>
        simp only [DComp.next, DComp.dstartNext] at ha
        obtain ⟨b, -, hb⟩ := map_map_eq_some_some ha
        split at hb
        · simp only [DComp.St.pro.injEq] at hb
          subst hb
          simp [ProA.D.start, ProA.Dat.start]
        · cases hb
      | pro d0 =>
        simp only [DComp.next, DComp.proNext] at ha
        split at ha
        · split at ha
          · cases ha
          · cases ha
        · obtain ⟨b, hb, hb'⟩ := map_map_eq_some_some ha
          simp only [DComp.St.pro.injEq] at hb'
          subst hb'
          exact absurd hs (Ledger.pro_next_ne hb)
      | sm d0 =>
        exfalso
        simp only [DComp.next, DComp.smNext] at ha
        split at ha
        · simp only [DComp.exitNext] at ha
          split at ha <;> simp_all
        · obtain ⟨b, hb, hb'⟩ := map_map_eq_some_some ha
          cases hb'
      | epi d0 =>
        exfalso
        simp only [DComp.next] at ha
        obtain ⟨b, hb, hb'⟩ := map_map_eq_some_some ha
        cases hb'
    | _ => trivial

theorem smaxz_inv :
    ∀ (k : Nat) (s : TSt), St Q L X g k = some (some s) → SMaxZ s := by
  refine stateAt_induction SMaxZ ?_ ?_
  · show SMaxZ (if g % L.block < 128 then .d (DComp.code L g Q).init
      else .w (WComp.code L g Q).init)
    split <;> trivial
  · intro k e s s' _ _ hi hnx
    exact smaxz_step hnx hi

/-- **Two lanes of a warp at synchronizing states of the prologue, at one site, agree on the
guards.** -/
theorem proAgree_of (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) {h a b : Nat} {d d' : ProA.D} (hw : SameWarp L g h)
    (hsa : St Q L X g a = some (some (.d (.pro d))))
    (hsb : St Q L X h b = some (some (.d (.pro d'))))
    (hsy : proSy d = true) (hsite : d.site = d'.site) : ProAgree L g h d d' := by
  have hg : g < L.threads := hw.1.1
  have hh : h < L.threads := hw.1.2.1
  have hc : g / L.block = h / L.block := hw.1.2.2
  obtain ⟨-, tm, -, hpro⟩ := hf.reach hg hsa
  obtain ⟨-, tm', -, hpro'⟩ := hf.reach hh hsb
  have hw1 : d.dt.pro.w71 = d'.dt.pro.w71 := by
    rw [hpro, hpro', DStart.inh_w71 hpre, DStart.inh_w71 hpre]
  have hx : ProA.cta L g .x = ProA.cta L h .x := ProA.cta_eq_of_block hc .x
  have hz : ProA.cta L g .z = ProA.cta L h .z := ProA.cta_eq_of_block hc .z
  refine guards_of_r31 (r31_congr hx hw1 ?_ ?_ ?_)
  all_goals
    rcases proSy_site hsy with hs | hs
    · have hs' : d'.site = .sMax := by rw [← hsite]; exact hs
      obtain ⟨z1, z2, z3⟩ := smaxz_inv a _ hsa hs
      obtain ⟨z1', z2', z3'⟩ := smaxz_inv b _ hsb hs'
      first | (rw [z3, z3']) | (rw [z1, z1']) | (rw [z2, z2'])
    · have hs' : d'.site.afterSk = true := by rw [← hsite]; exact hs
      obtain ⟨w0, w1, w2⟩ := wordsSo_all hpre hX hf a _ hsa
      obtain ⟨w0', w1', w2'⟩ := wordsSo_all hpre hX hf b _ hsb
      have hne : d.site ≠ .sMax ∧ d.site ≠ .ldCu0 := by
        constructor <;> (intro h'; rw [h'] at hs; simp [ProA.Site.afterSk] at hs)
      have hne' : d'.site ≠ .sMax ∧ d'.site ≠ .ldCu0 := by
        constructor <;> (intro h'; rw [h'] at hs'; simp [ProA.Site.afterSk] at hs')
      first
        | (rw [w2 hs, w2' hs', hz])
        | (rw [w1 (Or.inl hs), w1' (Or.inl hs'), hz])
        | (rw [w0 hne.1 hne.2, w0' hne'.1 hne'.2, hz])

end
end PTX.Kernels.InklingRelDecode.Proof.Interface.Lk
