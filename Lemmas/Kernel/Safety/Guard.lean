-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.WarpUniformAt

@[expose] public section

/-! # Uniform guards from group-uniform values

A proof tool, generic over the kernel, for the positions of ERR-NONUNIFORM-GUARD
(`WarpDivergent`) that are not poll branches. `Lemmas/Flow/WarpUniformAt.lean` splits
`WarpDivergent` into the poll branches (the poll arguments) and the positions `U` of the kernel's
choice (`¬ WarpDivergentAt U`). Here `¬ WarpDivergentAt U` follows from **group-uniform values**:
at every record of a walk of a launched thread at a position of `U`, the guard's value (when the
record has one) is `G pc g` and the index of a `brx.idx.uni` (when it has one) is `I pc g`, and
`G pc`, `I pc` agree on two threads of one uniform group of the instruction at `pc`
(`not_warpDivergentAt_of_value`). Every two records then agree, ordered or not, so no ordering
argument is needed (a guard computed from the warp index, a launch value, or a register the warp's
collective source makes uniform).

At the poll branches, a kernel assumption that selects every poll branch with `uniPoll` (a
`pollAgree` assumption, ASM-POLL-AGREE) exempts every disagreeing pair whose polls use one object,
so no order between the lanes is needed: `not_warpDivergent_pollAgree` asks only that each poll
position polls one object across a warp (`PollObjUniform`), besides `¬ WarpDivergentAt U` for the
other positions (Inkling request L-j).

The per-thread premise is a property of the thread's states: `not_warpDivergentAt_of_inv` takes
an invariant of every step (`WStep`, `Walk.inv`) under which the guard at a position of `U`
evaluates to `G pc g` and the index reads `I pc g`. -/

namespace PTX

open PTX.Proof

noncomputable section

variable {U : Nat → Prop} {L : Launch} {K : Kernel} {A : List Assumption} {X : Execution}

/-- **No divergence at positions of group-uniform values.** -/
theorem not_warpDivergentAt_of_value (G : Nat → Nat → Bool) (I : Nat → Nat → Nat)
    (hv : ∀ g, g < L.threads → ∀ eg vg, eg <+: X.tr g → Walk K A L g {} eg vg →
      ∀ (i : Nat) (vi : Visit), vg[i]? = some vi → U vi.pc →
        (∀ b, vi.guard = some b → b = G vi.pc g) ∧ (∀ x, vi.index = some x → x = I vi.pc g))
    (hG : ∀ pc g h, U pc → SameUniformGroup L (K.uniformScopeAt pc) g h →
      G pc g = G pc h ∧ I pc g = I pc h) :
    ¬ WarpDivergentAt U L K A X := by
  rintro ⟨g, h, hg, hh, -, eg, eh, vg, vh, hpg, hph, hwg, hwh, i, j, pc, vi, vj, hu, hvi, hvj,
    hpi, hpj, hgrp, hdis, -⟩
  obtain ⟨hgg, hgi⟩ := hv g hg eg vg hpg hwg i vi hvi (hpi ▸ hu)
  obtain ⟨hhg, hhi⟩ := hv h hh eh vh hph hwh j vj hvj (hpj ▸ hu)
  obtain ⟨e1, e2⟩ := hG pc g h hu hgrp
  rw [hpi] at hgg hgi
  rw [hpj] at hhg hhi
  rcases hdis with ⟨b, b', hb, hb', hne⟩ | ⟨x, y, hx, hy, hne⟩
  · exact hne (by rw [hgg b hb, hhg b' hb', e1])
  · exact hne (by rw [hgi x hx, hhi y hy, e2])

/-- **No divergence at positions of group-uniform values, from an invariant of every step**: the
thread's invariant `P g` holds at its start and is kept by every step, and at a state satisfying
it the guard of a guarded uniform instruction at a position of `U` evaluates to `G pc g` and the
index a `brx.idx.uni` reads is `I pc g`. -/
theorem not_warpDivergentAt_of_inv (G : Nat → Nat → Bool) (I : Nat → Nat → Nat)
    (P : Nat → TState → Prop) (h0 : ∀ g, g < L.threads → P g {})
    (hstep : ∀ g s ev s', g < L.threads → P g s → WStep K A L g s ev s' → P g s')
    (hguard : ∀ g s ins b, g < L.threads → P g s → U s.pc → K.code[s.pc]? = some ins →
      ins.op.uniform = true → ins.guard.isSome = true → guardHolds s ins.guard = .ok b →
      b = G s.pc g)
    (hindex : ∀ g s ins x, g < L.threads → P g s → U s.pc → K.code[s.pc]? = some ins →
      uniIndex L g s ins.op = some x → x = I s.pc g)
    (hG : ∀ pc g h, U pc → SameUniformGroup L (K.uniformScopeAt pc) g h →
      G pc g = G pc h ∧ I pc g = I pc h) :
    ¬ WarpDivergentAt U L K A X := by
  refine not_warpDivergentAt_of_value G I (fun g hg eg vg _ hw i vi hvi hu => ?_) hG
  obtain ⟨s, ev, hs, rfl⟩ := Walk.inv (I := P g) (fun s ev s' hs hst => hstep g s ev s' hg hs hst)
    hw (h0 g hg) hvi
  simp only [visit] at hu ⊢
  refine ⟨fun b hb => ?_, fun x hx => ?_⟩
  · cases hc : K.code[s.pc]? with
    | none => rw [hc] at hb; cases hb
    | some ins =>
      rw [hc] at hb
      simp only at hb
      split_ifs at hb with hu'
      · simp only [Bool.and_eq_true] at hu'
        cases hgd : guardHolds s ins.guard with
        | error e => rw [hgd] at hb; cases hb
        | ok b' =>
          rw [hgd] at hb
          cases hb
          exact hguard g s ins b hg hs hu hc hu'.1 hu'.2 hgd
  · cases hc : K.code[s.pc]? with
    | none => rw [hc] at hx; cases hx
    | some ins =>
      rw [hc] at hx
      exact hindex g s ins x hg hs hu hc hx

/-- **No warp-divergent execution under a `pollAgree` assumption**: every lane-comparing
instruction is a poll branch or at a position of `U`, no execution diverges at the positions of
`U`, every poll branch is selected by an assumption's `uniPoll`, the code's local steps keep the
frame of their instruction, and each poll position polls one object across a warp. -/
theorem not_warpDivergent_pollAgree
    (hK : ∀ pc ins, K.code[pc]? = some ins → ins.laneCompared = true →
      K.pollBranch pc = true ∨ U pc)
    (hU : ¬ WarpDivergentAt U L K A X)
    (hloc : ∀ g t op t', execLocalA A L g t op = .ok t' → LocalFrame op t t')
    (hobj : PollObjUniform L X)
    (hsel : ∀ pc, K.pollBranch pc = true → A.any (·.uniPoll pc) = true) :
    ¬ WarpDivergent L K A X := by
  intro hd
  obtain ⟨g, h, hg, hh, -, eg, eh, vg, vh, hpg, hph, hwg, hwh, i, j, pc, vi, vj, hpb, hvi, hvj,
    hpi, hpj, hgrp, -, -, -, hnot⟩ := warpDivergent_split hK hU hd
  obtain ⟨-, -, dst, neg, tgt, base, off, par, acq, sc, hcb, hcw⟩ := pollBranch_spec hpb
  have hw : SameWarp L g h := by
    simpa [Kernel.uniformScopeAt, hcb, Op.uniformScope, SameUniformGroup] using hgrp
  have hpb1 : K.pollBranch vi.pc = true := by rw [hpi]; exact hpb
  obtain ⟨hi, ug, mg, pg, okg, acqg, scg, hug, hugev⟩ := hwg.poll_before (hloc g) hvi hpb1
  have hpb' : K.pollBranch vj.pc = true := by rw [hpj]; exact hpb
  obtain ⟨hj, uh, mh, ph, okh, acqh, sch, huh, huhev⟩ := hwh.poll_before (hloc h) hvj hpb'
  rw [hpj] at huhev
  rw [hpi] at hugev
  obtain ⟨hxg, -⟩ := hwg.event_get hpg hug hugev
  obtain ⟨hxh, -⟩ := hwh.event_get hph huh huhev
  have hm : mg = mh := hobj _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hg hh hw hxg hxh
  subst hm
  exact hnot ⟨hsel pc hpb, ⟨dst, neg, tgt, _, base, off, par, acq, sc, hcb, hcw, rfl⟩, ug, uh, mg,
    pg, ph, okg, okh, acqg, acqh, scg, sch, hug, huh, hi, hj, hugev, huhev⟩

end

end PTX
