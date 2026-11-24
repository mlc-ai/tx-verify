-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.Lk5VShfl

@[expose] public section

/-!
# The value chain of the lazy-rescale test, by iteration

Without the warp lockstep: the source lane of a shuffle of the softmax region is found by the count
of shuffles (`shfl_same_site`).

* `sm_shfl_peer_d`: the source lane of a butterfly shuffle of the region is at the softmax state of
  the same site and iteration, and the received word is the field of that state;
* `m2_value_d`, `p170_value_d`: given that the scratch words of iteration `i` read as numbers
  `W r` in CTA `c` (the body of `ScratchIt`), the decision at `shfl12` is the comparison of the four
  words' minimum with `1.0`;
* `decAgree_of_it`: `ScratchIt i` gives `DecAgree c i` for every CTA `c`.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface.Lk
open PTX PTX.Proof PTX.Flow PTX.Assumption PTX.Kernels.InklingRelDecode.Proof.Sm

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- A softmax state is a default-partition thread's. -/
theorem sm_def {g k : Nat} {d : Sm.D} (hk : k ≤ (X.tr g).length)
    (hσ : St Q L X g k = some (some (.d (.sm d)))) : g % L.block < 128 :=
  (cls_inv k _ hk hσ).mp trivial

/-- **The source lane of a shuffle of the softmax region is at the same site and iteration**,
without the lockstep. -/
theorem sm_shfl_peer_d (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hb : L.block = 256) {y a : Nat} {d : Sm.D} {e : Event}
    {fld : Sm.D → Value} {k : Nat} (hshp : ShflShape L d.site fld k)
    (hy : y < L.threads) (hge : X.get (y, a) = some e)
    (hs : St Q L X y a = some (some (.d (.sm d)))) :
    ∃ (recv : Value) (ok : Bool) (x j : Nat) (d2 : Sm.D),
      e = ⟨d.site.pc, .shfl .bfly (fld d) k 31 recv ok⟩ ∧ SameWarp L y x ∧
      x = shflSrc L y .bfly k 31 ∧ St Q L X x j = some (some (.d (.sm d2))) ∧
      d2.site = d.site ∧ d2.i = d.i ∧ recv = fld d2 ∧
      (k = 1 ∨ k = 2 → x % L.block % 4 = (y % L.block % 4) ^^^ k) ∧ j ≤ (X.tr x).length ∧
      ∃ (r2 : Value) (o2 : Bool),
        X.get (x, j) = some ⟨d2.site.pc, .shfl .bfly (fld d2) k 31 r2 o2⟩ := by
  have hyd := sm_def (event_le hge) hs
  obtain ⟨u, hF⟩ := fired_cont hX hf hy hge hs (by simp [ExitState])
  obtain ⟨recv, ok, he⟩ := hshp (fired_sm hF) rfl
  subst he
  have hk' : X.ShflK (y, a) (((X.tr y).take a).countP Execution.isShfl) :=
    ⟨⟨_, _, _, _, _, _, _, hge⟩, rfl⟩
  obtain ⟨j, pc', b', c', r', o', hkj, hget', hw⟩ :=
    shfl_source_d (Q := Q) hX (shflLiveD_of hpre hX hf) hb hy hyd hge hk'
  obtain ⟨s', hs'⟩ := Frame.event_state hf.sound hX hf.tracked hget' (fun pc f h => by cases h)
  have hs'' : St Q L X (shflSrc L y .bfly k 31) j = some (some s') := hs'
  obtain ⟨d2, rfl, hsite2, hi2⟩ := shfl_same_site hpre hX hf hw hk' hkj hs hs'' hyd
  obtain ⟨u2, hF2⟩ := fired_cont hX hf hw.1.2.1 hget' hs'' (by simp [ExitState])
  obtain ⟨recv2, ok2, he2⟩ := hshp (fired_sm hF2) hsite2
  have hkind := congrArg Event.kind he2
  simp only [Kind.shfl.injEq] at hkind
  have hev2 : X.get (shflSrc L y .bfly k 31, j) =
      some ⟨d2.site.pc, .shfl .bfly (fld d2) k 31 recv2 ok2⟩ := by rw [hget', he2]
  exact ⟨recv, ok, _, j, d2, rfl, hw, rfl, hs'', hsite2, hi2, hkind.2.1,
    fun hk' => src_mod4 hb k hk', event_le hget', recv2, ok2, hev2⟩

/-- The body of `ScratchIt` at one CTA. -/
def ScratchW (Q : Params) (L : Launch) (X : Execution) (c i : Nat) (W : Nat → EReal) : Prop :=
  ∀ {g k : Nat} {d : Sm.D}, g < L.threads → g / L.block = c →
    St Q L X g k = some (some (.d (.sm d))) → d.site = .shfl11 → d.i = i →
    ReadsAs d.stg.ld (W (g % L.block % 4))

/-- **`m2` of a lane at `shfl12`**, without the lockstep. -/
theorem m2_value_d (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hb : L.block = 256) {c i : Nat} {W : Nat → EReal}
    (hR : ScratchW Q L X c i W) {y a : Nat} {d : Sm.D} (hy : y < L.threads)
    (hyc : y / L.block = c) (hs : St Q L X y a = some (some (.d (.sm d))))
    (hsite : d.site = .shfl12) (hi : d.i = i) (ha : a ≤ (X.tr y).length) :
    d.stg.m2 = erealValue .f32 (min (W (y % L.block % 4)) (W ((y % L.block % 4) ^^^ 2))) := by
  rcases Sv.pred_sm ha hs with ⟨dt, rfl⟩ | ⟨k0, d0, e0, rfl, he0, hσ0, hn⟩
  · simp [SmEntry.d0] at hsite
  have hs0 : d0.site = .shfl11 := prev_shfl12 hn hsite
  have hi0 : d0.i = i := by rw [← hi]; exact (shfl11_succ_i hn hs0).symm
  have hge0 : X.get (y, k0) = some e0 := he0
  obtain ⟨recv, ok, x, j, d2, he0', hw, -, hσ2, hsite2, hi2, hrecv, hmod, -⟩ :=
    sm_shfl_peer_d hpre hX hf hb (fld := fun d => d.stg.ld) (k := 2)
      (by rw [hs0]; exact shflShape_11 L) hy hge0 hσ0
  have hx1 : ReadsAs d0.stg.ld (W (y % L.block % 4)) := hR hy hyc hσ0 hs0 hi0
  have hxc : x / L.block = c := hw.1.2.2.symm.trans hyc
  have hx2 : ReadsAs recv (W ((y % L.block % 4) ^^^ 2)) := by
    rw [hrecv, ← hmod (Or.inr rfl)]
    exact hR hw.1.2.1 hxc hσ2 (hsite2.trans hs0) (hi2.trans hi0)
  have he : e0.kind = .shfl .bfly d0.stg.ld 2 31 recv ok := by rw [he0']
  have hn' := next_shfl11 L y hs0 he hx1 hx2
  rw [hn'] at hn
  have := Option.some.inj (Option.some.inj hn)
  rw [← this]
  rfl

/-- **The decision `%p170` at `shfl12` is a function of the four words**, without the lockstep.
-/
theorem p170_value_d (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hb : L.block = 256) {c i : Nat} {W : Nat → EReal}
    (hW : ∀ r, W r ≠ ⊤) (hR : ScratchW Q L X c i W) {y a : Nat} {d : Sm.D} {e : Event}
    (hy : y < L.threads) (hyc : y / L.block = c) (hge : X.get (y, a) = some e)
    (hs : St Q L X y a = some (some (.d (.sm d)))) (hsite : d.site = .shfl12) (hi : d.i = i) :
    ∃ (recv : Value) (ok : Bool), e = ⟨d.site.pc, .shfl .bfly d.stg.m2 1 31 recv ok⟩ ∧
      d.p170 recv = setpE (.unord .ge) false (erealValue .f32 (Wmin W)) (b32 1065353216) := by
  have ha : a ≤ (X.tr y).length := event_le hge
  obtain ⟨recv, ok, x, j, d2, he, hw, -, hσ2, hsite2, hi2, hrecv, hmod, hj, -⟩ :=
    sm_shfl_peer_d hpre hX hf hb (fld := fun d => d.stg.m2) (k := 1)
      (by rw [hsite]; exact shflShape_12 L) hy hge hs
  have hxc : x / L.block = c := hw.1.2.2.symm.trans hyc
  have hm2y : ReadsAs d.stg.m2 (min (W (y % L.block % 4)) (W ((y % L.block % 4) ^^^ 2))) := by
    rw [m2_value_d hpre hX hf hb hR hy hyc hs hsite hi ha]
    exact ReadsAs.of_erealValue (min_ne_top' (hW _))
  have hm2x := m2_value_d hpre hX hf hb hR hw.1.2.1 hxc hσ2 (hsite2.trans hsite)
    (hi2.trans hi) hj
  have hrx : ReadsAs recv (min (W (x % L.block % 4)) (W ((x % L.block % 4) ^^^ 2))) := by
    rw [hrecv, hm2x]
    exact ReadsAs.of_erealValue (min_ne_top' (hW _))
  rw [hmod (Or.inl rfl)] at hrx
  refine ⟨recv, ok, he, ?_⟩
  rw [p170_readsAs d hm2y hrx, wmin_eq W (Nat.mod_lt _ (by decide))]

/-- **`ScratchIt i` gives the decision agreement of iteration `i` in every CTA.** -/
theorem decAgree_of_it (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) {j : Nat} (hS : ScratchIt Q L X j) (c : Nat) :
    DecAgree Q L X c j := by
  intro g g' k k' d d' e e' hg hg' hc hc' he he' hs hs' hsite hsite' hi hi'
  have hb : L.block = 256 := hpre.block
  obtain ⟨W, hW, hR⟩ := hS c
  have hR' : ScratchW Q L X c j W := fun hg hc hσ hs hi => hR hg hc hσ hs hi
  obtain ⟨r1, o1, he1, hp1⟩ := p170_value_d hpre hX hf hb hW hR' hg hc he hs hsite hi
  obtain ⟨r2, o2, he2, hp2⟩ := p170_value_d hpre hX hf hb hW hR' hg' hc' he' hs' hsite' hi'
  exact ⟨r1, r2, o1, o2, he1, he2, hp1.trans hp2.symm⟩

end
end PTX.Kernels.InklingRelDecode.Proof.Interface.Lk
