-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.Lk3Event
public import Lemmas.Flow.PollRendezvous
public import Kernels.InklingRelDecode.Proof.Interface.SvPred
public import Kernels.InklingRelDecode.Proof.Thread.Lk3Shape
public import Kernels.InklingRelDecode.Proof.Thread.Lk3Min
public import Kernels.InklingRelDecode.Proof.Thread.Lk3Num

@[expose] public section

/-!
# The rescale test's shuffles: source lanes, the four words' minimum, the edge into the P store

* `shflSrc`, `src_sameWarp`: the source lane of a shuffle is a lane of the thread's warp;
* `prev_shfl12`, `ShflShape`, `src_mod4`: the shapes of the test's two exchanges (`shfl11`,
  `shfl12`), whose source lanes are the lanes `^ 2` and `^ 1`;
* `Wmin`, `wmin_eq`: the minimum of the four scratch words in the order the decision builds it;
* `numInv_at`, `updOkSame`: every softmax state has the words `Sm.NumInv` (by induction along the
  trace from the region's first state, `Sv.pred_sm`), so the edge into the P store (`Sm.toBar20`)
  succeeds at every state, in both lanes of a pair or in neither (`UpdOkSame`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface.Lk
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The source lane of a shuffle: `g - laneOf g + j` with `j` a lane. -/
def shflSrc (L : Launch) (g : Nat) (m : ShflMode) (b c : Nat) : Nat :=
  g - laneOf L g + (shflSource m (laneOf L g) b c).1

theorem shflSource_lt (m : ShflMode) {lane b c : Nat} (hl : lane < 32) :
    (shflSource m lane b c).1 < 32 := by
  have hmax : ((lane &&& (c / 256 % 32)) ||| ((c % 32) &&& (31 - c / 256 % 32))) < 32 := by
    have h1 : (lane &&& (c / 256 % 32)) < 2 ^ 5 := Nat.and_lt_two_pow _ (by omega)
    have h2 : ((c % 32) &&& (31 - c / 256 % 32)) < 2 ^ 5 := Nat.and_lt_two_pow _ (by omega)
    have := Nat.or_lt_two_pow h1 h2
    simpa using this
  unfold shflSource
  cases m <;> simp only [] <;> split <;> simp_all <;> omega

/-- The lane `j` of the warp of a thread is a thread of its warp. -/
theorem src_sameWarp (hb : L.block = 256) {g : Nat} (hg : g < L.threads) {j : Nat} (hj : j < 32) :
    SameWarp L g (g - laneOf L g + j) ∧ laneOf L (g - laneOf L g + j) = j := by
  have hthr : L.threads = L.grid * 256 := by
    unfold Launch.threads
    rw [hb]
  unfold SameWarp SameCta laneOf
  rw [hb]
  rw [hthr] at hg ⊢
  refine ⟨⟨⟨hg, ?_, ?_⟩, ?_⟩, ?_⟩ <;> omega

end
end PTX.Kernels.InklingRelDecode.Proof.Interface.Lk

namespace PTX.Kernels.InklingRelDecode.Proof.Interface.Lk
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Sm
open PTX.Kernels.InklingRelDecode.Proof.Lk (dKey d_sy_key d_pc_range rangeOf smKey sm_key_comps)

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **Only the first exchange of the rescale test's second pair leads to the second.** -/
theorem prev_shfl12 {L : Launch} {g : Nat} {d d' : Sm.D} {e : Event}
    (hn : Sm.next L g d e = some (some d')) (h : d'.site = .shfl12) : d.site = .shfl11 := by
  unfold Sm.next at hn
  repeat' split at hn
  all_goals first
    | (simp only [Option.some.injEq, reduceCtorEq] at hn; done)
    | (simp only [Option.some.injEq] at hn; subst hn; simp_all; done)
    | (simp only [Option.some.injEq] at hn; subst hn; simp [Sm.D.afterSum] at h)
    | (have := Sv.afterSetup_site hn; rcases this with h' | h' <;> simp_all)
    | (have := Sv.toBar20_site hn; simp_all)

end
end PTX.Kernels.InklingRelDecode.Proof.Interface.Lk

namespace PTX.Kernels.InklingRelDecode.Proof.Interface.Lk
open PTX PTX.Proof PTX.Flow PTX.Assumption PTX.Kernels.InklingRelDecode.Proof.Sm

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The source lane of an `bfly` shuffle with offset `k < 32` and clamp 31. -/
theorem shflSource_bfly {lane k : Nat} (hl : lane < 32) (hk : k < 32) :
    shflSource .bfly lane k 31 = (lane ^^^ k, true) := by
  have hx : lane ^^^ k < 2 ^ 5 := Nat.xor_lt_two_pow hl hk
  unfold shflSource
  have e1 : 31 / 256 % 32 = 0 := by decide
  have e2 : k % 32 = k := Nat.mod_eq_of_lt hk
  simp only [e1, e2, Nat.and_zero, Nat.sub_zero, Nat.zero_or]
  have e3 : 31 % 32 &&& 31 = 31 := by decide
  rw [e3]
  have : lane ^^^ k ≤ 31 := by omega
  simp [this]

theorem xor2_mod4 : ∀ lane < 32, (lane ^^^ 2) % 4 = (lane % 4) ^^^ 2 := by decide

theorem xor1_mod4 : ∀ lane < 32, (lane ^^^ 1) % 4 = (lane % 4) ^^^ 1 := by decide

/-- The tile index modulo 4 of the source lane of a `bfly` shuffle of offset 2 (resp. 1). -/
theorem src_mod4 (hb : L.block = 256) {y : Nat} (k : Nat) (hk : k = 1 ∨ k = 2) :
    shflSrc L y .bfly k 31 % L.block % 4 = (y % L.block % 4) ^^^ k := by
  have hl : laneOf L y < 32 := Nat.mod_lt _ (by decide)
  have hk32 : k < 32 := by omega
  unfold shflSrc
  rw [shflSource_bfly hl hk32]
  simp only []
  have h1 : (y - laneOf L y + (laneOf L y ^^^ k)) % L.block % 4 = (laneOf L y ^^^ k) % 4 := by
    unfold laneOf
    rw [hb]
    have : (y % 256 % 32 ^^^ k) < 32 := by
      have := Nat.xor_lt_two_pow (n := 5) (x := y % 256 % 32) (y := k) (by omega) (by omega)
      simpa using this
    omega
  rw [h1]
  have h2 : laneOf L y % 4 = y % L.block % 4 := by
    unfold laneOf
    rw [hb]
    omega
  rcases hk with rfl | rfl
  · rw [xor1_mod4 _ hl, h2]
  · rw [xor2_mod4 _ hl, h2]

/-- The shape of the event a softmax state fires at a butterfly shuffle site: a full-warp
`shfl.sync.bfly` of the operand `fld d` with offset `k` and clamp 31. -/
def ShflShape (L : Launch) (site : Sm.Site) (fld : Sm.D → Value) (k : Nat) : Prop :=
  ∀ {g : Nat} {d : Sm.D} {e : Event} {u : TState}, Sm.Fired L g d e (some u) → d.site = site →
    ∃ (recv : Value) (ok : Bool), e = ⟨d.site.pc, .shfl .bfly (fld d) k 31 recv ok⟩

theorem shflShape_11 (L : Launch) : ShflShape L .shfl11 (fun d => d.stg.ld) 2 :=
  fun hF hs => Sm.shape_shfl11 hF hs

theorem shflShape_12 (L : Launch) : ShflShape L .shfl12 (fun d => d.stg.m2) 1 :=
  fun hF hs => Sm.shape_shfl12 hF hs

/-- The exchange at `shfl11` keeps the iteration. -/
theorem shfl11_succ_i {L : Launch} {g : Nat} {d0 d : Sm.D} {e : Event}
    (hn : Sm.next L g d0 e = some (some d)) (hs : d0.site = .shfl11) : d.i = d0.i := by
  simp only [Sm.next, hs] at hn
  repeat' split at hn
  all_goals first
    | (simp at hn; done)
    | (simp only [Option.some.injEq] at hn; subst hn; rfl)

/-- **The four words' minimum**, in the order the decision is built. -/
def Wmin (W : Nat → EReal) : EReal := min (min (W 0) (W 1)) (min (W 2) (W 3))

/-- The minimum over the lanes `r`, `r ^ 2`, `r ^ 1`, `r ^ 3` of the words is the four words'
minimum. -/
theorem wmin_eq (W : Nat → EReal) {r : Nat} (hr : r < 4) :
    min (min (W r) (W (r ^^^ 2))) (min (W (r ^^^ 1)) (W ((r ^^^ 1) ^^^ 2))) = Wmin W := by
  unfold Wmin
  rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3) with rfl | rfl | rfl | rfl <;>
    simp only [Nat.reduceXor] <;> ac_rfl

theorem min_ne_top' {x y : EReal} (hx : x ≠ ⊤) : min x y ≠ ⊤ :=
  ne_top_of_le_ne_top hx (min_le_left _ _)

end
end PTX.Kernels.InklingRelDecode.Proof.Interface.Lk

namespace PTX.Kernels.InklingRelDecode.Proof.Interface.Lk
open PTX PTX.Proof PTX.Flow PTX.Assumption PTX.Kernels.InklingRelDecode.Proof.Sm
open PTX.Kernels.InklingRelDecode.Proof.Lk (smKey sm_key_comps smSy SmAgree BranchBar20)

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **The edge into the P store succeeds in both lanes or in neither.** At `shfl12` the successor
along the branch to the P store is `Sm.toBar20`, which faults when the new running maximum is not a
word of four bytes or the update `fma` has no outcome. -/
def UpdOkSame (Q : Params) (L : Launch) (X : Execution) : Prop :=
  ∀ {g h a b : Nat} {d d' : Sm.D}, SameWarp L g h →
    St Q L X g a = some (some (.d (.sm d))) → St Q L X h b = some (some (.d (.sm d'))) →
    d.site = .shfl12 → d'.site = .shfl12 → (d.updOk = true ↔ d'.updOk = true)

end
end PTX.Kernels.InklingRelDecode.Proof.Interface.Lk

namespace PTX.Kernels.InklingRelDecode.Proof.Interface.Lk
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Sm

noncomputable section

variable {Q : Params} {L : Launch} {X : Execution} {g : Nat}

/-- **A softmax state of a thread has the numbers**, at any event index of its trace. -/
theorem numInv_at {k : Nat} {d : Sm.D} (hk : k ≤ (X.tr g).length)
    (hσ : St Q L X g k = some (some (.d (.sm d)))) : NumInv d := by
  induction k using Nat.strong_induction_on generalizing d with
  | _ k ih =>
    rcases Sv.pred_sm hk hσ with ⟨dt, rfl⟩ | ⟨k0, d0, e, rfl, he, hσ0, hn⟩
    · exact numInv_init _
    · exact numInv_next (ih k0 (by omega) (by omega) hσ0) hn

theorem numInv_state {k : Nat} {d : Sm.D} (hσ : St Q L X g k = some (some (.d (.sm d)))) :
    NumInv d := by
  by_cases hk : k ≤ (X.tr g).length
  · exact numInv_at hk hσ
  · have h1 : Frame.stateAt (code L Q) X g k =
        Frame.stateAt (code L Q) X g (X.tr g).length :=
      Frame.stateAt_of_le (by omega)
    have h2 : St Q L X g (X.tr g).length = some (some (.d (.sm d))) := h1.symm.trans hσ
    exact numInv_at le_rfl h2

/-- **The softmax states have the real numbers**: at every softmax state of a thread the flag
`Sm.Stg.re` is set, so the registers of the score stage hold the real numbers the state records
(`Sm.Inv.re`, `Sm.RealSt`: `alpha`, the probability words, their sum's word). -/
def SmReal (Q : Params) (L : Launch) (X : Execution) : Prop :=
  ∀ {g k : Nat} {d : Sm.D}, St Q L X g k = some (some (.d (.sm d))) → d.stg.re = true

/-- **The exchange of the row maximum receives score words**: at every softmax state of a
thread at the exchange of the row maximum, the running maximum, the word the event received and
the 64 words of the columns are score words (`Sm.D.RealIn`), so the machine takes the successor of
the real numbers (`Sm.D.afterMax`). Proved in the result layer (`Qy.smMaxOk_of`) from the S words
being `f32` numbers. -/
def SmMaxOk (Q : Params) (L : Launch) (X : Execution) : Prop :=
  ∀ {g k : Nat} {d : Sm.D} {e : Event}, g < L.threads → X.get (g, k) = some e →
    St Q L X g k = some (some (.d (.sm d))) → d.site = .shfl5 →
    ∀ m av bv cv r o, e.kind = .shfl m av bv cv r o → d.RealIn r

theorem smReal_at {mem0 : Mem0} (hX : Consistent L kernel asms mem0 X) (hM : SmMaxOk Q L X)
    {k : Nat} {d : Sm.D} (hk : k ≤ (X.tr g).length)
    (hσ : St Q L X g k = some (some (.d (.sm d)))) : d.stg.re = true := by
  induction k using Nat.strong_induction_on generalizing d with
  | _ k ih =>
    rcases Sv.pred_sm hk hσ with ⟨dt, rfl⟩ | ⟨k0, d0, e, rfl, he, hσ0, hn⟩
    · rfl
    · have he' : X.get (g, k0) = some e := he
      rw [re_next hn (fun h5 m av bv cv r o hke =>
        hM (Frame.lt_of_get hX he') he' hσ0 h5 m av bv cv r o hke)]
      exact ih k0 (by omega) (by omega) hσ0

/-- **`SmReal` from `SmMaxOk`**: only the exchange of the row maximum on words that are not score
words clears the flag (`Sm.re_next`). -/
theorem smReal_of_max {mem0 : Mem0} (hX : Consistent L kernel asms mem0 X)
    (hM : SmMaxOk Q L X) : SmReal Q L X := by
  intro g k d hσ
  by_cases hk : k ≤ (X.tr g).length
  · exact smReal_at hX hM hk hσ
  · have h1 : Frame.stateAt (code L Q) X g k =
        Frame.stateAt (code L Q) X g (X.tr g).length :=
      Frame.stateAt_of_le (by omega)
    have h2 : St Q L X g (X.tr g).length = some (some (.d (.sm d))) := h1.symm.trans hσ
    exact smReal_at hX hM le_rfl h2

/-- **`UpdOkSame`**: the edge into the P store succeeds at every softmax state. -/
theorem updOkSame : UpdOkSame Q L X := by
  intro g h a b d d' hw hs hs' _ _
  exact ⟨fun _ => updOk_of (numInv_state hs'), fun _ => updOk_of (numInv_state hs)⟩

variable {mem0 : Mem0}

end
end PTX.Kernels.InklingRelDecode.Proof.Interface.Lk
