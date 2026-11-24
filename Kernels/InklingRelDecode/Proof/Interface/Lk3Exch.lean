-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.Lk3Upd
public import Kernels.InklingRelDecode.Proof.Result.SvScoreLoad

@[expose] public section

/-!
# The exchange with the partner lane (`Sv.ExchPrem`)

The two shuffles of the stage (`shfl5`: the row maximum, `shfl6`: the sum of the probabilities)
exchange with the lane `^ 16` (`src16_mod`). Here: the thread's state after the exchange of the
row maximum (`shfl5_succ`: where the machine follows the received word, it is `D.afterMax` of
it) and the two shuffles' shapes. The exchange itself is `exchEv_at` (`Lk5PeerSv.lean`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface.Lk
open PTX PTX.Proof PTX.Flow PTX.Assumption PTX.Kernels.InklingRelDecode.Proof.Sm
open PTX.Kernels.InklingRelDecode.Proof.Sv (ValidRow ExchEv halfScores)

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-! ### The lane `^ 16` -/

theorem xor16_tab : ∀ T < 256, T - T % 32 + ((T % 32) ^^^ 16) = T ^^^ 16 := by decide

theorem src16_mod (hb : L.block = 256) (y : Nat) :
    shflSrc L y .bfly 16 31 % L.block = (y % L.block) ^^^ 16 := by
  have hl : laneOf L y < 32 := Nat.mod_lt _ (by decide)
  unfold shflSrc
  rw [shflSource_bfly hl (by norm_num)]
  simp only []
  have h1 : (y - laneOf L y + (laneOf L y ^^^ 16)) % L.block =
      y % L.block - laneOf L y + (laneOf L y ^^^ 16) := by
    unfold laneOf
    rw [hb]
    have : (y % 256 % 32 ^^^ 16) < 32 := by
      have := Nat.xor_lt_two_pow (n := 5) (x := y % 256 % 32) (y := 16) (by omega) (by omega)
      simpa using this
    omega
  rw [h1]
  have := xor16_tab (y % L.block) (by rw [hb]; omega)
  rw [← this]
  unfold laneOf
  rfl

/-! ### The thread's state after the exchange of the row maximum -/

theorem not_leaves_shfl {L : Launch} {g : Nat} {d : Sm.D} {e : Event}
    (h : d.site = .shfl5 ∨ d.site = .shfl6) : ¬ DComp.leaves L g d e := by
  unfold DComp.leaves
  rcases h with h | h <;> rw [h] <;> exact not_false

theorem sm_next_state {g k : Nat} {d d1 : Sm.D} {e : Event} (he : (X.tr g)[k]? = some e)
    (hσ : St Q L X g k = some (some (.d (.sm d)))) (hleave : ¬ DComp.leaves L g d e)
    (hn : Sm.next L g d e = some (some d1)) :
    St Q L X g (k + 1) = some (some (.d (.sm d1))) := by
  have h0 : Frame.stateAt (code L Q) X g k = some (some (.d (.sm d))) := hσ
  show Frame.stateAt (code L Q) X g (k + 1) = _
  rw [Frame.stateAt_succ he, h0]
  show (threadCode L g Q).next (.d (.sm d)) e = _
  rw [next_d]
  have hsm : DComp.next L g Q (.sm d) e = (Sm.next L g d e).map (Option.map DComp.St.sm) := by
    show DComp.smNext L g d e = _
    unfold DComp.smNext
    simp only [hleave, ↓reduceIte]
  rw [hsm, hn]
  rfl

/-- **The state after the exchange of the row maximum**, where it receives score words
(`SmMaxOk`): the thread's maximum, the word it received and its 64 score words are score words,
and the state is `D.afterMax` of the received word. -/
theorem shfl5_succ (hX : Consistent L kernel asms mem0 X) (hf : ThreadFacts Q L mem0 X)
    (hM : SmMaxOk Q L X)
    {g k : Nat} {d : Sm.D} {e : Event} (hg : g < L.threads) (he : X.get (g, k) = some e)
    (hσ : St Q L X g k = some (some (.d (.sm d)))) (hs : d.site = .shfl5) :
    ∃ (recv : Value) (ok : Bool),
      e = ⟨d.site.pc, .shfl .bfly (erealValue .f32 d.ownE) 16 31 recv ok⟩ ∧
      ScoreWord d.m ∧ ScoreWord recv ∧ (∀ j < 64, ScoreWord (d.stg.fsv j).1) ∧
      St Q L X g (k + 1) = some (some (.d (.sm (d.afterMax recv)))) := by
  obtain ⟨u, hF⟩ := fired_cont hX hf hg he hσ (by simp [ExitState])
  obtain ⟨recv, ok, he'⟩ := Sm.shape_shfl5 (fired_sm hF) hs
  have hk : e.kind = .shfl .bfly (ownV fun k => (d.stg.fsv k).1) 16 31 recv ok := by rw [he']
  have hck : d.RealIn recv := hM hg he hσ hs _ _ _ _ _ _ hk
  have hn : Sm.next L g d e = some (some (d.afterMax recv)) := by
    simp only [Sm.next, hs, hk, hck, ↓reduceIte]
  rw [Sm.ownV_fsv hck.2.2] at he'
  exact ⟨recv, ok, he', hck.1, hck.2.1, hck.2.2,
    sm_next_state (show (X.tr g)[k]? = some e from he) hσ (not_leaves_shfl (Or.inl hs)) hn⟩

theorem shflShape_5 (L : Launch) :
    ShflShape L .shfl5 (fun d => ownV fun k => (d.stg.fsv k).1) 16 :=
  fun hF hs => Sm.shape_shfl5 hF hs

theorem shflShape_6 (L : Launch) : ShflShape L .shfl6 (fun d => d.stg.sw) 16 :=
  fun hF hs => Sm.shape_shfl6 hF hs

theorem shflEv_recv {pc pc' : Nat} {m m' : ShflMode} {a a' : Value} {b b' c c' : Nat}
    {r r' : Value} {o o' : Bool}
    (h : (⟨pc, .shfl m a b c r o⟩ : Event) = ⟨pc', .shfl m' a' b' c' r' o'⟩) : r = r' := by
  cases h
  rfl

theorem shflKind_recv {m m' : ShflMode} {a a' : Value} {b b' c c' : Nat} {r r' : Value}
    {o o' : Bool} {pc : Nat}
    (h : (⟨pc, .shfl m a b c r o⟩ : Event).kind = .shfl m' a' b' c' r' o') : r = r' := by
  cases h
  rfl

theorem shflKind_recv_eq {e : Event} {m m' : ShflMode} {a a' : Value} {b b' c c' : Nat}
    {r r' : Value} {o o' : Bool} {pc : Nat} (h : e = ⟨pc, .shfl m a b c r o⟩)
    (h' : e.kind = .shfl m' a' b' c' r' o') : r' = r := by
  subst h
  exact (shflKind_recv h').symm

end
end PTX.Kernels.InklingRelDecode.Proof.Interface.Lk
