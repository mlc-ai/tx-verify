-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.PrefixTrack
public import Kernels.InklingRelDecode.Proof.Interface.SameValue
public import Kernels.InklingRelDecode.Proof.Interface.ShapeInput
public import Kernels.InklingRelDecode.Proof.Interface.WordsThreads
public import Lemmas.Flow.AllocTmpl
public import Kernels.InklingRelDecode.Proof.Interface.ExitFacts
public import Kernels.InklingRelDecode.Proof.Thread.ClassQNext

@[expose] public section

/-!
# The prologue's request-word loads continue the machine (prefix form)

The prologue machine leaves its run (`ProA.next = some none`) at the three loads of the request's
words when the loaded bytes are no 32-bit word, and at the third when the three words do not
satisfy `WordsOk`, and `DComp.proNext` leaves it at `bar18` when the words are not the request's.
`pro_words_next_ne` proves that none of these happens at an event that `Good` allows: the load's
bytes are the launch's (`LaunchRead`), the earlier loads' were (`Good` at the thread's earlier
events), and the words of a request of the launch satisfy `WordsOk` (`ProA.wordsOk_of_pre`).

`WordsSo` (the words a prologue state has loaded are the request's) holds at every state of a
thread whose earlier events are `Good` (`wordsSo_all_at`); `Mbar.wordsSo_all` (`MbarWords.lean`)
is its form for an execution whose machines follow every thread.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Mbar
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.InklingRelDecode.Proof.Interface

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The request words a prologue state has loaded are the request's: `cu0` from the second load
on, `cu1` from the third, `sk` after the third. -/
def WordsSo (Q : Params) (L : Launch) (g : Nat) : TSt → Prop
  | .d (.pro d) =>
    (d.site ≠ .sMax → d.site ≠ .ldCu0 → d.dt.cu0 = Q.qStart (ProA.cta L g .z)) ∧
    ((d.site.afterSk = true ∨ d.site = .ldSk) → d.dt.cu1 = Q.qStart (ProA.cta L g .z + 1)) ∧
    (d.site.afterSk = true → d.dt.sk = Q.seqK (ProA.cta L g .z))
  | _ => True

theorem qStart_lt32 (hpre : Pre Q L mem0) {r : Nat} (hr : r ≤ Q.b) : Q.qStart r < 2 ^ 32 := by
  have h1 := qStart_mono hpre hr (Nat.le_refl _)
  have h2 := hpre.cuEnd
  have h3 := hpre.nTokRange
  omega

theorem reads_cu {r : Nat} (hr : r ≤ Q.b) {k : Nat} (hk : k < 4) :
    Q.reads (Q.cuBase + 4 * r + k) :=
  Or.inr (Or.inr (Or.inr (Or.inl ⟨r, hr, k, hk, rfl⟩)))

theorem reads_seq {r : Nat} (hr : r < Q.b) {k : Nat} (hk : k < 4) :
    Q.reads (Q.seqBase + 4 * r + k) :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨r, hr, k, hk, rfl⟩))))

theorem next_map_some {α β : Type} {f : α → β} {o : Option (Option α)} {s : β}
    (h : o.map (Option.map f) = some (some s)) : ∃ a, o = some (some a) ∧ f a = s := by
  cases o with
  | none => cases h
  | some o =>
    cases o with
    | none => cases h
    | some a => exact ⟨a, rfl, Option.some.inj (Option.some.inj h)⟩

theorem wordsSo_start (g : Nat) (P : ProA.Inh) (w : Value) :
    WordsSo Q L g (.d (.pro (ProA.D.start P w))) := by
  have h : (ProA.D.start P w).site = .sMax := rfl
  refine ⟨fun h' => absurd h h', fun h' => ?_, fun h' => ?_⟩ <;>
    simp [h, ProA.Site.afterSk] at h'

/-- No successor of the softmax region or of the epilogue is a prologue state. -/
theorem next_sm_not_pro (g : Nat) (Q : Params) (d : Sm.D) (e : Event) (d1 : ProA.D) :
    DComp.next L g Q (.sm d) e ≠ some (some (.pro d1)) := by
  intro h
  have h' : DComp.smNext L g d e = some (some (.pro d1)) := h
  unfold DComp.smNext at h'
  split at h'
  · unfold DComp.exitNext at h'
    split at h'
    · cases h'
    · cases h'
  · obtain ⟨a, -, ha⟩ := next_map_some h'
    cases ha

theorem next_epi_not_pro (g : Nat) (Q : Params) (d : Epi.D) (e : Event) (d1 : ProA.D) :
    DComp.next L g Q (.epi d) e ≠ some (some (.pro d1)) := by
  intro h
  have h' : (Epi.next d e).map (Option.map DComp.St.epi) = some (some (.pro d1)) := h
  obtain ⟨a, -, ha⟩ := next_map_some h'
  cases ha

end
end PTX.Kernels.InklingRelDecode.Proof.Mbar

namespace PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.InklingRelDecode.Proof.Mbar

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-! ### Local forms of the event-state lemmas -/

/-- **An exit event fires from an exit state.** -/
theorem exit_state_at (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) {g k pc : Nat} {s : TSt}
    (he : X.get (g, k) = some ⟨pc, .exit⟩) (hσ : St Q L X g k = some (some s)) :
    ExitState s := by
  obtain ⟨t, ins, o, hat, hinv, hc, hf⟩ := Frame.fired_site hS hX he hσ
  have hop : isExitOp ins.op = true := by
    rcases fires_exit_op hf (rfl : (⟨pc, .exit⟩ : Event).kind = .exit) with h | h <;>
      simp [isExitOp, h]
  have hpw : TSt.pc s ∈ exitPcs := OpPcsFast.mem kernel_exit_pcs hc hop
  cases s with
  | w s =>
    cases s with
    | worker w => exact absurd hpw (fun h => by simpa using worker_exit_pc w.site h)
    | idle d => exact absurd hpw (fun h => by simpa using idle_exit_pc d.site h)
    | loader d _ => exact absurd hpw (fun h => by simpa using loader_exit_pc d.site h)
    | mma d _ => exact absurd hpw (fun h => by simpa using mma_exit_pc d.site h)
    | exit x => simpa [ExitState] using exitsite_exit_pc x.site hpw
  | d s =>
    cases s with
    | dstart d => exact absurd hpw (fun h => by simpa using dstart_exit_pc d.site h)
    | pro d => exact absurd hpw (fun h => by simpa using pro_exit_pc d.site h)
    | sm d => exact absurd hpw (fun h => by simpa using sm_exit_pc d.site h)
    | epi d => simpa [ExitState] using epi_exit_pc d.site hpw

/-- **An event at a followed state that is not an exit continues the thread** (`fired_cont`
without `ThreadFacts`: the machines are sound, and no state fires an undefined-behaviour
template). -/
theorem fired_cont_at (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound)
    (hT : ∀ g < L.threads, (threadCode L g Q).TmplOk) {g k : Nat} {e : Event} {s : TSt}
    (hg : g < L.threads) (he : X.get (g, k) = some e) (hσ : St Q L X g k = some (some s))
    (hs : ¬ ExitState s) : ∃ u, (threadCode L g Q).toMachine.Fired (some s) e (some u) :=
  fired_cont_of hS hX hg he hσ hs
    (fun h => by subst h; exact Code.ub_stopped (hS g hg) (hT g hg) (hX.thr g hg) he)
    (fun h => by subst h; exact exit_state_at hX hS he hσ)

/-! ### The words of the launch -/

/-- **A four-byte read of input bytes returns the bytes of their word**, given the launch bytes of
the read (`LaunchRead`). -/
theorem input_word_of_launch {g k pc : Nat} {a : Acc} {bs : List (Option Byte)}
    (hX : Consistent L kernel asms mem0 X) (hL : LaunchRead Q mem0 X (g, k))
    (he : X.get (g, k) = some ⟨pc, .rd a bs⟩) {A : Nat} (hloc : a.loc = ⟨.global, 0, A⟩)
    (hsz : a.size = 4) (x : Nat)
    (hx : ∀ j < 4, Q.reads (A + j) ∧ mem0 ⟨.global, 0, A + j⟩ = some (some (i32Byte x j))) :
    bs = (b32 x).toBytes.map some :=
  word_of_bytes hX he hloc hsz x hx fun j hj hrd =>
    hL pc a bs he (by rw [hloc]) (by rw [hloc]) j (by omega) hrd

/-- **A word load returns the launch's word.** -/
theorem loaded_word_at (hX : Consistent L kernel asms mem0 X) {g k pc A x : Nat}
    {bs : List (Option Byte)} (hL : LaunchRead Q mem0 X (g, k))
    (he : X.get (g, k) = some ⟨pc, .rd (EvD.wordAcc ⟨.global, 0, A⟩) bs⟩)
    (hx32 : x < 2 ^ 32)
    (hx : ∀ j < 4, Q.reads (A + j) ∧ mem0 ⟨.global, 0, A + j⟩ = some (some (i32Byte x j)))
    {a' : Acc} {bs' : List (Option Byte)} {v : Value} {x' : Nat}
    (hk : (⟨pc, .rd (EvD.wordAcc ⟨.global, 0, A⟩) bs⟩ : Event).kind = .rd a' bs')
    (hrb : rebuild 3 bs' = .ok v) (hw : ProA.word32 v = some x') : x' = x := by
  have hbs := input_word_of_launch hX hL he (A := A) rfl rfl x hx
  simp only [Kind.rd.injEq] at hk
  obtain ⟨-, rfl⟩ := hk
  rw [hbs, rebuild_b32] at hrb
  cases hrb
  rw [ProA.word32_b32 hx32] at hw
  exact (Option.some.inj hw).symm

/-! ### The three loads -/

variable (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound)
    (hT : ∀ g < L.threads, (threadCode L g Q).TmplOk)
include hpre hX hS hT

/-- **The first load stores `cu_seqlens_q[req]`.** -/
theorem load_cu0_at {g k : Nat} {s : ProA.Site} {dt : ProA.Dat} {d' : ProA.D} {e : Event}
    (hg : g < L.threads) (he : X.get (g, k) = some e)
    (hσ : St Q L X g k = some (some (.d (.pro ⟨s, dt⟩)))) (hL : LaunchRead Q mem0 X (g, k))
    (hs : s = .ldCu0) (hn : ProA.next L g ⟨s, dt⟩ e = some (some d')) :
    d'.dt.cu0 = Q.qStart (ProA.cta L g .z) := by
  subst hs
  obtain ⟨u, hF⟩ := fired_cont_at hX hS hT hg he hσ (by simp [ExitState])
  obtain ⟨bs, hlen, hev⟩ := ProA.shape_cu hpre hg (fired_pro hF) (Or.inl rfl)
  simp only [ite_true] at hev
  subst hev
  obtain ⟨a', bs', v, x', hk, hrb, hw, rfl⟩ := ProA.next_ldCu0 hn
  have hz := (ProA.cta_lt hpre hg).2.2
  have hb := hpre.bRange
  have hr := hpre.readsRange (Q.cuBase + 4 * ProA.cta L g .z + 3)
    (reads_cu (by omega) (by omega))
  have hA : (Q.cuBase + 4 * ProA.cta L g .z) % 2 ^ 64 = Q.cuBase + 4 * ProA.cta L g .z :=
    Nat.mod_eq_of_lt (by omega)
  rw [hA] at he hk
  exact loaded_word_at hX hL he (qStart_lt32 hpre (by omega))
    (fun j hj => ⟨reads_cu (by omega) hj, hpre.cuInput _ (by omega) j hj⟩) hk hrb hw

/-- **The second load stores `cu_seqlens_q[req + 1]`.** -/
theorem load_cu1_at {g k : Nat} {s : ProA.Site} {dt : ProA.Dat} {d' : ProA.D} {e : Event}
    (hg : g < L.threads) (he : X.get (g, k) = some e)
    (hσ : St Q L X g k = some (some (.d (.pro ⟨s, dt⟩)))) (hL : LaunchRead Q mem0 X (g, k))
    (hs : s = .ldCu1) (hn : ProA.next L g ⟨s, dt⟩ e = some (some d')) :
    d'.dt.cu1 = Q.qStart (ProA.cta L g .z + 1) := by
  subst hs
  obtain ⟨u, hF⟩ := fired_cont_at hX hS hT hg he hσ (by simp [ExitState])
  obtain ⟨bs, hlen, hev⟩ := ProA.shape_cu hpre hg (fired_pro hF) (Or.inr (Or.inl rfl))
  simp only [reduceCtorEq, ite_false, ite_true] at hev
  subst hev
  obtain ⟨a', bs', v, x', hk, hrb, hw, rfl⟩ := ProA.next_ldCu1 hn
  have hz := (ProA.cta_lt hpre hg).2.2
  have hb := hpre.bRange
  have hr := hpre.readsRange (Q.cuBase + 4 * (ProA.cta L g .z + 1) + 3)
    (reads_cu (by omega) (by omega))
  have hA : (Q.cuBase + 4 * (ProA.cta L g .z + 1)) % 2 ^ 64 =
      Q.cuBase + 4 * (ProA.cta L g .z + 1) := Nat.mod_eq_of_lt (by omega)
  rw [hA] at he hk
  exact loaded_word_at hX hL he (qStart_lt32 hpre (by omega))
    (fun j hj => ⟨reads_cu (by omega) hj, hpre.cuInput _ (by omega) j hj⟩) hk hrb hw

/-- **The third load stores `seq_lens[req]`.** -/
theorem load_sk_at {g k : Nat} {s : ProA.Site} {dt : ProA.Dat} {d' : ProA.D} {e : Event}
    (hg : g < L.threads) (he : X.get (g, k) = some e)
    (hσ : St Q L X g k = some (some (.d (.pro ⟨s, dt⟩)))) (hL : LaunchRead Q mem0 X (g, k))
    (hs : s = .ldSk) (hn : ProA.next L g ⟨s, dt⟩ e = some (some d')) :
    d'.dt.sk = Q.seqK (ProA.cta L g .z) := by
  subst hs
  obtain ⟨u, hF⟩ := fired_cont_at hX hS hT hg he hσ (by simp [ExitState])
  obtain ⟨bs, hlen, hev⟩ := ProA.shape_cu hpre hg (fired_pro hF) (Or.inr (Or.inr rfl))
  simp only [reduceCtorEq, ite_false] at hev
  subst hev
  obtain ⟨a', bs', v, x', hk, hrb, hw, rfl⟩ := ProA.next_ldSk hn
  have hz := (ProA.cta_lt hpre hg).2.2
  have hb := hpre.bRange
  have hr := hpre.readsRange (Q.seqBase + 4 * ProA.cta L g .z + 3)
    (reads_seq (by omega) (by omega))
  have hA : (Q.seqBase + 4 * ProA.cta L g .z) % 2 ^ 64 = Q.seqBase + 4 * ProA.cta L g .z :=
    Nat.mod_eq_of_lt (by omega)
  have hsk := hpre.seqRange _ hz
  rw [hA] at he hk
  exact loaded_word_at hX hL he (by omega)
    (fun j hj => ⟨reads_seq hz hj, hpre.seqInput _ hz j hj⟩) hk hrb hw

/-! ### The words along the thread -/

/-- **One prologue step keeps `WordsSo`.** -/
theorem wordsSo_step_at {g k : Nat} {d0 d1 : ProA.D} {e : Event} (hg : g < L.threads)
    (he : X.get (g, k) = some e) (hσ : St Q L X g k = some (some (.d (.pro d0))))
    (hL : LaunchRead Q mem0 X (g, k)) (hI : WordsSo Q L g (.d (.pro d0)))
    (hn : ProA.next L g d0 e = some (some d1)) :
    WordsSo Q L g (.d (.pro d1)) := by
  obtain ⟨s, dt⟩ := d0
  obtain ⟨h0, h1, h2⟩ := hI
  by_cases hk : s.afterSk = true
  · obtain ⟨kc0, kc1, ks⟩ := ProA.keeps_next hn hk
    have hs' := ProA.afterSk_next hn hk
    have hne : s ≠ .sMax ∧ s ≠ .ldCu0 := by
      constructor <;> (rintro rfl; simp [ProA.Site.afterSk] at hk)
    refine ⟨fun _ _ => ?_, fun _ => ?_, fun _ => ?_⟩
    · rw [kc0]
      exact h0 hne.1 hne.2
    · rw [kc1]
      exact h1 (Or.inl hk)
    · rw [ks]
      exact h2 hk
  · have hs4 : s = .sMax ∨ s = .ldCu0 ∨ s = .ldCu1 ∨ s = .ldSk := by
      cases s <;> simp_all [ProA.Site.afterSk]
    rcases hs4 with rfl | rfl | rfl | rfl
    · rw [ProA.next_sMax hn]
      exact ⟨fun _ h => absurd rfl h, fun h => by simp [ProA.Site.afterSk] at h,
        fun h => by simp [ProA.Site.afterSk] at h⟩
    · obtain ⟨a, bs, v, x, -, -, -, rfl⟩ := ProA.next_ldCu0 hn
      exact ⟨fun _ _ => load_cu0_at hpre hX hS hT hg he hσ hL rfl hn,
        fun h => by simp [ProA.Site.afterSk] at h,
        fun h => by simp [ProA.Site.afterSk] at h⟩
    · obtain ⟨a, bs, v, x, -, -, -, rfl⟩ := ProA.next_ldCu1 hn
      exact ⟨fun _ _ => h0 (by simp) (by simp),
        fun _ => load_cu1_at hpre hX hS hT hg he hσ hL rfl hn,
        fun h => by simp [ProA.Site.afterSk] at h⟩
    · obtain ⟨a, bs, v, x, -, -, -, rfl⟩ := ProA.next_ldSk hn
      exact ⟨fun _ _ => h0 (by simp) (by simp), fun _ => h1 (Or.inr rfl),
        fun _ => load_sk_at hpre hX hS hT hg he hσ hL rfl hn⟩

/-- **The request words are the request's at every state of a thread**, given the launch bytes of
its earlier reads. -/
theorem wordsSo_all_at {g : Nat} :
    ∀ k s, St Q L X g k = some (some s) → (∀ j < k, Good Q L mem0 X (g, j)) →
      WordsSo Q L g s := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro s hσ hgood
  by_cases hinit : s = (code L Q g).init
  · subst hinit
    show WordsSo Q L g (if g % L.block < 128 then .d (DComp.code L g Q).init
      else .w (WComp.code L g Q).init)
    split <;> exact trivial
  · obtain ⟨k0, e, s0, hlt, he', hs0, hn⟩ := stateAt_pred hσ hinit
    have he : X.get (g, k0) = some e := he'
    have hg : g < L.threads := Frame.lt_of_get hX he
    have hI := ih k0 hlt s0 hs0 (fun j hj => hgood j (by omega))
    cases s0 with
    | w w0 =>
      rw [next_w] at hn
      obtain ⟨a, -, rfl⟩ := next_map_some hn
      exact trivial
    | d d0 =>
      rw [next_d] at hn
      obtain ⟨s1, hn1, rfl⟩ := next_map_some hn
      cases s1 with
      | dstart d1 => exact trivial
      | sm d1 => exact trivial
      | epi d1 => exact trivial
      | pro d1 =>
        cases d0 with
        | dstart ds =>
          have h' : DComp.dstartNext L g Q ds e = some (some (.pro d1)) := hn1
          unfold DComp.dstartNext at h'
          obtain ⟨d2, -, h2⟩ := next_map_some h'
          split_ifs at h2
          cases h2
          exact wordsSo_start g _ _
        | sm ds => exact absurd hn1 (next_sm_not_pro g Q ds e d1)
        | epi ds => exact absurd hn1 (next_epi_not_pro g Q ds e d1)
        | pro dp =>
          have h' : DComp.proNext L g Q dp e = some (some (.pro d1)) := hn1
          unfold DComp.proNext at h'
          by_cases hb : dp.site = ProA.Site.bar18
          · simp only [hb, ↓reduceIte] at h'
            split_ifs at h' <;> cases h'
          · simp only [hb, ↓reduceIte] at h'
            obtain ⟨d3, hd3, h3⟩ := next_map_some h'
            cases h3
            exact wordsSo_step_at hpre hX hS hT hg he hs0 (hgood k0 hlt).launch hI hd3

/-! ### The machine does not leave its run at the words -/

omit hpre hX hS hT in
/-- The thread machine's successor at a prologue state other than `bar18` is the prologue
machine's, mapped: it is not `some none` when the prologue machine's is not. -/
theorem next_pro_ne_of {g : Nat} {d : ProA.D} {e : Event} (hb : d.site ≠ ProA.Site.bar18)
    (h : ProA.next L g d e ≠ some none) :
    (threadCode L g Q).next (.d (.pro d)) e ≠ some none := by
  rw [next_d]
  change (DComp.proNext L g Q d e).map (Option.map TSt.d) ≠ some none
  unfold DComp.proNext
  simp only [hb, ↓reduceIte]
  intro h'
  apply h
  cases hh : ProA.next L g d e with
  | none => simp [hh] at h'
  | some o =>
    cases o with
    | none => rfl
    | some a => simp [hh] at h'

/-- **A word load's event reads the launch's word.** At a prologue state at one of the three
word loads, the event is a read of four bytes that are the bytes of the request's word
(`cu_seqlens_q[req]`, `cu_seqlens_q[req + 1]`, `seq_lens[req]`), given the launch bytes of the
read. -/
theorem pro_word_event {g k : Nat} {d : ProA.D} {e : Event} (hg : g < L.threads)
    (he : X.get (g, k) = some e) (hσ : St Q L X g k = some (some (.d (.pro d))))
    (hL : LaunchRead Q mem0 X (g, k)) (hs : d.site = .ldCu0 ∨ d.site = .ldCu1 ∨ d.site = .ldSk) :
    ∃ a bs x, e.kind = .rd a bs ∧ rebuild 3 bs = .ok (b32 x) ∧ ProA.word32 (b32 x) = some x ∧
      (d.site = .ldCu0 → x = Q.qStart (ProA.cta L g .z)) ∧
      (d.site = .ldCu1 → x = Q.qStart (ProA.cta L g .z + 1)) ∧
      (d.site = .ldSk → x = Q.seqK (ProA.cta L g .z)) := by
  obtain ⟨u, hF⟩ := fired_cont_at hX hS hT hg he hσ (by simp [ExitState])
  obtain ⟨bs, hlen, hev⟩ := ProA.shape_cu hpre hg (fired_pro hF) hs
  have hz := (ProA.cta_lt hpre hg).2.2
  have hb := hpre.bRange
  rcases hs with hs | hs | hs
  · simp only [hs, ite_true] at hev
    subst hev
    have hr := hpre.readsRange (Q.cuBase + 4 * ProA.cta L g .z + 3)
      (reads_cu (by omega) (by omega))
    have hA : (Q.cuBase + 4 * ProA.cta L g .z) % 2 ^ 64 = Q.cuBase + 4 * ProA.cta L g .z :=
      Nat.mod_eq_of_lt (by omega)
    rw [hA] at he
    have hx32 := qStart_lt32 hpre (r := ProA.cta L g .z) (by omega)
    have hbs := input_word_of_launch hX hL he (A := Q.cuBase + 4 * ProA.cta L g .z) rfl rfl
      (Q.qStart (ProA.cta L g .z))
      (fun j hj => ⟨reads_cu (by omega) hj, hpre.cuInput _ (by omega) j hj⟩)
    rw [hA]
    refine ⟨_, bs, _, rfl, ?_, ProA.word32_b32 hx32, fun _ => rfl,
      fun h => absurd (hs ▸ h) (by simp), fun h => absurd (hs ▸ h) (by simp)⟩
    rw [hbs]
    exact rebuild_b32 _
  · simp only [hs, reduceCtorEq, ite_false, ite_true] at hev
    subst hev
    have hr := hpre.readsRange (Q.cuBase + 4 * (ProA.cta L g .z + 1) + 3)
      (reads_cu (by omega) (by omega))
    have hA : (Q.cuBase + 4 * (ProA.cta L g .z + 1)) % 2 ^ 64 =
        Q.cuBase + 4 * (ProA.cta L g .z + 1) := Nat.mod_eq_of_lt (by omega)
    rw [hA] at he
    have hx32 := qStart_lt32 hpre (r := ProA.cta L g .z + 1) (by omega)
    have hbs := input_word_of_launch hX hL he (A := Q.cuBase + 4 * (ProA.cta L g .z + 1)) rfl rfl
      (Q.qStart (ProA.cta L g .z + 1))
      (fun j hj => ⟨reads_cu (by omega) hj, hpre.cuInput _ (by omega) j hj⟩)
    rw [hA]
    refine ⟨_, bs, _, rfl, ?_, ProA.word32_b32 hx32, fun h => absurd (hs ▸ h) (by simp),
      fun _ => rfl, fun h => absurd (hs ▸ h) (by simp)⟩
    rw [hbs]
    exact rebuild_b32 _
  · simp only [hs, reduceCtorEq, ite_false] at hev
    subst hev
    have hr := hpre.readsRange (Q.seqBase + 4 * ProA.cta L g .z + 3)
      (reads_seq (by omega) (by omega))
    have hA : (Q.seqBase + 4 * ProA.cta L g .z) % 2 ^ 64 = Q.seqBase + 4 * ProA.cta L g .z :=
      Nat.mod_eq_of_lt (by omega)
    have hsk := hpre.seqRange _ hz
    rw [hA] at he
    have hbs := input_word_of_launch hX hL he (A := Q.seqBase + 4 * ProA.cta L g .z) rfl rfl
      (Q.seqK (ProA.cta L g .z))
      (fun j hj => ⟨reads_seq hz hj, hpre.seqInput _ hz j hj⟩)
    rw [hA]
    refine ⟨_, bs, _, rfl, ?_, ProA.word32_b32 (by omega), fun h => absurd (hs ▸ h) (by simp),
      fun h => absurd (hs ▸ h) (by simp), fun _ => rfl⟩
    rw [hbs]
    exact rebuild_b32 _

/-- **The prologue's word loads and its exit to the softmax region do not leave the run.** At the
three word loads and at `bar18`, the thread machine's successor is not `some none`: the loaded
words are the launch's (`LaunchRead` at the load, `Good` at the thread's earlier events), they
satisfy `WordsOk` (`ProA.wordsOk_of_pre`), and at `bar18` they are the request's
(`wordsSo_all_at`). -/
theorem pro_words_next_ne {g k : Nat} {d : ProA.D} {e : Event} (hg : g < L.threads)
    (he : X.get (g, k) = some e) (hσ : St Q L X g k = some (some (.d (.pro d))))
    (hgood : ∀ j < k, Good Q L mem0 X (g, j)) (hL : LaunchRead Q mem0 X (g, k))
    (hs : d.site = .ldCu0 ∨ d.site = .ldCu1 ∨ d.site = .ldSk ∨ d.site = .bar18)
    (hw : d.site = .bar18 → ProA.wGood d.dt = true) :
    (threadCode L g Q).next (.d (.pro d)) e ≠ some none := by
  obtain ⟨site, dt⟩ := d
  simp only at hs hw
  rcases hs with hs | hs | hs | hs
  · subst hs
    obtain ⟨a, bs, x, hk, hrb, hw, -⟩ := pro_word_event hpre hX hS hT hg he hσ hL (Or.inl rfl)
    refine next_pro_ne_of (by simp) ?_
    simp [ProA.next, hk, hrb, hw]
  · subst hs
    obtain ⟨a, bs, x, hk, hrb, hw, -⟩ :=
      pro_word_event hpre hX hS hT hg he hσ hL (Or.inr (Or.inl rfl))
    refine next_pro_ne_of (by simp) ?_
    simp [ProA.next, hk, hrb, hw]
  · subst hs
    obtain ⟨a, bs, x, hk, hrb, hw, -, -, hx⟩ :=
      pro_word_event hpre hX hS hT hg he hσ hL (Or.inr (Or.inr rfl))
    have hx := hx rfl
    obtain ⟨h0, h1, -⟩ := wordsSo_all_at hpre hX hS hT k _ hσ hgood
    have hdef := treach_stateAt hpre hg hσ
    obtain ⟨hdef, tm, htm, hpro⟩ := hdef
    have ha : ProA.ArgsOk L g dt.pro := by
      simp only at hpro
      rw [hpro]
      exact DStart.argsOk_inh hpre hg hdef tm
    have hN : dt.pro.w71 = Q.splits := by
      simp only at hpro
      rw [hpro]
      exact Nat.mod_eq_of_lt (by have := hpre.splitsRange; omega)
    have hm : ProA.WordsMatch Q (ProA.cta L g .z) { dt with sk := x } :=
      ⟨h0 (by simp) (by simp), h1 (Or.inr rfl), hx⟩
    have hok := ProA.wordsOk_of_pre hpre hg (dt := { dt with sk := x }) ha hN hm
    refine next_pro_ne_of (by simp) ?_
    simp [ProA.next, hk, hrb, hw, hok]
  · subst hs
    obtain ⟨h0, h1, h2⟩ := wordsSo_all_at hpre hX hS hT k _ hσ hgood
    have hk : (ProA.Site.bar18).afterSk = true := by decide
    have hm : ProA.WordsMatch Q (ProA.cta L g .z) dt :=
      ⟨h0 (by simp) (by simp), h1 (Or.inl hk), h2 hk⟩
    rw [next_d]
    change (DComp.proNext L g Q ⟨.bar18, dt⟩ e).map (Option.map TSt.d) ≠ some none
    simp [DComp.proNext, hm, hw rfl]

/-! ### The query loads -/

omit hpre hX hS hT in
theorem ldq_afterSk {k : Nat} (hk : k < 64) : (ProA.ldqSite k).afterSk = true := by
  interval_cases k <;> rfl

omit hpre hX hS hT in
theorem bf16_toBytes (x : ℝ) : (Value.float .bf16 x).toBytes =
    [(Value.float .bf16 x).byteAt 0, (Value.float .bf16 x).byteAt 1] := by
  simp [Value.toBytes, Value.bytes, FloatFmt.bytes, List.range_succ]

omit hpre hX hS hT in
theorem bf16_bytes (x : ℝ) : (Value.float .bf16 x).bytes = 2 := by
  simp [Value.bytes, FloatFmt.bytes]

/-- **A query load returns the request's query element and the machine continues.** -/
theorem ldq_loaded_at {g k0 k : Nat} (hk : k < 64) {dt : ProA.Dat} {e : Event} (hg : g < L.threads)
    (he : X.get (g, k0) = some e)
    (hσ : St Q L X g k0 = some (some (.d (.pro ⟨ProA.ldqSite k, dt⟩))))
    (hgood : ∀ j < k0, Good Q L mem0 X (g, j)) (hL : LaunchRead Q mem0 X (g, k0)) :
    ∃ d', ProA.next L g ⟨ProA.ldqSite k, dt⟩ e = some (some d') ∧
      d'.dt.q k = Value.float .bf16 (Q.q (Q.qStart (ProA.cta L g .z) +
        (ProA.tidOf L g / 8 % 16 + 16 * (k / 16)) / 6)
        (ProA.cta L g .y * 6 + (ProA.tidOf L g / 8 % 16 + 16 * (k / 16)) % 6)
        (8 * (ProA.tidOf L g % 8) + 64 * (k % 16 / 8) + k % 8)) := by
  obtain ⟨u, hF⟩ := fired_cont_at hX hS hT hg he hσ (by simp [ExitState])
  have hF' := fired_pro hF
  obtain ⟨bs, hlen, hev⟩ := ProA.shape_ldq hk hF' rfl
  obtain ⟨t, ins, h, hinv, hc, hf'⟩ := ProA.fired_unpack hF'
  have hG : ProA.guardVal L g dt (ProA.ldqSite k) = true := hinv.guard
  obtain ⟨hdef, tm, htm, hpro⟩ := treach_stateAt hpre hg hσ
  have ha : ProA.ArgsOk L g dt.pro := by
    rw [hpro]
    exact DStart.argsOk_inh hpre hg hdef tm
  obtain ⟨h0, h1, h2⟩ := wordsSo_all_at hpre hX hS hT k0 _ hσ hgood
  have hsk : (ProA.ldqSite k).afterSk = true := ldq_afterSk hk
  have hne : ProA.ldqSite k ≠ .sMax ∧ ProA.ldqSite k ≠ .ldCu0 := by
    constructor <;> (intro h'; rw [h'] at hsk; simp [ProA.Site.afterSk] at hsk)
  have hm : ProA.WordsMatch Q (ProA.cta L g .z) dt :=
    ⟨h0 hne.1 hne.2, h1 (Or.inl hsk), h2 hsk⟩
  obtain ⟨hA, htok, hhead, hcol⟩ := ProA.ldq_spec hpre hg ha hm hk hG
  obtain ⟨hx, hy, hz⟩ := ProA.cta_lt hpre hg
  -- the two bytes of the read
  set x := Q.q (Q.qStart (ProA.cta L g .z) + (ProA.tidOf L g / 8 % 16 + 16 * (k / 16)) / 6)
    (ProA.cta L g .y * 6 + (ProA.tidOf L g / 8 % 16 + 16 * (k / 16)) % 6)
    (8 * (ProA.tidOf L g % 8) + 64 * (k % 16 / 8) + k % 8) with hxdef
  set A0 := ProA.loadAddr L g dt (ProA.ldqSite k) with hA0
  obtain ⟨acc, hacc⟩ : ∃ acc : Acc, acc = { loc := ⟨.global, 0, A0⟩, size := 2 } := ⟨_, rfl⟩
  have hev' : e = ⟨ProA.evPc (ProA.ldqSite k), .rd acc bs⟩ := by rw [hacc]; exact hev
  have hr : X.MemReads (.thread (g, k0)) acc bs := by
    rw [hev'] at he
    exact Or.inl ⟨_, he⟩
  have hbyte : ∀ j < 2, bs[j]? = some (some ((Value.float .bf16 x).byteAt j)) := by
    intro j hj
    have hrd : Q.reads (acc.loc.at j).addr := by
      have := ProA.ldq_reads hpre hg ha hm hk hG j hj
      rw [hacc]
      simpa [Loc.at] using this
    have he2 : X.get (g, k0) = some ⟨ProA.evPc (ProA.ldqSite k), .rd acc bs⟩ := by
      rw [hev'] at he
      exact he
    obtain ⟨c, hc1, hc2⟩ := hL _ acc bs he2 (by rw [hacc]) (by rw [hacc])
      j (by rw [hacc]; simpa using hj) hrd
    have hq := hpre.qInput _ hz _ htok _ hhead _ hcol j hj
    have hloc : (acc.loc.at j) = ⟨.global, 0, Q.qBase + 2 * ((Q.qStart (ProA.cta L g .z) +
        (ProA.tidOf L g / 8 % 16 + 16 * (k / 16)) / 6) * Q.strideQ +
        (ProA.cta L g .y * 6 + (ProA.tidOf L g / 8 % 16 + 16 * (k / 16)) % 6) * headDim +
        (8 * (ProA.tidOf L g % 8) + 64 * (k % 16 / 8) + k % 8)) + j⟩ := by
      rw [hacc]
      simp only [Loc.at]
      rw [hA]
    rw [hloc, hq] at hc1
    have := Option.some.inj (Option.some.inj hc1)
    rw [this]
    exact hc2
  have hbs : bs = (Value.float .bf16 x).toBytes.map some := by
    apply List.ext_getElem?
    intro j
    by_cases hj : j < 2
    · rw [hbyte j hj, bf16_toBytes]
      interval_cases j <;> simp
    · have h1 : bs[j]? = none := List.getElem?_eq_none (by omega)
      rw [h1, bf16_toBytes]
      simp
      omega
  have hrb : rebuild 3 bs = .ok (Value.float .bf16 x) := by
    rw [hbs]
    exact rebuild_scalar (by rw [bf16_bytes]; norm_num) rfl
  have hkind : e.kind = .rd acc bs := by rw [hev']
  obtain ⟨d', hn⟩ := ProA.next_ldq_some (L := L) (g := g) (dt := dt) hk hkind hrb (bf16_bytes x)
  refine ⟨d', hn, ?_⟩
  obtain ⟨a', bs', v, hk', hrb', -, hd⟩ := ProA.next_ldq hk hn
  rw [hkind] at hk'
  simp only [Kind.rd.injEq] at hk'
  obtain ⟨-, rfl⟩ := hk'
  rw [hrb] at hrb'
  have := Except.ok.inj hrb'
  rw [hd, ← this]
  simp [ProA.qUpd]


end
end PTX.Kernels.InklingRelDecode.Proof.Interface
