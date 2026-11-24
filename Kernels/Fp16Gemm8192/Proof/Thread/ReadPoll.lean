-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.PollRead
public import Kernels.Fp16Gemm8192.Proof.Thread.AccessAddr
public import Kernels.Fp16Gemm8192.Proof.Thread.PrologueIndex

@[expose] public section

/-! # A read of the response buffer follows a successful response poll

Each role reaches its response load only from its response wait, by a successful poll
(`clcLoad_prev`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

/-- Unfold a role's successor to the cases that reach a given site. -/
macro "prev_cases" h:ident hs:ident unf:ident : tactic => `(tactic| (
  unfold $unf at $h:ident
  split at $h:ident <;> (repeat' split at $h:ident)
  all_goals (try simp only [Option.some.injEq, Option.map_eq_some_iff] at $h:ident)
  all_goals (try obtain ⟨_, _, $h:ident⟩ := $h:ident)
  all_goals (try subst $h:ident)
  all_goals (try simp only [Loader.endOfTrip, Mma.endOfTrip, Scheduler.loopHead] at $hs:ident)
  all_goals (try split_ifs at $hs:ident)
  all_goals simp_all))

theorem Loader.clcLoad_prev {l l' : Loader.D} {e : Event} (h : Loader.next L g l e = some (some l'))
    (hs : l'.site = .clcLoad) : l.site = .clcWait ∧ ∃ m p acq sc, e.kind = .wait m p true acq sc :=
      by
  prev_cases h hs Loader.next

theorem Mma.clcLoad_prev {l l' : Mma.D} {e : Event} (h : Mma.next L g l e = some (some l'))
    (hs : l'.site = .clcLoad) : l.site = .clcWait ∧ ∃ m p acq sc, e.kind = .wait m p true acq sc :=
      by
  prev_cases h hs Mma.next

theorem Scheduler.clcLoad_prev {l l' : Scheduler.D} {e : Event}
    (h : Scheduler.next L g l e = some (some l')) (hs : l'.site = .clcLoad) :
    l.site = .clcWait ∧ ∃ m p acq sc, e.kind = .wait m p true acq sc := by
  prev_cases h hs Scheduler.next

theorem Consumer.clcLoad_prev {l l' : Consumer.D} {e : Event}
    (h : Consumer.next L g l e = some (some l')) (hs : l'.site = .clcLoad) :
    l.site = .clcWait ∧ ∃ m p acq sc, e.kind = .wait m p true acq sc := by
  prev_cases h hs Consumer.next

/-- The prologue reaches no response load. -/
theorem Prologue.not_clcLoad {p : Prologue.D} {e : Event} {d : ThreadD}
    (h : Prologue.next L g p e = some (some d)) (hd : d.AtClcLoad) : False := by
  unfold Prologue.next at h
  split at h <;> (repeat' split at h)
  all_goals (try simp only [Option.some.injEq] at h)
  all_goals (try subst h)
  all_goals (try simp only [ThreadD.AtClcLoad, Prologue.loaderStart, Prologue.loaderIdle,
    Prologue.mmaStart, Prologue.consStart, Prologue.schedStart] at hd)
  all_goals (try split_ifs at hd)
  all_goals simp_all

/-- **A thread reaches its response load only by a successful poll at its response wait.** -/
theorem clcLoad_prev {d0 d : ThreadD} {e : Event} (h : (code L g).next d0 e = some (some d))
    (hd : d.AtClcLoad) : d0.AtClcWait ∧ ∃ m p acq sc, e.kind = .wait m p true acq sc := by
  rcases d0 with p | (l | m | s | c)
  · exact (Prologue.not_clcLoad h hd).elim
  · rcases h1 : Loader.next L g l e with _ | _ | l'
    all_goals simp [code, h1] at h
    subst h
    exact Loader.clcLoad_prev h1 hd
  · rcases h1 : Mma.next L g m e with _ | _ | l'
    all_goals simp [code, h1] at h
    subst h
    exact Mma.clcLoad_prev h1 hd
  · rcases h1 : Scheduler.next L g s e with _ | _ | l'
    all_goals simp [code, h1] at h
    subst h
    exact Scheduler.clcLoad_prev h1 hd
  · rcases h1 : Consumer.next L g c e with _ | _ | l'
    all_goals simp [code, h1] at h
    subst h
    exact Consumer.clcLoad_prev h1 hd

/-- **A read follows a successful response poll**, unless it is the read of the Tensor Memory
base word. -/
theorem read_poll_fact {X : Execution} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Prod mem0 X) {k : Nat} {e : Event} {d : ThreadD} {a : Acc}
    {bs : List (Option Byte)} (hg : g < L.threads) (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (code L) X g k = some (some d)) (hk : e.kind = .rd a bs) :
    a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ ∨
      (0 < k ∧ ∃ pc p acq sc, X.get (g, k - 1) =
        some ⟨pc, .wait (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) p true acq sc⟩) := by
  obtain ⟨_, hfo⟩ := (Frame.trace (fun _ => sound hpre) hX hg).fired_at he hσ
  obtain ⟨t, ins, hat, -, hc, hf⟩ := Code.fired_site (sound hpre hg) hfo
  have hn := read_kind hc hf hk
  have hd : d.AtClcLoad ∨ a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ := by
    rcases d with p | (l | m | s | c)
    · cases hs : p.site <;> simp [nextKind, prologueKind, hs] at hn
    · left; cases hs : l.site <;> simp [nextKind, loaderKind, hs, ThreadD.AtClcLoad] at hn ⊢
    · left; cases hs : m.site <;> simp [nextKind, mmaKind, hs, ThreadD.AtClcLoad] at hn ⊢
    · left; cases hs : s.site <;> simp [nextKind, schedKind, hs, ThreadD.AtClcLoad] at hn ⊢
    · have hl : c.site = .clcLoad ∨ c.site = .ldBase := by
        cases hs : c.site <;> simp [nextKind, consKind, hs] at hn ⊢
      rcases hl with hl | hl
      · exact .inl hl
      · exact .inr (Consumer.ldBase_read hpre hl hat hc hf a bs hk).1
  rcases hd with hd | hd
  swap
  · exact .inl hd
  right
  rcases k with _ | k
  · rw [stateAt_zero] at hσ
    cases hσ
    exact hd.elim
  have hk' : k < (X.tr g).length := by
    have := len_of_get he
    simp only at this
    omega
  obtain ⟨e', he'⟩ : ∃ e', (X.tr g)[k]? = some e' := ⟨_, List.getElem?_eq_getElem hk'⟩
  rw [Frame.stateAt_succ he'] at hσ
  rcases hσk : Frame.stateAt (code L) X g k with _ | _ | d0
  · rw [hσk] at hσ; cases hσ
  · rw [hσk] at hσ; cases hσ
  rw [hσk] at hσ
  obtain ⟨hw, m0, p, acq, sc, hkw⟩ := clcLoad_prev hσ hd
  obtain ⟨t0, ins0, o0, hat0, hinv0, hc0, hf0⟩ := Frame.fired_site (fun _ => sound hpre) hX he' hσk
  obtain ⟨ok, acq', sc', rfl⟩ := clc_event hpre hinv0 hw hat0 hc0 hf0
  simp only at hkw
  obtain ⟨-, -, rfl, -, -⟩ := hkw
  exact ⟨by omega, _, _, _, _, he'⟩

end

end PTX.Kernels.Fp16Gemm8192.Proof
