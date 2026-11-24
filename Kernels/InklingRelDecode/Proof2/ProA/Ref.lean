-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof2.ProA.Steps
public import Kernels.InklingRelDecode.Proof.Thread.ClassBt
public import Kernels.InklingRelDecode.Proof2.Startup.Base
public import Lemmas.Flow.AllocTmpl

@[expose] public section

/-! # The prologue's reference invariant and its step (`ref_next`)

**Reference** (`PRef`): the inherited registers are the launch's with base word 0, the request
words the state has loaded are the request's (`WordsF`: `cu_seqlens_q[req]` from the second load
on, `cu_seqlens_q[req + 1]` from the third, `seq_lens[req]` after it; `req = ctaid.z`), and the
gate of the preloaded blocks (`Proof.ProA.Gate`: a block's sites are entered only where the
block is preloaded). Both are stated of the flat state `d.old`, so the flat machine's
preservation lemmas apply (`keeps_next`, `afterSk_next`, `gate_next`).

**Expectation** (`Expect`): what the event of a state returns for the reference to continue. A
request-word load returns the bytes of the request's word, a block-table load the bytes of a
32-bit word, a query load two bytes. The execution layer (`Ref/Pro.lean`) proves it from the
read-only input source.

**`ref_next`**: under `PRef` and `Expect` the machine does not stop, and every successor holds
`PRef`. The only stops of the flat successor are the kinds of loaded values and its last barrier
(`flat_stop`), which `next` replaces by the exit. -/

namespace PTX.Kernels.InklingRelDecode.Proof2.ProA
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.InklingRelDecode
open PTX.Kernels.InklingRelDecode.Proof.ProA (Dat Inh cta word32 word32_b32 Gate)

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {m : Mem0} {g : Nat}

/-! ### The flat successor: where it stops, what it keeps -/

/-- The word loads (request and block-table words). -/
def Site.isWord : Site → Bool
  | .ld _ | .lb _ _ => true
  | _ => false

/-- The query loads. -/
def Site.isQ : Site → Bool
  | .ldq _ => true
  | _ => false

/-- **Where the flat successor stops**: at its last barrier, and at a load whose bytes do not
rebuild or whose value has another kind than the site's (other than the third request word,
whose content test `next0` does not take). -/
theorem flat_stop {s : OSite} {dt : Dat} {e : Event} (hs : s ≠ .ldSk)
    (h : Proof.ProA.next L g ⟨s, dt⟩ e = some none) :
    s = .bar18 ∨ ∃ a bs, e.kind = .rd a bs ∧
      (((Site.ofOld s).isLoad = true ∧ ∃ f, rebuild 3 bs = .error f) ∨
        ∃ v, rebuild 3 bs = .ok v ∧ (((Site.ofOld s).isWord = true ∧ word32 v = none) ∨
          ((Site.ofOld s).isQ = true ∧ v.bytes ≠ 2))) := by
  cases s <;> first
    | exact absurd rfl hs
    | exact .inl rfl
    | (simp only [Proof.ProA.next] at h
       repeat' split at h
       all_goals first
         | (cases h; done)
         | exact .inr ⟨_, _, ‹_›, .inl ⟨rfl, _, ‹_›⟩⟩
         | exact .inr ⟨_, _, ‹_›, .inr ⟨_, ‹_›, .inl ⟨rfl, ‹_›⟩⟩⟩
         | exact .inr ⟨_, _, ‹_›, .inr ⟨_, ‹_›, .inr ⟨rfl, ‹_›⟩⟩⟩)

/-- **The flat successor keeps the inherited registers.** -/
theorem flat_pro {s : OSite} {dt : Dat} {e : Event} {d' : Proof.ProA.D}
    (h : Proof.ProA.next L g ⟨s, dt⟩ e = some (some d')) : d'.dt.pro = dt.pro := by
  cases s <;>
    (simp only [Proof.ProA.next] at h
     repeat' split at h
     all_goals first
       | (cases h; done)
       | (simp only [Option.some.injEq] at h; subst h
          simp [Proof.ProA.elDt, Proof.ProA.qUpd]))

/-- **The flat successor keeps the base word register.** -/
theorem flat_w {s : OSite} {dt : Dat} {e : Event} {d' : Proof.ProA.D}
    (h : Proof.ProA.next L g ⟨s, dt⟩ e = some (some d')) : d'.dt.w = dt.w := by
  cases s <;>
    (simp only [Proof.ProA.next] at h
     repeat' split at h
     all_goals first
       | (cases h; done)
       | (simp only [Option.some.injEq] at h; subst h
          simp [Proof.ProA.elDt, Proof.ProA.qUpd]))

theorem ofOld_old (s : Site) (hx : s ≠ .exit) : Site.ofOld s.old = s := by
  cases s with
  | ld k | el k | init k | arr k | psh k | ldq k | st9 k => fin_cases k <;> rfl
  | pb b j | lb b j | pel b j | ptc b j | stq b j => fin_cases b <;> fin_cases j <;> rfl
  | exit => exact absurd rfl hx
  | _ => rfl

/-! ### The reference invariant -/

/-- The request's words: `cu_seqlens_q[req]`, `cu_seqlens_q[req + 1]`, `seq_lens[req]`. -/
def reqWord (Q : Params) (L : Launch) (g : Nat) : Fin 3 → Nat
  | 0 => Q.qStart (cta L g .z)
  | 1 => Q.qStart (cta L g .z + 1)
  | 2 => Q.seqK (cta L g .z)

theorem reqWord_lt (hpre : Pre Q L m) (hg : g < L.threads) (k : Fin 3) :
    reqWord Q L g k < 2 ^ 32 := by
  have hz := (Proof.ProA.cta_lt hpre hg).2.2
  have h1 := Proof.qStart_mono hpre (r := cta L g .z) (r' := Q.b) (by omega) le_rfl
  have h1' := Proof.qStart_mono hpre (r := cta L g .z + 1) (r' := Q.b) (by omega) le_rfl
  have h2 := hpre.cuEnd
  have h3 := hpre.nTokRange
  have h4 := hpre.seqRange _ hz
  fin_cases k <;> simp only [reqWord] <;> omega

/-- The request words a flat state has loaded are the request's. -/
def WordsF (Q : Params) (L : Launch) (g : Nat) (fd : Proof.ProA.D) : Prop :=
  (fd.site ≠ .sMax → fd.site ≠ .ldCu0 → fd.dt.cu0 = reqWord Q L g 0) ∧
  ((fd.site.afterSk = true ∨ fd.site = .ldSk) → fd.dt.cu1 = reqWord Q L g 1) ∧
  (fd.site.afterSk = true → fd.dt.sk = reqWord Q L g 2)

/-- **The prologue's reference invariant.** -/
structure PRef (Q : Params) (L : Launch) (g tm : Nat) (w0 : Value) (d : D) : Prop where
  pro : d.dt.pro = Startup.inh L g Q tm
  words : WordsF Q L g d.old
  gate : Gate L g d.site.old d.dt
  /-- The base word register holds the value the startup's load returned. -/
  w : d.dt.w = w0

/-- The block-table index of word `h` of preloaded block `b`. -/
def btIdx (Q : Params) (L : Launch) (g : Nat) (b : Fin 3) (h : Fin 2) : Nat :=
  2 * (cta L g .x + b.val * Q.splits) + h.val

/-- **What an event must return** for the reference to continue. -/
def Expect (Q : Params) (L : Launch) (g : Nat) (d : D) (e : Event) : Prop :=
  match d.site with
  | .ld k => ∀ a bs, e.kind = .rd a bs → bs = (b32 (reqWord Q L g k)).toBytes.map some
  | .lb _ _ => ∃ x < 2 ^ 32, ∀ a bs, e.kind = .rd a bs → bs = (b32 x).toBytes.map some
  | .ldq _ => ∀ a bs, e.kind = .rd a bs → bs.length = 2
  | _ => True

/-- The flat early sites are in no block. -/
theorem gate_early {s : OSite} (dt : Dat)
    (hs : s = .sMax ∨ s = .ldCu0 ∨ s = .ldCu1 ∨ s = .ldSk ∨ s = .el0) : Gate L g s dt := by
  rcases hs with rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨fun h => absurd h (by decide), fun h => absurd h (by decide),
      fun h => absurd h (by decide)⟩

theorem pref_init {tm : Nat} {w0 : Value} (P : Inh) (hP : P = Startup.inh L g Q tm) :
    PRef Q L g tm w0 (init P w0) := by
  refine ⟨hP, ⟨fun h => absurd rfl h, fun h => ?_, fun h => ?_⟩, ?_, ?_⟩
  · simp [init, D.old, Site.old, Proof.ProA.Site.afterSk] at h
  · simp [init, D.old, Site.old, Proof.ProA.Site.afterSk] at h
  · exact gate_early _ (.inl rfl)
  · subst hP; rfl

/-! ### The step -/

theorem rebuild_word {x : Nat} (hx : x < 2 ^ 32) {bs : List (Option Byte)}
    (h : bs = (b32 x).toBytes.map some) : ∃ v, rebuild 3 bs = .ok v ∧ word32 v = some x :=
  ⟨b32 x, by rw [h]; exact rebuild_b32 x, word32_b32 hx⟩

/-- **A flat step keeps the words and the gate**, given what a request-word load returns. -/
theorem flat_keep (hpre : Pre Q L m) (hg : g < L.threads) {s : OSite} {dt : Dat} {e : Event}
    {fd : Proof.ProA.D} (hs : s ≠ .ldSk) (hW : WordsF Q L g ⟨s, dt⟩) (hG : Gate L g s dt)
    (hE : ∀ k : Fin 2, s = [Proof.ProA.Site.ldCu0, .ldCu1].getD k .sMax →
      ∀ a bs, e.kind = .rd a bs → bs = (b32 (reqWord Q L g ⟨k, by omega⟩)).toBytes.map some)
    (h : Proof.ProA.next L g ⟨s, dt⟩ e = some (some fd)) :
    WordsF Q L g fd ∧ Gate L g fd.site fd.dt := by
  obtain ⟨h0, h1, h2⟩ := hW
  by_cases hk : s.afterSk = true
  · obtain ⟨kc0, kc1, ks⟩ := Proof.ProA.keeps_next h hk
    have hs' := Proof.ProA.afterSk_next h hk
    have hne : s ≠ .sMax ∧ s ≠ .ldCu0 := by
      constructor <;> (rintro rfl; simp [Proof.ProA.Site.afterSk] at hk)
    refine ⟨⟨fun _ _ => ?_, fun _ => ?_, fun _ => ?_⟩, Proof.ProA.gate_next h hG hk⟩
    · rw [kc0]; exact h0 hne.1 hne.2
    · rw [kc1]; exact h1 (.inl hk)
    · rw [ks]; exact h2 hk
  · have hs3 : s = .sMax ∨ s = .ldCu0 ∨ s = .ldCu1 := by
      cases s <;> simp_all [Proof.ProA.Site.afterSk]
    rcases hs3 with rfl | rfl | rfl
    · rw [Proof.ProA.next_sMax h]
      exact ⟨⟨fun _ h => absurd rfl h, fun h => by simp [Proof.ProA.Site.afterSk] at h,
        fun h => by simp [Proof.ProA.Site.afterSk] at h⟩, gate_early _ (by simp)⟩
    · obtain ⟨a, bs, v, x, he, hv, hw, rfl⟩ := Proof.ProA.next_ldCu0 h
      obtain ⟨v', hv', hw'⟩ := rebuild_word (reqWord_lt hpre hg 0) (hE 0 rfl a bs he)
      rw [hv] at hv'
      cases hv'
      rw [hw] at hw'
      cases hw'
      exact ⟨⟨fun _ _ => rfl, fun h => by simp [Proof.ProA.Site.afterSk] at h,
        fun h => by simp [Proof.ProA.Site.afterSk] at h⟩, gate_early _ (by simp)⟩
    · obtain ⟨a, bs, v, x, he, hv, hw, rfl⟩ := Proof.ProA.next_ldCu1 h
      obtain ⟨v', hv', hw'⟩ := rebuild_word (reqWord_lt hpre hg 1) (hE 1 rfl a bs he)
      rw [hv] at hv'
      cases hv'
      rw [hw] at hw'
      cases hw'
      exact ⟨⟨fun _ _ => h0 (by simp) (by simp), fun _ => rfl,
        fun h => by simp [Proof.ProA.Site.afterSk] at h⟩, gate_early _ (by simp)⟩

/-- The successor `next0` away from the third request word, the last barrier and the exit is the
flat one, regrouped. -/
theorem next0_flat {s : Site} {dt : Dat} {e : Event} (h1 : s ≠ .bar18) (h2 : s ≠ .exit)
    (h3 : s ≠ .ld 2) {o : Option D} (h : next0 L g ⟨s, dt⟩ e = some o) :
    Proof.ProA.next L g ⟨s.old, dt⟩ e = some (o.map D.old) := by
  rw [next_old dt h1 h2 h3, h]
  rfl

/-- **The prologue's step under its reference**: the machine does not stop, and its successor
holds the reference. -/
theorem ref_next (hpre : Pre Q L m) (hg : g < L.threads) {d : D} {e : Event}
    {tm : Nat} {w0 : Value} (hR : PRef Q L g tm w0 d) (hE : Expect Q L g d e)
    (hx : d.site ≠ .exit) :
    next L g d e ≠ some none ∧ ∀ d', next L g d e = some (some d') → PRef Q L g tm w0 d' := by
  obtain ⟨s, dt⟩ := d
  obtain ⟨hpro, hW, hG, hw0⟩ := hR
  by_cases hk : kill ⟨s, dt⟩ e = true
  · simp [next, hk]
  have hn : next L g ⟨s, dt⟩ e = next0 L g ⟨s, dt⟩ e := by simp [next, hk]
  rw [hn]
  by_cases hl : s = .ld 2
  · subst hl
    have hE' : ∀ a bs, e.kind = .rd a bs → bs = (b32 (reqWord Q L g 2)).toBytes.map some := hE
    obtain ⟨pc, kd⟩ := e
    cases kd with
    | rd a bs =>
      obtain ⟨v, hv, hw⟩ := rebuild_word (reqWord_lt hpre hg 2) (hE' a bs rfl)
      refine ⟨?_, fun d' h => ?_⟩
      · simp only [next0, hv, hw]; split <;> simp
      · simp only [next0, hv, hw] at h
        split at h
        · simp only [Option.some.injEq] at h
          subst h
          obtain ⟨h0, h1, -⟩ := hW
          refine ⟨hpro, ⟨fun _ _ => h0 (by simp [D.old, Site.old]) (by simp [D.old, Site.old]),
            fun _ => h1 (.inr rfl),
            fun _ => rfl⟩, gate_early _ (by simp [Site.old, elOld]), hw0⟩
        · cases h
    | _ => exact ⟨by simp [next0], fun d' h => by simp [next0] at h⟩
  by_cases hb : s = .bar18
  · subst hb
    refine ⟨by simp [next0], fun d' h => ?_⟩
    simp only [next0, Option.some.injEq] at h
    subst h
    exact ⟨hpro, hW, hG, hw0⟩
  have hso : s.old ≠ .ldSk := fun h => hl (by rw [← ofOld_old s hx, h]; rfl)
  refine ⟨fun h => ?_, fun d' h => ?_⟩
  · have hf := next0_flat hb hx hl h
    rcases flat_stop hso hf with h' | ⟨a, bs, he, ⟨hld, f, hf'⟩ | ⟨v, hv, ⟨hw, hv'⟩ | ⟨hq, hv'⟩⟩⟩
    · exact hb (by rw [← ofOld_old s hx, h']; rfl)
    · rw [ofOld_old s hx] at hld
      simp [kill, hld, he, hf'] at hk
    · rw [ofOld_old s hx] at hw
      cases s with
      | ld k =>
        obtain ⟨v', hv'', hw'⟩ := rebuild_word (reqWord_lt hpre hg k) (hE a bs he)
        rw [hv] at hv''
        cases hv''
        rw [hv'] at hw'
        cases hw'
      | lb b j =>
        obtain ⟨x, hx32, hx⟩ := hE
        obtain ⟨v', hv'', hw'⟩ := rebuild_word hx32 (hx a bs he)
        rw [hv] at hv''
        cases hv''
        rw [hv'] at hw'
        cases hw'
      | _ => simp [Site.isWord] at hw
    · rw [ofOld_old s hx] at hq
      cases s with
      | ldq k =>
        have hlen : bs.length = 2 := hE a bs he
        exact hv' (by rw [rebuild_bytes_eq_length 3 bs v hv, hlen])
      | _ => simp [Site.isQ] at hq
  · have hf := next0_flat hb hx hl h
    simp only [Option.map_some] at hf
    have hE2 : ∀ k : Fin 2, s.old = [Proof.ProA.Site.ldCu0, .ldCu1].getD k .sMax →
        ∀ a bs, e.kind = .rd a bs →
          bs = (b32 (reqWord Q L g ⟨k, by omega⟩)).toBytes.map some := by
      intro k hk' a bs he
      have hs' : s = .ld ⟨k, by omega⟩ := by
        rw [← ofOld_old s hx, hk']
        fin_cases k <;> rfl
      subst hs'
      exact hE a bs he
    obtain ⟨hw, hg'⟩ := flat_keep hpre hg hso hW hG hE2 hf
    exact ⟨(flat_pro hf).trans hpro, hw, hg', (flat_w hf).trans hw0⟩

end
end PTX.Kernels.InklingRelDecode.Proof2.ProA
