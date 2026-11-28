-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.TraceBase

@[expose] public section

/-! # The data machine along the trace: the watched sites

The steps at the sites whose pcs are read as a block's words (`invW_sld`, `invW_vm`, `invW_pld`,
`invW_mld`, `invW_vote`) and the softmax-ready arrival (`invW_arrS`), and the invariant's step
(`invW_step`: every followed step keeps `InvW`) and start (`invW_init`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
open PTX PTX.Proof PTX.Flow PTX.Kernels.FlashMlaSparseDecodeH64

noncomputable section

variable {P : Params} {L : Launch} {g : Nat} {w : BitVec 64}

theorem invW_vm {l : List Event} {d : D} {c' : Control.D} {e : Event} (hI : InvW l d)
    (hs : d.c.site = .vm) (hpc : e.pc = d.c.site.pc)
    (hc : Control.succ P L g w d.c e = some (some c')) :
    InvW (l ++ [e]) (dataNext L d c' e) := by
  have hp : e.pc = 289 := by rw [hpc, hs]; rfl
  have hna : d.c.site ≠ .arrS := by rw [hs]; nofun
  have hn3 : ∀ k : Fin 8, d.c.site ≠ .pld k := fun k => by rw [hs]; nofun
  have hk : (∃ a bs, e.kind = .rd a bs) ∨ ∃ a bs, e.kind = .nc a bs := by
    simp only [Control.succ, hs, Control.dataRd] at hc
    split at hc
    · exact .inr ⟨_, _, ‹_›⟩
    · exact .inl ⟨_, _, ‹_›⟩
    · cases hc
  have hlo := hI.lo; have hhi := hI.hi; have hpm := hI.pm; have hvt := hI.vt
  have hmw := hI.mw
  have hpw : (w0Words ((w0Scan l).2 ++ [e])).pw = (w0Words (w0Scan l).2).pw :=
    w0Words_pw_miss _ _ (fun k hk => by rw [hp]; omega)
  simp only [w0Words] at hlo hhi hpm hvt hmw
  refine invW_gen hI hna hn3 (by rw [hp]; decide) (fun k hk => by rw [hp]; omega) hc
    ?_ ?_ ?_ ?_ ?_ ?_
  all_goals rcases hk with ⟨a, bs, hk⟩ | ⟨a, bs, hk⟩
  all_goals first
    | (simp only [record, hs, hk]; rw [hpw]; exact funext hI.pw)
    | simp [record, hs, hk, w0Words, w0Last_snoc, hp, w0RdVal, loadVal, hlo, hhi, hpm,
        hvt, hmw]

theorem invW_mld {l : List Event} {d : D} {c' : Control.D} {e : Event} (hI : InvW l d)
    (hs : d.c.site = .mld) (hpc : e.pc = d.c.site.pc)
    (hc : Control.succ P L g w d.c e = some (some c')) :
    InvW (l ++ [e]) (dataNext L d c' e) := by
  have hp : e.pc = 572 := by rw [hpc, hs]; rfl
  have hna : d.c.site ≠ .arrS := by rw [hs]; nofun
  have hn3 : ∀ k : Fin 8, d.c.site ≠ .pld k := fun k => by rw [hs]; nofun
  have hk : (∃ a bs, e.kind = .rd a bs) ∨ ∃ a bs, e.kind = .nc a bs := by
    simp only [Control.succ, hs, Control.dataRd] at hc
    split at hc
    · exact .inr ⟨_, _, ‹_›⟩
    · exact .inl ⟨_, _, ‹_›⟩
    · cases hc
  have hlo := hI.lo; have hhi := hI.hi; have hpm := hI.pm; have hvt := hI.vt
  have hmw := hI.mw
  have hpw : (w0Words ((w0Scan l).2 ++ [e])).pw = (w0Words (w0Scan l).2).pw :=
    w0Words_pw_miss _ _ (fun k hk => by rw [hp]; omega)
  simp only [w0Words] at hlo hhi hpm hvt hmw
  refine invW_gen hI hna hn3 (by rw [hp]; decide) (fun k hk => by rw [hp]; omega) hc
    ?_ ?_ ?_ ?_ ?_ ?_
  all_goals rcases hk with ⟨a, bs, hk⟩ | ⟨a, bs, hk⟩
  all_goals first
    | (simp only [record, hs, hk]; rw [hpw]; exact funext hI.pw)
    | simp [record, hs, hk, w0Words, w0Last_snoc, hp, w0RdVal, loadVal, hlo, hhi, hpm,
        hvt, hmw]

theorem invW_vote {l : List Event} {d : D} {c' : Control.D} {e : Event} (hI : InvW l d)
    (hs : d.c.site = .vote) (hpc : e.pc = d.c.site.pc)
    (hc : Control.succ P L g w d.c e = some (some c')) :
    InvW (l ++ [e]) (dataNext L d c' e) := by
  have hp : e.pc = 578 := by rw [hpc, hs]; rfl
  have hna : d.c.site ≠ .arrS := by rw [hs]; nofun
  have hn3 : ∀ k : Fin 8, d.c.site ≠ .pld k := fun k => by rw [hs]; nofun
  have hk : ∃ a b c r, e.kind = .voteMode a b c r := by
    simp only [Control.succ, hs] at hc
    split at hc
    · exact ⟨_, _, _, _, ‹_›⟩
    · cases hc
  have hlo := hI.lo; have hhi := hI.hi; have hpm := hI.pm; have hvt := hI.vt
  have hmw := hI.mw
  have hpw : (w0Words ((w0Scan l).2 ++ [e])).pw = (w0Words (w0Scan l).2).pw :=
    w0Words_pw_miss _ _ (fun k hk => by rw [hp]; omega)
  simp only [w0Words] at hlo hhi hpm hvt hmw
  refine invW_gen hI hna hn3 (by rw [hp]; decide) (fun k hk => by rw [hp]; omega) hc
    ?_ ?_ ?_ ?_ ?_ ?_
  all_goals obtain ⟨a, b, c, r, hk⟩ := hk
  all_goals first
    | (simp only [record, hs, hk]; rw [hpw]; exact funext hI.pw)
    | simp [record, hs, hk, w0Words, w0Last_snoc, hp, w0VoteOf, hlo, hhi, hpm,
        hmw]

theorem invW_sld {l : List Event} {d : D} {c' : Control.D} {e : Event} {a : Bool} {k : Fin 2}
    (hI : InvW l d) (hs : d.c.site = .sld a k) (hpc : e.pc = d.c.site.pc)
    (hc : Control.succ P L g w d.c e = some (some c')) :
    InvW (l ++ [e]) (dataNext L d c' e) := by
  have hna : d.c.site ≠ .arrS := by rw [hs]; nofun
  have hn3 : ∀ k : Fin 8, d.c.site ≠ .pld k := fun k => by rw [hs]; nofun
  have hk : ∃ x vals y, e.kind = .tc (.ld x vals y) := by
    have : ∀ s, Control.tcLoad e d.c s = some (some c') → ∃ x vals y, e.kind = .tc (.ld x vals y) :=
      fun s h => by
        unfold Control.tcLoad at h; split at h
        · exact ⟨_, _, _, ‹_›⟩
        · cases h
    fin_cases k <;> simp only [Control.succ, hs] at hc <;> exact this _ hc
  have hlo := hI.lo; have hhi := hI.hi; have hpm := hI.pm; have hvt := hI.vt
  have hmw := hI.mw
  simp only [w0Words] at hlo hhi hpm hvt hmw
  obtain ⟨x, vals, y, hk⟩ := hk
  fin_cases k <;> cases a <;>
  · have hp := hpc
    rw [hs] at hp
    simp [Site.pc] at hp
    have hpw : (w0Words ((w0Scan l).2 ++ [e])).pw = (w0Words (w0Scan l).2).pw :=
      w0Words_pw_miss _ _ (fun k hk => by rw [hp]; omega)
    refine invW_gen hI hna hn3 (by rw [hp]; decide) (fun k hk => by rw [hp]; omega) hc
      ?_ ?_ ?_ ?_ ?_ ?_
    all_goals first
      | (simp only [record, hs, hk]; rw [hpw]; exact funext hI.pw)
      | simp [record, hs, hk, sldLo, w0Words, w0Last_snoc, hp, w0TcVals, hlo, hhi, hpm, hvt, hmw]

theorem invW_pld {l : List Event} {d : D} {c' : Control.D} {e : Event} {k : Fin 8}
    (hI : InvW l d) (hs : d.c.site = .pld k) (hel : d.c.el < 2) (hpc : e.pc = d.c.site.pc)
    (hc : Control.succ P L g w d.c e = some (some c')) :
    InvW (l ++ [e]) (dataNext L d c' e) := by
  have hna : d.c.site ≠ .arrS := by rw [hs]; nofun
  have hp : e.pc = 477 + 5 * k.val := by rw [hpc, hs]; rfl
  have hk : ∃ a bs, e.kind = .rd a bs := by
    simp only [Control.succ, hs] at hc
    split at hc
    · exact ⟨_, _, ‹_›⟩
    · cases hc
  obtain ⟨a, bs, hk⟩ := hk
  have hrd : (w0RdVal e).isSome = true := by simp [w0RdVal, hk]
  have h1122 : e.pc ≠ w0ArrSPc := by rw [hp]; unfold w0ArrSPc; omega
  have hsc : (w0Scan (l ++ [e])).2 = (w0Scan l).2 ++ [e] := by
    simp [w0Scan_snoc, h1122]
  have hpf : ∀ j : Fin 8, w0Pf ((w0Scan l).2 ++ [e]) j =
      w0Pf (w0Scan l).2 j ++ (if j = k then [e] else []) := fun j => by
    rw [w0Pf_snoc]
    by_cases hj : j = k
    · subst hj; simp [hp, hrd]
    · have : e.pc ≠ 477 + 5 * j.val := fun h => hj (Fin.ext (by omega))
      simp [this, hj]
  have hlo := hI.lo; have hhi := hI.hi; have hpm := hI.pm; have hvt := hI.vt
  have hmw := hI.mw
  have hnot : ∀ p, p ∈ [278, 280, 283, 285, 289, 572, 578] → e.pc ≠ p := fun p hp' h' => by
    rw [hp] at h'; simp at hp'; omega
  have hww : ∀ f, f ∈ ["lo", "hi"] → True := fun _ _ => trivial
  have hlo' : (w0Words ((w0Scan l).2 ++ [e])).lo = (w0Words (w0Scan l).2).lo := by
    unfold w0Words; simp only [w0Last_snoc]
    have := hnot 280; have := hnot 283
    simp_all
  have hhi' : (w0Words ((w0Scan l).2 ++ [e])).hi = (w0Words (w0Scan l).2).hi := by
    unfold w0Words; simp only [w0Last_snoc]
    have := hnot 278; have := hnot 285
    simp_all
  have hmw' : (w0Words ((w0Scan l).2 ++ [e])).mw = (w0Words (w0Scan l).2).mw := by
    unfold w0Words; simp only [w0Last_snoc]
    have := hnot 289
    simp_all
  have hpm' : (w0Words ((w0Scan l).2 ++ [e])).pm = (w0Words (w0Scan l).2).pm := by
    unfold w0Words; simp only [w0Last_snoc]
    have := hnot 572
    simp_all
  have hvt' : (w0Words ((w0Scan l).2 ++ [e])).vt = (w0Words (w0Scan l).2).vt := by
    unfold w0Words; simp only [w0Last_snoc]
    have := hnot 578
    simp_all
  have hpwj : ∀ j : Nat, (w0Words ((w0Scan l).2 ++ [e])).pw j =
      if j = k.val then w0PeerOf (w0Pf (w0Scan l).2 k ++ [e]) else (w0Words (w0Scan l).2).pw j := by
    intro j
    unfold w0Words
    simp only [w0Peer_eq_pf]
    by_cases hj : j < 8
    · have := hpf ⟨j, hj⟩
      simp only [hj, ite_true] at this ⊢
      by_cases hjk : j = k.val
      · subst hjk
        have hjk' : (⟨k.val, hj⟩ : Fin 8) = k := Fin.ext rfl
        rw [hjk'] at this
        rw [this]; simp
      · have hjk' : (⟨j, hj⟩ : Fin 8) ≠ k := fun h => hjk (by rw [← h])
        simp only [hjk, ite_false]
        rw [this]; simp [hjk']
    · have : j ≠ k.val := by omega
      simp [hj, this]
  have hpar := hI.par k
  rw [dataNext_eq hna]
  have hcs : Control.succ P L g w d.c e = some (some (if d.c.el = 0 then
      { d.c with el := 1, a0 := (rebuild 3 bs).toOption.getD (.bits 64 0) }
      else { d.c with el := 0, a0 := .pred false, site :=
        [.pld 1, .pld 2, .pld 3, .pld 4, .pld 5, .pld 6, .pld 7].getD k.val .mst })) := by
    simp only [Control.succ, hs, hk]
    by_cases h0 : d.c.el = 0 <;> simp [h0]
  rw [hcs] at hc
  have hc' := Option.some.inj (Option.some.inj hc)
  subst hc'
  by_cases h0 : d.c.el = 0
  · simp only [h0, ite_true] at hc ⊢
    have hev : (w0Pf (w0Scan l).2 k).length % 2 = 0 := by
      have := hpar.not.mpr (fun h => by omega)
      omega
    refine ⟨?_, ?_, ?_, fun j => ?_, ?_, ?_, fun k' => ?_, fun k' h h1 => ?_⟩
    · simp only [record, hs, hk, h0, ite_true]; rw [hsc, hlo']; exact hlo
    · simp only [record, hs, hk, h0, ite_true]; rw [hsc, hhi']; exact hhi
    · simp only [record, hs, hk, h0, ite_true]; rw [hsc, hmw']; exact hmw
    · simp only [record, hs, hk, h0, ite_true]; rw [hsc, hpwj j]
      by_cases hj : j = k.val
      · simp only [hj, ite_true]
        rw [w0PeerOf_even_snoc _ _ hev]
        have := hI.pw k.val
        simp only [w0Words, w0Peer_eq_pf, k.isLt, ite_true] at this
        exact this
      · simp only [hj, ite_false]; exact hI.pw j
    · simp only [record, hs, hk, h0, ite_true]; rw [hsc, hpm']; exact hpm
    · simp only [record, hs, hk, h0, ite_true]; rw [hsc, hvt']; exact hvt
    · dsimp only; rw [hsc, hpf k']
      by_cases hj : k' = k
      · subst hj; simp [hs]; omega
      · simp only [hj, ite_false, List.append_nil]
        have hf : d.c.site ≠ .pld k' := fun h1 =>
          hj (by rw [hs] at h1; exact (Site.pld.inj h1).symm)
        exact (hI.par k').trans ⟨fun h => absurd h.1 hf, fun h => absurd h.1 hf⟩
    · dsimp only at h h1
      have hkk : k' = k := by rw [hs] at h; exact (Site.pld.inj h).symm
      subst hkk
      refine ⟨e, ?_, ?_⟩
      · rw [hsc, hpf]; simp
      · simp [w0A0, hk]
  · simp only [h0, ite_false] at hc ⊢
    have hel1 : d.c.el = 1 := by omega
    have hodd : (w0Pf (w0Scan l).2 k).length % 2 = 1 := hpar.mpr ⟨hs, hel1⟩
    obtain ⟨e0, hl0, ha0⟩ := hI.a0 k hs hel1
    have hrdv : (w0RdVal e).getD (.pred false) = loadVal bs := by simp [w0RdVal, hk, loadVal]
    have hlb : ∀ b : Blk, (record d.c e b).lo = b.lo ∧ (record d.c e b).hi = b.hi ∧
        (record d.c e b).mw = b.mw ∧ (record d.c e b).pm = b.pm ∧ (record d.c e b).vt = b.vt ∧
        (record d.c e b).pw = fun j => if j = k.val then (d.c.a0, loadVal bs) else b.pw j := by
      intro b; simp [record, hs, hk, h0]
    obtain ⟨q1, q2, q3, q4, q5, q6⟩ := hlb d.b
    refine ⟨?_, ?_, ?_, fun j => ?_, ?_, ?_, fun k' => ?_, fun k' h h1 => ?_⟩
    · rw [q1, hsc, hlo']; exact hlo
    · rw [q2, hsc, hhi']; exact hhi
    · rw [q3, hsc, hmw']; exact hmw
    · rw [q6, hsc, hpwj j]
      by_cases hj : j = k.val
      · simp only [hj, ite_true]
        rw [w0PeerOf_odd_snoc _ _ _ hodd hl0, hrdv, ha0]
      · simp only [hj, ite_false]; exact hI.pw j
    · rw [q4, hsc, hpm']; exact hpm
    · rw [q5, hsc, hvt']; exact hvt
    · dsimp only; rw [hsc, hpf k']
      by_cases hj : k' = k
      · subst hj; simp; omega
      · simp only [hj, ite_false, List.append_nil]
        have hf : d.c.site ≠ .pld k' := fun h1 =>
          hj (by rw [hs] at h1; exact (Site.pld.inj h1).symm)
        exact (hI.par k').trans ⟨fun h => absurd h.1 hf, fun h => absurd h.2 (by decide)⟩
    · exact absurd h1 (by simp)


theorem w0Words_nil : w0Words [] =
    ⟨[], [], Value.pred false, fun _ => (Value.pred false, Value.pred false), Value.pred false,
      false⟩ := by
  unfold w0Words
  simp [w0Last, w0Peer_eq_pf, w0PeerOf, w0Pf, lastN]

theorem invW_arrS {l : List Event} {d : D} {c' : Control.D} {e : Event} (_hI : InvW l d)
    (hs : d.c.site = .arrS) (hpc : e.pc = d.c.site.pc)
    (hc : Control.succ P L g w d.c e = some (some c')) :
    InvW (l ++ [e]) (dataNext L d c' e) := by
  have hp : e.pc = w0ArrSPc := by rw [hpc, hs]; rfl
  have hsc : (w0Scan (l ++ [e])).2 = [] := by simp [w0Scan_snoc, hp]
  have hsite : c'.site = .bar0 ∨ c'.site = .ebar0 := by
    simp only [Control.succ, hs] at hc
    split at hc
    · cases hc; exact .inl rfl
    · cases hc; exact .inr rfl
  have hn : ∀ k : Fin 8, c'.site ≠ .pld k := fun k h => by
    rcases hsite with h' | h' <;> rw [h'] at h <;> cases h
  simp only [dataNext, hs]
  refine ⟨?_, ?_, ?_, fun j => ?_, ?_, ?_, fun k => ?_, fun k h _ => absurd h (hn k)⟩
  · rw [hsc, w0Words_nil]
  · rw [hsc, w0Words_nil]
  · rw [hsc, w0Words_nil]
  · rw [hsc, w0Words_nil]
  · rw [hsc, w0Words_nil]
  · rw [hsc, w0Words_nil]
  · rw [hsc]; simp [w0Pf, hn k]

/-- **A followed step keeps the invariant.** -/
theorem invW_step {l : List Event} {d : D} {c' : Control.D} {e : Event} (hI : InvW l d)
    (hel : d.c.el < Control.elems d.c.site) (hpc : e.pc = d.c.site.pc)
    (hc : Control.succ P L g w d.c e = some (some c')) :
    InvW (l ++ [e]) (dataNext L d c' e) := by
  by_cases hw : w0Watched d.c.site.pc = true
  · rcases w0Site_watched _ hw with ⟨a, k, hs⟩ | hs | ⟨k, hs⟩ | hs | hs | hs
    · exact invW_sld hI hs hpc hc
    · exact invW_vm hI hs hpc hc
    · refine invW_pld hI hs ?_ hpc hc
      rw [hs] at hel; simpa [Control.elems] using hel
    · exact invW_mld hI hs hpc hc
    · exact invW_vote hI hs hpc hc
    · exact invW_arrS hI hs hpc hc
  · exact invW_unwatched hI hpc (by simpa using hw) hc

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
