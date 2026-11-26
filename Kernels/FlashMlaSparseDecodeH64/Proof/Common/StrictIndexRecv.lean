-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.StrictIndexOrigin
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.StrictIndexSrc
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.CollIxAt
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.CollWg1
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.View
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Index.Export.Nc
import Kernels.FlashMlaSparseDecodeH64.Proof.Index.StrictOperand

@[expose] public section

/-! # The words an index lane's shuffles receive are 32-bit

`ix_op`: the shuffle of an index lane's window sends a 32-bit word (the strict state before it
satisfies the tag invariant), given the window's well-formedness up to it (`ix_win`).
`ix_shRecv`: by induction on the number of shuffles before it, every shuffle of a window receives a
32-bit word: its source lane (`ix_shflSrc`) made the shuffle of the same instance, which sends a
32-bit word (`ix_op`, with fewer shuffles before its window events). -/

/-! # The events of an index lane's window are well formed

`ShRecv X c`: every shuffle of an index lane's window with fewer than `c` shuffles before it
receives a 32-bit word. `ix_evWf`: an event in the window is well formed (`IxWfT`) when the window
before it is and, if it is a shuffle, it receives a 32-bit word: the loads by the allocation of the
words they read (`index_ncWord`), the head's shuffle by the launch's warp word (`hsh_wf`).
`ix_win`: with `ShRecv X c`, the window of every lane up to a position with at most `c` shuffles
before it is well formed. -/

/-! # The head's shuffle of an index lane is well formed

`hsh_wf`: the head's shuffle of a lane whose warp is the index warp receives the launch's warp word
(`head_recv_follow`), which is the 32-bit word `7` (`IxWfT`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow Index

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- **The head's event at the shuffle state of an index lane is well formed.** -/
theorem hsh_wf (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hgate : subOk L g .index = true) {k : Nat} {e : Event} {n : Cls → Nat}
    (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (thread P L) X g k = some (some (hshState P L g n))) : IxWfT P e := by
  by_cases hub : ∀ f, e.kind ≠ .ub f
  · obtain ⟨σ, hσ', hJ, -, hev, -⟩ := ev_at hp hX hFw he hub
    rw [hσ] at hσ'
    obtain rfl := Option.some.inj (Option.some.inj hσ')
    have hg := Frame.lt_of_get hX he
    obtain ⟨-, hJ1, -, -⟩ := hJ
    change Wg1.HRef L g .hsh (n .shfl) at hJ1
    obtain ⟨hsh, hwg⟩ := hJ1
    obtain ⟨r, ok, hk⟩ := (show Wg1.Ev L g .hsh e from hev)
    have hc : Frame.cnt X Execution.isShfl g k = 2 := by
      rw [← hsh]
      exact (state_count hσ .shfl).symm
    have hr : r = w32 (warpW L g) := by
      obtain ⟨pc, kd⟩ := e
      simp only at hk
      subst hk
      exact head_recv_follow hp hX hFw he hc hwg
    have hw7 : warpOf L g = 7 := by simpa [subOk] using hgate
    refine ⟨⟨fun x bs h => ?_, fun _ x bs y h => ?_, fun md av bv cv recv ok' h => ?_⟩,
      fun md av bv cv recv ok' _ h => ?_⟩
    · rw [hk] at h; cases h
    · rw [hk] at h; cases h
    · rw [hk] at h
      obtain ⟨-, -, -, -, rfl, -⟩ := Kind.shfl.inj h
      exact ⟨_, hr⟩
    · rw [hk] at h
      obtain ⟨-, -, -, -, rfl, -⟩ := Kind.shfl.inj h
      refine ⟨_, hr, ?_⟩
      simp only [warpW, hw7]
      decide
  · obtain ⟨f, hf⟩ := not_forall.mp hub
    have hf := not_not.mp hf
    refine ⟨⟨fun x bs h => ?_, fun _ x bs y h => ?_, fun md av bv cv recv ok' h => ?_⟩,
      fun md av bv cv recv ok' _ h => ?_⟩ <;> rw [hf] at h <;> cases h

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow Index

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **The receive facts below `c`**: a shuffle of an index lane's window, with fewer than `c`
shuffles before it, receives a 32-bit word. -/
def ShRecv (P : Params) (L : Launch) (X : Execution) (c : Nat) : Prop :=
  ∀ (h k0 i : Nat) (n0 : Cls → Nat) (e : Event) (md : ShflMode) (a : Value) (b cc : Nat)
    (r : Value) (ok : Bool), h < L.threads → warpOf L h = 7 →
    Frame.stateAt (thread P L) X h k0 = some (some (hshState P L h n0)) → k0 < i →
    X.get (h, i) = some e → e.kind = .shfl md a b cc r ok →
    ((X.tr h).take i).countP Execution.isShfl < c → ∃ y, r = .bits 32 y

/-- **The window of lane `h` up to position `i`** is well formed. -/
def IxWin (P : Params) (X : Execution) (h k0 i : Nat) : Prop :=
  ∀ e ∈ ((X.tr h).drop k0).take (i - k0), IxWfT P e

theorem subOk_of_warp {h : Nat} (hw : warpOf L h = 7) : subOk L h .index = true := by
  simp [subOk, hw]

/-- **An event of the window is well formed** when the window before it is and, if it is a
shuffle, it receives a 32-bit word. -/
theorem ix_evWf (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {h k0 i : Nat} {n0 : Cls → Nat} (hh : h < L.threads)
    (hw : warpOf L h = 7)
    (hk0 : Frame.stateAt (thread P L) X h k0 = some (some (hshState P L h n0))) (hlt : k0 < i)
    {e : Event} (he : X.get (h, i) = some e) (hW : IxWin P X h k0 i)
    (hrecv : ∀ md a b cc r ok, e.kind = .shfl md a b cc r ok → ∃ y, r = .bits 32 y) :
    IxWfT P e := by
  have hgate := subOk_of_warp hw
  by_cases hub : ∀ f, e.kind ≠ .ub f
  · obtain ⟨σ, hσ, -⟩ := ev_at hp hX hFw he hub
    obtain ⟨hok, -⟩ := ix_windowAt hp hX hh hgate hk0 hlt hσ he hW
    rcases hok with ⟨-, n', rfl⟩ | ⟨d, n, rfl, -⟩
    · exact hsh_wf hp hX hFw hgate he hσ
    · obtain ⟨hev, -, -⟩ := ix_evAt hp hX hFw he hub hσ
      have hat : ∀ a bs, e.kind = .nc a bs → MbarRow.IndexAt L h e.pc := fun a bs hk =>
        ⟨hw, ix_pcRange hev (by rw [hk]; intro h'; cases h')⟩
      refine ⟨⟨fun a bs hk => (index_ncWord hp hX hFw he (hat a bs hk) hk).1,
        fun hpc a bs y hk hr hy => (index_ncWord hp hX hFw he (hat a bs hk) hk).2 hpc y hr hy,
        hrecv⟩, fun md av bv cv recv ok hpc hk => ?_⟩
      have := ix_shflPc hev (ix_shflSite hev hk)
      omega
  · obtain ⟨f, hf⟩ := not_forall.mp hub
    have hf := not_not.mp hf
    refine ⟨⟨fun x bs h => ?_, fun _ x bs y h => ?_, fun md av bv cv recv ok' h => ?_⟩,
      fun md av bv cv recv ok' _ h => ?_⟩ <;> rw [hf] at h <;> cases h

/-- The shuffle count before the next position. -/
theorem cnt_succ {es : List Event} {i : Nat} {e : Event} (he : es[i]? = some e) :
    (es.take (i + 1)).countP Execution.isShfl =
      (es.take i).countP Execution.isShfl + if Execution.isShfl e then 1 else 0 := by
  rw [List.take_add_one, he]
  simp [List.countP_append]

/-- **The window of an index lane is well formed** up to a position with at most `c` shuffles
before it, when every shuffle of a window with fewer than `c` before it receives a 32-bit word. -/
theorem ix_win (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {c : Nat} (hSR : ShRecv P L X c) {h k0 : Nat} {n0 : Cls → Nat}
    (hh : h < L.threads) (hw : warpOf L h = 7)
    (hk0 : Frame.stateAt (thread P L) X h k0 = some (some (hshState P L h n0))) :
    ∀ d, ((X.tr h).take (k0 + d)).countP Execution.isShfl ≤ c → IxWin P X h k0 (k0 + d) := by
  intro d
  induction d with
  | zero => intro _ e he; simp at he
  | succ d ih =>
    intro hc e hmem
    have hmono : ((X.tr h).take (k0 + d)).countP Execution.isShfl ≤
        ((X.tr h).take (k0 + (d + 1))).countP Execution.isShfl := by
      rw [← Nat.add_assoc, List.take_add_one]
      simp [List.countP_append]
    have hW := ih (le_trans hmono hc)
    rw [show k0 + (d + 1) - k0 = d + 1 by omega, List.take_add_one] at hmem
    rcases List.mem_append.mp hmem with hm | hm
    · exact hW e (by rwa [show k0 + d - k0 = d by omega])
    · have hge : (X.tr h)[k0 + d]? = some e := by
        rw [List.getElem?_drop] at hm
        cases hq : (X.tr h)[k0 + d]? with
        | none => rw [hq] at hm; simp at hm
        | some e' => rw [hq] at hm; simp at hm; rw [hm]
      have hge' : X.get (h, k0 + d) = some e := hge
      rcases Nat.eq_zero_or_pos d with rfl | hd
      · exact hsh_wf hp hX hFw (subOk_of_warp hw) (by simpa using hge') hk0
      · refine ix_evWf hp hX hFw hh hw hk0 (by omega) hge' hW ?_
        intro md a b cc r ok hk
        refine hSR h k0 (k0 + d) n0 e md a b cc r ok hh hw hk0 (by omega) hge' hk ?_
        have hs := cnt_succ hge
        have hc' : ((X.tr h).take (k0 + d + 1)).countP Execution.isShfl ≤ c := hc
        have : Execution.isShfl e = true := by obtain ⟨pc, kd⟩ := e; simp only at hk; subst hk; rfl
        simp [this] at hs
        omega

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow Index

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **A shuffle of an index lane's window sends a 32-bit word.** -/
theorem ix_op (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {c : Nat} (hSR : ShRecv P L X c) {h i k0 : Nat} {n0 : Cls → Nat}
    (hh : h < L.threads) (hw : warpOf L h = 7)
    (hk0 : Frame.stateAt (thread P L) X h k0 = some (some (hshState P L h n0))) (hlt : k0 < i)
    {e : Event} {md : ShflMode} {a : Value} {b cc : Nat} {r : Value} {ok : Bool} {d : Index.D}
    {n : Cls → Nat} (he : X.get (h, i) = some e) (hk : e.kind = .shfl md a b cc r ok)
    (hσ : Frame.stateAt (thread P L) X h i = some (some (idxState P L h d n)))
    (hc : ((X.tr h).take i).countP Execution.isShfl ≤ c) : ∃ y, a = .bits 32 y := by
  have hub : ∀ f, e.kind ≠ .ub f := fun f hf => by rw [hk] at hf; cases hf
  have hW := ix_win hp hX hFw hSR hh hw hk0 (i - k0) (by rwa [show k0 + (i - k0) = i by omega])
  rw [show k0 + (i - k0) = i by omega] at hW
  obtain ⟨-, t1, o', hgood, hq, hes⟩ :=
    ix_windowAt hp hX hh (subOk_of_warp hw) hk0 hlt hσ he hW
  obtain ⟨ins, hc', hf⟩ := Code.fired_of_good (thread_sound hp) hgood hes
  obtain ⟨hev, -, -⟩ := ix_evAt hp hX hFw he hub hσ
  have hsite := ix_shflSite hev hk
  have hse : Execution.isShfl e = true := by
    obtain ⟨pc, kd⟩ := e; simp only at hk; subst hk; rfl
  obtain ⟨-, -, -, -, hF⟩ := hgood.1
  obtain ⟨recv, ok', he'⟩ := ix_shflSends (P := P) hF hsite hc' hf hse
  rw [he'] at hk
  obtain ⟨-, rfl, -⟩ := Kind.shfl.inj hk
  exact ix_sendBits d.c hsite

theorem refW_le {g : Nat} {d : Startup.D} {sh : Nat} (h : Startup.RefW L g d sh) : sh ≤ 2 := by
  obtain ⟨site, x1, x2⟩ := d
  cases site with
  | sh j =>
    have := j.isLt
    simp only [Startup.RefW] at h
    omega
  | _ => simp only [Startup.RefW] at h; omega

/-- **Every shuffle of an index lane's window receives a 32-bit word.** -/
theorem ix_shRecv (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) : ∀ c, ShRecv P L X c := by
  intro c
  induction c with
  | zero =>
    intro h k0 i n0 e md a b cc r ok _ _ _ _ _ _ hcs
    exact absurd hcs (Nat.not_lt_zero _)
  | succ c ih =>
    intro h k0 i n0 e md a b cc r ok hh hw hk0 hlt he hk hcs
    rcases Nat.lt_or_ge (((X.tr h).take i).countP Execution.isShfl) c with hlt' | hge
    · exact ih h k0 i n0 e md a b cc r ok hh hw hk0 hlt he hk hlt'
    have hcc : ((X.tr h).take i).countP Execution.isShfl = c := by omega
    have hub : ∀ f, e.kind ≠ .ub f := fun f hf => by rw [hk] at hf; cases hf
    obtain ⟨σ, hσ, -⟩ := ev_at hp hX hFw he hub
    have hW := ix_win hp hX hFw ih hh hw hk0 (i - k0)
      (by rw [show k0 + (i - k0) = i by omega]; omega)
    rw [show k0 + (i - k0) = i by omega] at hW
    obtain ⟨hok, -⟩ := ix_windowAt hp hX hh (subOk_of_warp hw) hk0 hlt hσ he hW
    rcases hok with ⟨-, n', rfl⟩ | ⟨d, n, rfl, -⟩
    · exact (hsh_wf hp hX hFw (subOk_of_warp hw) he hσ).1.shfl md a b cc r ok hk
    · obtain ⟨pc, kd⟩ := e
      simp only at hk
      subst hk
      obtain ⟨hev, -, h3⟩ := ix_evAt hp hX hFw he hub hσ
      obtain ⟨j, pc', b', c', r', o', hsj, hG, hcs', hsT, hsW⟩ := ix_shflSrc hp hX hFw he hσ
      have hubs : ∀ f, (⟨pc', .shfl md r b' c' r' o'⟩ : Event).kind ≠ .ub f :=
        fun f hf => by cases hf
      obtain ⟨σs, hσs, -⟩ := ev_at hp hX hFw hsj hubs
      have hcnt : n .shfl = c := (state_count hσ .shfl).trans hcc
      rcases ix_cls2 hFw hsT hsW hσs with ⟨ds, ns, rfl, hRW, -⟩ | ⟨s, ns, rfl, -, hn2⟩ |
          ⟨ds, ns, rfl⟩
      · have h1 := refW_le hRW
        have h2 : ns .shfl = c := (state_count hσs .shfl).trans (hcs'.trans hcc)
        omega
      · have h2 : ns .shfl = c := (state_count hσs .shfl).trans (hcs'.trans hcc)
        omega
      · obtain ⟨k0', n0', hk0lt, hk0'⟩ := index_origin hσs
        exact ix_op hp hX hFw ih hsT hsW hk0' hk0lt hsj rfl hσs (by omega)

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
