-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Result.OutStore
public import Kernels.InklingRelDecode.Proof.Result.OutIssued
public import Lemmas.Kernel.IdenticalWrites
public import Lemmas.Tcgen05.MemFloat
public import Lemmas.Kernel.Goals

@[expose] public section

/-!
# `Post` from the stores' values (result layer, part 2e)

`result_goal`: a complete execution's final memory satisfies `Spec.Post`, from `Inputs`.

* Every write of a global byte is a thread's store (`global_write_thread`), so the writers of a
  byte are among the events of the launch's threads (`allWrites`).
* A byte of `OPart[split, token, head, d]` or `LsePart[split, token, head]` has a writer
  (`OutIssued.exists_oStore`, `exists_lseStore`), and every writer of it stores the same word
  (`write_spec`; distinct output words do not overlap, `oLoc_overlap`, `lseLoc_overlap`,
  `oLoc_lseLoc_apart`; the tokens of distinct requests are distinct, `token_unique`). So the
  final memory holds that byte of the word (`IsFinal.of_agree`).
* The word is the f32 float of `Spec.oPart` (`oWord`), or the zero word when the split has no
  block, which is also `oPart`; of `Spec.lsePart`, or the `-inf` pattern for an empty row.
* The last conjunct of `Post` is `ThreadFacts.post_frame`.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Result.Out
open PTX PTX.Proof PTX.Flow PTX.Assumption PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Result.Mma PTX.TcMma
open Classical

noncomputable section

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-! ### The requests' tokens are distinct -/

/-- **A token belongs to one request.** -/
theorem token_unique (hpre : Pre Q L mem0) {r r' tok tok' : Nat} (hr : r < Q.b) (hr' : r' < Q.b)
    (ht : tok < Q.qLen r) (ht' : tok' < Q.qLen r') (h : Q.qStart r + tok = Q.qStart r' + tok') :
    r = r' ∧ tok = tok' := by
  have key : ∀ {a a' u u' : Nat}, a < a' → a < Q.b → a' < Q.b → u < Q.qLen a →
      Q.qStart a + u = Q.qStart a' + u' → False := by
    intro a a' u u' hlt ha ha' hu he
    have h1 := qStart_le hpre ha
    have h2 := qStart_mono hpre (r := a + 1) (r' := a') (by omega) (by omega)
    omega
  rcases Nat.lt_trichotomy r r' with hlt | rfl | hgt
  · exact (key hlt hr hr' ht h).elim
  · exact ⟨rfl, by omega⟩
  · exact (key hgt hr' hr ht' h.symm).elim

/-! ### The writers of a byte -/

/-- The thread writes of the launch: every event of every thread. -/
def allWrites (L : Launch) (X : Execution) : List AsyncCopy.Ref :=
  (List.range L.threads).flatMap fun g =>
    (List.range (X.tr g).length).map fun n => AsyncCopy.Ref.thread (g, n)

/-- **A write of a global byte is one of the launch's thread writes.** -/
theorem mem_allWrites (hX : Consistent L kernel Assumptions.all mem0 X) {w : AsyncCopy.Ref}
    {a : Acc} {bs : List Byte} (hw : X.MemWrites w a bs) (hsp : a.loc.space = .global) :
    w ∈ allWrites L X := by
  obtain ⟨g, n, pc, rfl, hget⟩ := Interface.global_write_thread hX hw hsp
  have hg := Frame.lt_of_get hX hget
  have hn := (List.getElem?_eq_some_iff.mp hget).1
  exact List.mem_flatMap.mpr ⟨g, List.mem_range.mpr hg,
    List.mem_map.mpr ⟨n, List.mem_range.mpr hn, rfl⟩⟩

/-- A store's bytes, at a byte of its word. -/
theorem wbyte_word (l : Loc) (v : Value) {z : Nat} (hz : z < v.bytes) :
    wbyte (EvD.wordAcc l) v.toBytes (l.at z) = some (v.byteAt z) := by
  simp [wbyte, EvD.wordAcc, Loc.at, Value.toBytes, hz]

theorem covers_word {l : Loc} {z : Nat} (hz : z < 4) : (EvD.wordAcc l).Covers (l.at z) := by
  simp only [EvD.wordAcc, Acc.Covers, Loc.InRange, Loc.at]
  exact ⟨trivial, trivial, by omega, by omega⟩

/-! ### The final memory at the bytes of an output word -/

/-- **A byte of `OPart` of a valid row holds the byte of its word**: the final memory has, at
byte `z` of `OPart[split, token, head, dc]`, byte `z` of `oWord`. -/
theorem final_oByte (hpre : Pre Q L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hcomp : Complete L X) (hin : Inputs Q L mem0 X) {m : FinalMem} (hfin : IsFinal L mem0 X m)
    {r s tok head dc z : Nat} (hr : r < Q.b) (hs : s < Q.splits) (ht : tok < Q.qLen r)
    (hh : head < heads) (hd : dc < headDim) (hz : z < 4) :
    m ((oLoc Q s (Q.qStart r + tok) head dc).at z) =
      some (some ((oWord Q r s tok head dc).byteAt z)) := by
  have htk := token_lt hpre hr ht
  have hf := Interface.threadFacts hpre hin.smOb hX hin.premises
  obtain ⟨g0, k0, pc0, bs0, hg0, hget0⟩ := exists_oStore hpre hX hcomp hf hr hs ht hh hd
  have hz' : z < (oWord Q r s tok head dc).bytes := by rw [oWord_bytes]; exact hz
  have hspace : ((oLoc Q s (Q.qStart r + tok) head dc).at z).space = .global := rfl
  obtain ⟨r0, s0, tok0, head0, hr0, hs0, ht0, hh0, hc0⟩ :=
    write_spec hpre hX hcomp hin hg0 hget0 rfl
  refine IsFinal.of_agree hfin (ws := allWrites L X) (fun w a bs hw hc =>
    mem_allWrites hX hw (hc.1.symm.trans hspace)) (w := .thread (g0, k0))
    (a := EvD.wordAcc (oLoc Q s (Q.qStart r + tok) head dc)) (bs := bs0) (Or.inl ⟨pc0, hget0⟩)
    (covers_word hz) ?_
  intro w a bs hw hc
  have hsp : a.loc.space = .global := hc.1.symm.trans hspace
  obtain ⟨g', n', pc', rfl, hget'⟩ := Interface.global_write_thread hX hw hsp
  have hg' := Frame.lt_of_get hX hget'
  obtain ⟨r', s', tok', head', hr', hs', ht', hh', hcase⟩ :=
    write_spec hpre hX hcomp hin hg' hget' hsp
  have hx : ((oLoc Q s (Q.qStart r + tok) head dc).at z).addr =
      (oLoc Q s (Q.qStart r + tok) head dc).addr + z := rfl
  have hin1 : (oLoc Q s (Q.qStart r + tok) head dc).addr ≤
        ((oLoc Q s (Q.qStart r + tok) head dc).at z).addr ∧
      ((oLoc Q s (Q.qStart r + tok) head dc).at z).addr <
        (oLoc Q s (Q.qStart r + tok) head dc).addr + 4 := by
    rw [hx]
    omega
  obtain ⟨-, -, h1, h2⟩ := hc
  rcases hcase with ⟨dc', hd', rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp only [EvD.wordAcc] at h1 h2
    obtain ⟨e1, e2, e3, e4⟩ := Interface.oLoc_overlap (Q := Q) htk (token_lt hpre hr' ht')
      hh hh' hd hd' hin1 ⟨h1, h2⟩
    obtain ⟨rfl, rfl⟩ := token_unique hpre hr hr' ht ht' e2
    subst e1 e3 e4
    exact wbyte_word _ _ hz'
  · simp only [EvD.wordAcc] at h1 h2
    exact (Interface.oLoc_lseLoc_apart hpre hs htk hh hd hs' (token_lt hpre hr' ht') hh'
      hin1 ⟨h1, h2⟩).elim

/-- **A byte of `LsePart` of a valid row holds the byte of its word.** -/
theorem final_lseByte (hpre : Pre Q L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hcomp : Complete L X) (hin : Inputs Q L mem0 X) {m : FinalMem} (hfin : IsFinal L mem0 X m)
    {r s tok head z : Nat} (hr : r < Q.b) (hs : s < Q.splits) (ht : tok < Q.qLen r)
    (hh : head < heads) (hz : z < 4) :
    m ((lseLoc Q s (Q.qStart r + tok) head).at z) =
      some (some ((lseWordOf Q r s tok head).byteAt z)) := by
  have htk := token_lt hpre hr ht
  have hf := Interface.threadFacts hpre hin.smOb hX hin.premises
  obtain ⟨g0, k0, pc0, bs0, hg0, hget0⟩ := exists_lseStore hpre hX hcomp hf hr hs ht hh
  have hz' : z < (lseWordOf Q r s tok head).bytes := by rw [lseWordOf_bytes]; exact hz
  have hspace : ((lseLoc Q s (Q.qStart r + tok) head).at z).space = .global := rfl
  refine IsFinal.of_agree hfin (ws := allWrites L X) (fun w a bs hw hc =>
    mem_allWrites hX hw (hc.1.symm.trans hspace)) (w := .thread (g0, k0))
    (a := EvD.wordAcc (lseLoc Q s (Q.qStart r + tok) head)) (bs := bs0) (Or.inl ⟨pc0, hget0⟩)
    (covers_word hz) ?_
  intro w a bs hw hc
  have hsp : a.loc.space = .global := hc.1.symm.trans hspace
  obtain ⟨g', n', pc', rfl, hget'⟩ := Interface.global_write_thread hX hw hsp
  have hg' := Frame.lt_of_get hX hget'
  obtain ⟨r', s', tok', head', hr', hs', ht', hh', hcase⟩ :=
    write_spec hpre hX hcomp hin hg' hget' hsp
  have hx : ((lseLoc Q s (Q.qStart r + tok) head).at z).addr =
      (lseLoc Q s (Q.qStart r + tok) head).addr + z := rfl
  have hin1 : (lseLoc Q s (Q.qStart r + tok) head).addr ≤
        ((lseLoc Q s (Q.qStart r + tok) head).at z).addr ∧
      ((lseLoc Q s (Q.qStart r + tok) head).at z).addr <
        (lseLoc Q s (Q.qStart r + tok) head).addr + 4 := by
    rw [hx]
    omega
  obtain ⟨-, -, h1, h2⟩ := hc
  rcases hcase with ⟨dc', hd', rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp only [EvD.wordAcc] at h1 h2
    exact (Interface.oLoc_lseLoc_apart hpre hs' (token_lt hpre hr' ht') hh' hd' hs htk hh
      ⟨h1, h2⟩ hin1).elim
  · simp only [EvD.wordAcc] at h1 h2
    obtain ⟨e1, e2, e3⟩ := Interface.lseLoc_overlap (Q := Q) htk (token_lt hpre hr' ht')
      hh hh' hin1 ⟨h1, h2⟩
    obtain ⟨rfl, rfl⟩ := token_unique hpre hr hr' ht ht' e2
    subst e1 e3
    exact wbyte_word _ _ hz'

/-! ### `Post` -/

theorem toBytes_getElem {v : Value} {k : Nat} (hk : k < v.bytes) :
    v.toBytes[k]? = some (v.byteAt k) := by
  simp [Value.toBytes, hk]

theorem oWord_eq_zero {P : Params} {r s tok head d : Nat} (hn : P.numIters r s = 0) :
    oWord P r s tok head d = b32 0 := by
  simp [oWord, hn]

theorem oWord_ne {P : Params} {r s tok head d : Nat} (hn : ¬ P.numIters r s = 0) :
    oWord P r s tok head d = fl (oPart P r s tok head d) := by
  simp [oWord, hn]

theorem lseWordOf_eq {P : Params} {r s tok head : Nat} (h : rowSum P r s tok head = 0) :
    lseWordOf P r s tok head = b32 4286578688 := by
  simp [lseWordOf, h]

theorem lseWordOf_ne {P : Params} {r s tok head : Nat} (h : ¬ rowSum P r s tok head = 0) :
    lseWordOf P r s tok head = fl (lsePart P r s tok head) := by
  simp [lseWordOf, h]

/-- A split with no block has no visible key. -/
theorem rowSum_of_noIters (hpre : Pre Q L mem0) {r s tok head : Nat} (hn : Q.numIters r s = 0) :
    rowSum Q r s tok head = 0 := by
  refine (flatten_eq_nil_iff hpre.scalePos hpre.splitsPos r s tok head (fun _ _ => 0)).1 ?_
  simp [blocks, hn]

/-- **The final memory of a complete execution is `Spec`'s output**, from the stores' values. -/
theorem post_of (hpre : Pre Q L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hcomp : Complete L X) (hin : Inputs Q L mem0 X) {m : FinalMem} (hfin : IsFinal L mem0 X m) :
    Post Q mem0 m := by
  have hf := Interface.threadFacts hpre hin.smOb hX hin.premises
  refine ⟨?_, ?_, ?_, hf.post_frame hfin⟩
  · intro r hr s hs tok ht head hh d hd
    by_cases hn : Q.numIters r s = 0
    · have h0 : oPart Q r s tok head d = 0 := by
        simp [oPart, rowSum_of_noIters hpre hn]
      rw [memFloat_of_bytes (v := b32 0) (fun _ => rfl) rfl (fun k hk => ?_), h0]
      · exact valFloat_zero
      · have := final_oByte hpre hX hcomp hin hfin hr hs ht hh hd hk
        rw [oWord_eq_zero hn] at this
        exact this
    · refine memFloat_float fun k hk => ?_
      have := final_oByte hpre hX hcomp hin hfin hr hs ht hh hd hk
      rw [oWord_ne hn] at this
      exact this
  · intro r hr s hs tok ht head hh hne
    refine memFloat_float fun k hk => ?_
    have := final_lseByte hpre hX hcomp hin hfin hr hs ht hh hk
    rw [lseWordOf_ne hne] at this
    exact this
  · intro r hr s hs tok ht head hh h0 k hk
    have := final_lseByte hpre hX hcomp hin hfin hr hs ht hh hk
    rw [lseWordOf_eq h0] at this
    have hb := Interface.negInf_bytes k hk
    rw [toBytes_getElem (v := b32 4286578688) (show k < 4 from hk)] at hb
    rw [this, Option.some.injEq, Option.some.injEq]
    exact Option.some.inj hb

/-- **`ResultGoal`**: a complete execution of a launch that satisfies `Pre` leaves `Spec.Post`,
from the result layer's inputs (`Inputs`: what the thread, protocol and softmax layers have not
yet proved) for every consistent complete execution. -/
theorem result_goal (hpre : Pre Q L mem0)
    (hin : ∀ X, Consistent L kernel Assumptions.all mem0 X → Complete L X →
      Inputs Q L mem0 X) :
    ResultGoal kernel Assumptions.all L mem0 (Post Q mem0) :=
  fun X _ hX hcomp hfin => post_of hpre hX hcomp (hin X hX hcomp) hfin

end
end PTX.Kernels.InklingRelDecode.Proof.Result.Out
