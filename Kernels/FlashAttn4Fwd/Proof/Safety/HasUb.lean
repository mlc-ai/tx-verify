-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Interface.Tc
public import Lemmas.Kernel.FrameStop
public import Lemmas.Flow.AllocTmpl
public import Lemmas.Step.ExitLast

@[expose] public section

/-! # The undefined-behaviour branch of `Unsafe`

Undefined behaviour fires only after the thread's machine stopped (`TcFacts.ub_stop`), so after
a first stop (`Frame.first_stop_any`), which is the thread's exit or comes after a read the
machine does not follow (`TcFacts.stop_cause`, `BadRead`). An exit is the thread's last event
(`Execution.exit_last`), so no undefined-behaviour event follows it. The value protocols exclude
each such read:

* every `tcgen05.ld` returns single-precision floats (`LoadFloats`): each loaded register's
  source is an MMA result, an f32 value (the loads' sources, `Score.s_readSource` and
  `OAcc.o_readSource`, with the sources' values);
* every correction `ld.shared` returns the bytes of a canonical single-precision word
  (`StatsFloats`, `F32Read`): it reads a statistics word, whose last write is a softmax thread's
  store of such a word (`StatsBaseCausality.stats_ordered`, the read of the last write);
* every broadcast shuffle returns the thread's own source value (`ShflUniform`): every shuffle
  of the kernel is a `shfl.sync.idx` from lane 0 of a value all lanes of the warp hold
  (DEP-WARP-SHUFFLE);
* warp 12's read of its base word returns the bytes of the 32-bit 0 (`BaseZero`): lane 0's store
  of the allocated column, 0 (`TmemAlloc.read_zero`, from `TmemAlloc.BaseRead`); they rebuild to
  that word. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Safety

open PTX PTX.Proof

noncomputable section

variable {L : Launch} {mem0 : Mem0} {X : Execution}

/-- Every Tensor Memory load returns single-precision floats. -/
def LoadFloats (L : Launch) (X : Execution) : Prop :=
  ∀ {g k pc a : Nat} {vals : List Value}, g < L.threads →
    X.get (g, k) = some ⟨pc, .tc (.ld a vals .s32x32b)⟩ → F32s vals

/-- Every `ld.shared` of a correction thread returns the bytes of a canonical single-precision
word. -/
def StatsFloats (L : Launch) (X : Execution) : Prop :=
  ∀ {g k pc : Nat} {a : Acc} {bs : List (Option Byte)}, g < L.threads → 8 ≤ warpOf L g →
    warpOf L g < 12 → X.get (g, k) = some ⟨pc, .rd a bs⟩ → ∃ x, F32Read bs x

/-- Every shuffle returns the thread's own source value. -/
def ShflUniform (L : Launch) (X : Execution) : Prop :=
  ∀ {g k pc b c : Nat} {md : ShflMode} {a recv : Value} {ok : Bool}, g < L.threads →
    X.get (g, k) = some ⟨pc, .shfl md a b c recv ok⟩ → recv = a

/-- Every read of a CTA's base word by its warp 12 returns the bytes of the 32-bit 0. -/
def BaseZero (L : Launch) (X : Execution) : Prop :=
  ∀ {g k pc : Nat} {a : Acc} {bs : List (Option Byte)}, g < L.threads →
    X.get (g, k) = some ⟨pc, .rd a bs⟩ → a.loc = baseLoc L (ctaOf L g) → a.size = 4 →
    warpOf L g = 12 → bs = (b32 0).toBytes.map some

/-- **No read is one a machine does not follow**, given the protocols' values. -/
theorem not_badRead (hbz : BaseZero L X) (hlf : LoadFloats L X) (hsf : StatsFloats L X)
    (hsh : ShflUniform L X) {g j : Nat} (hg : g < L.threads) :
    ¬ BadRead L X g j := by
  rintro (⟨pc, a, vals, he, hn⟩ | ⟨pc, a, bs, he, h8, h12, hn⟩ |
    ⟨pc, a, bs, he, hw, hloc, hsz, hn⟩ | ⟨pc, md, a, b, c, recv, ok, he, hn⟩)
  · exact hn (hlf hg he)
  · exact hn (hsf hg h8 h12 he)
  · rw [hbz hg he hloc hsz hw] at hn
    exact absurd (hn _ (Flow.rebuild_b32 0)) (by simp [b32, Value.regBits])
  · exact hn (hsh hg he)

/-- **No event is undefined behaviour**, given the protocols' values. -/
theorem no_ub (hX : Consistent L kernel asms mem0 X) (ht : TcFacts L X) (hbz : BaseZero L X)
    (hlf : LoadFloats L X) (hsf : StatsFloats L X) (hsh : ShflUniform L X) : ¬ HasUb X := by
  rintro ⟨⟨g, k⟩, pc, f, he⟩
  have hg : g < L.threads := Frame.lt_of_get hX he
  obtain ⟨i, d, hik, hσ, hn⟩ := Frame.first_stop_any (ht.ub_stop hg he)
  rcases ht.stop_cause hg hσ hn with ⟨pcx, hx⟩ | ⟨j, -, hbad⟩
  · have hlast := Execution.exit_last hX hg hx
    have hk : k < (X.tr g).length := by
      by_contra hc
      have he' : (X.tr g)[k]? = some ⟨pc, .ub f⟩ := he
      rw [List.getElem?_eq_none (by omega)] at he'
      cases he'
    omega
  · exact not_badRead hbz hlf hsf hsh hg hbad

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Safety
