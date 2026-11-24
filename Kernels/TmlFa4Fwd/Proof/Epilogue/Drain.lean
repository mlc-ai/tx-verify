-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Lib.WarpIndex
public import Kernels.TmlFa4Fwd.Proof.Lib.GlobalWrites
public import Kernels.TmlFa4Fwd.Proof.Epilogue.Ledger
public import Lemmas.Tcgen05.TcFence
import Kernels.TmlFa4Fwd.Proof.Epilogue.Barriers
import Kernels.TmlFa4Fwd.Proof.Epilogue.Facts
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The output warp's drain

A lane of warp 13 that issued a tensor store and returned has committed its second bulk group
(pc 2980) after the store and then waited for the reads of its groups (pc 2984): the ledger's
commit count and a count of the read waits along the machine's run (`commit_wait`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Epilogue
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- **A store is drained before its lane returns**: a lane of warp 13 whose trace ends with its
return commits its second group after each of its stores (pc 2980) and then waits for the reads
of its groups (pc 2984), before the return. -/
theorem commit_wait (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hw : Prologue.warpIndex L g = 13) {k site addr : Nat} {spec : TensorStore.Spec}
    (he : X.get (g, k) = some ⟨site, .tensorStore addr spec⟩)
    (hx : (X.tr g).getLast? = some ⟨9205, .exit⟩) :
    ∃ c w, k < c ∧ c < w ∧ w + 1 < (X.tr g).length ∧
      X.get (g, c) = some ⟨2980, .bulkCommit⟩ ∧
      X.get (g, w) = some ⟨2984, .bulkWait .read 0⟩ := by
  have hpc := tensorStoreSite hX he
  simp only [outputStoreSites, List.mem_cons, List.not_mem_nil, or_false] at hpc
  have hg := Frame.lt_of_get hX he
  obtain ⟨hk5, dk, nk, hσk, -, hEk, -⟩ := output_event (p := p) hp hX hw he
    (by simp only; omega) (by rintro _ _ ⟨⟩)
  have hkn : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  have hfin : X.get (g, (X.tr g).length - 1) = some ⟨9205, .exit⟩ := by
    show (X.tr g)[(X.tr g).length - 1]? = _
    simpa only [List.getLast?_eq_getElem?] using hx
  have hkf : k < (X.tr g).length - 1 := by
    rcases Nat.lt_or_ge k ((X.tr g).length - 1) with h | h
    · exact h
    · have : k = (X.tr g).length - 1 := by omega
      rw [this, hfin] at he
      cases he
  have h5 : 5 ≤ (X.tr g).length := by omega
  obtain ⟨df, nf, hσf, -, hEf, -⟩ := event_site hp hX hw (by omega) hfin (by rintro _ _ ⟨⟩)
  set F := (X.tr g).length - 1 with hF
  -- The store's state and the return's state.
  obtain ⟨sk, w, dn, tl, u1, u2, u4, u8, u16, tot, grp, acc, gx, cur, bal, pv, nt, c0, c1⟩ := dk
  cases sk <;> simp only [Ev, isStore, reduceCtorEq, exists_false, or_self] at hEk
  case store st b =>
  obtain ⟨sf, w', dn', tl', u1', u2', u4', u8', u16', tot', grp', acc', gx', cur', bal', pv',
    nt', c0', c1'⟩ := df
  cases sf <;> simp only [Ev, isStore, reduceCtorEq, exists_false, or_self] at hEf
  case exit late =>
  obtain ⟨cs, cc, cw, -⟩ := ledger_at hp hX hg hw hσf
  -- The store is before the return, so the return is the second pass's.
  have hsk : isStore ⟨site, .tensorStore addr spec⟩ = true := rfl
  have hstore : 1 ≤ ((X.tr g).take F).countP isStore := by
    have hm := countP_take_mono isStore (X.tr g) (show k + 1 ≤ F by omega)
    rw [take_succ he, List.countP_append] at hm
    simp only [hsk, List.countP_singleton, ↓reduceIte] at hm
    omega
  have hlate : late = true := by
    cases late
    · simp only [stores, written, Bool.false_eq_true, ↓reduceIte] at cs; omega
    · rfl
  subst hlate
  simp only [commits, written, ↓reduceIte] at cc
  simp only [drains, written, ↓reduceIte] at cw
  -- The second commit, after the store: before the store a lane has committed at most its stage.
  have ck := (ledger_at hp hX hg hw hσk).2.1
  have hst : st.val ≤ 1 := by have := st.isLt; omega
  obtain ⟨jc, hjc, xc, hxc, hcom, hcc⟩ := exists_nth isCommit (X.tr g) (n := 1) (k := F)
    (by omega)
  have hjk : k < jc := by
    rcases Nat.lt_or_ge k jc with h | h
    · exact h
    rcases Nat.eq_or_lt_of_le h with h' | h'
    · exfalso
      rw [h'] at hxc
      rw [show (X.tr g)[k]? = _ from he] at hxc
      cases hxc
      simp [isCommit] at hcom
    · have := countP_take_mono isCommit (X.tr g) (show jc + 1 ≤ k by omega)
      rw [take_succ hxc, List.countP_append] at this
      simp only [hcom, List.countP_singleton, ↓reduceIte] at this
      simp only [commits] at ck
      omega
  obtain ⟨dc, nc, hσc, -, hEc, hpcc⟩ := event_site hp hX hw (by omega) hxc (by
    rintro pc f rfl; simp [isCommit] at hcom)
  have ccc := (ledger_at hp hX hg hw hσc).2.1
  simp only [hcc, commits, written] at ccc
  -- The second read wait.
  obtain ⟨jw, hjw, xw, hxw, hwait, hwc⟩ := exists_nth isWait (X.tr g) (n := 1) (k := F)
    (by omega)
  have hjw5 : 5 ≤ jw := by
    by_contra h
    have := (prologue_ev hp hX (by omega) hxw (by rintro pc f rfl; simp [isWait] at hwait)
      (good_all hp hX hg hw jw)).2.2.2.2 .wait (by simp [StartCls])
    simp only [cls] at this
    rw [hwait] at this
    cases this
  obtain ⟨dw, nw, hσw, -, hEw, hpcw⟩ := event_site hp hX hw hjw5 hxw (by
    rintro pc f rfl; simp [isWait] at hwait)
  obtain ⟨-, ccw, cww, -⟩ := ledger_at hp hX hg hw hσw
  simp only [hwc, commits, drains, written] at cww ccw
  obtain ⟨pcc, kc⟩ := xc
  obtain ⟨pcw, kw⟩ := xw
  have hkc : kc = .bulkCommit := by cases kc <;> first | rfl | simp [isCommit] at hcom
  obtain ⟨n, hkw⟩ : ∃ n, kw = .bulkWait .read n := by
    revert hwait
    cases kw with
    | bulkWait q n => cases q <;> intro h <;> first | exact ⟨n, rfl⟩ | simp [isWait] at h
    | _ => intro h; simp [isWait] at h
  subst hkc hkw
  obtain ⟨sc, _⟩ := dc
  obtain ⟨sw, _⟩ := dw
  simp only at hpcc hpcw
  cases sc <;> simp only [Ev, isStore, reduceCtorEq, exists_false, or_self,
    Bool.false_eq_true] at hEc
  case commit sc =>
  cases sw <;> simp only [Ev, isStore, reduceCtorEq, exists_false, or_self,
    Bool.false_eq_true] at hEw
  case drain sw =>
  simp only at ccc ccw cww
  have hsc : sc = 1 := Fin.ext (by omega)
  have hsw : sw = 1 := Fin.ext (by omega)
  subst hsc hsw
  have hcw : jc < jw := by
    by_contra h
    have hm := countP_take_mono isCommit (X.tr g) (show jw ≤ jc by omega)
    omega
  refine ⟨jc, jw, hjk, hcw, by omega, ?_, ?_⟩
  · show (X.tr g)[jc]? = _
    rw [hxc, hpcc]; rfl
  · have hn : n = 0 := by simpa using hEw
    subst hn
    show (X.tr g)[jw]? = _
    rw [hxw, hpcw]; rfl

end
end PTX.Kernels.TmlFa4Fwd.Proof.Epilogue
