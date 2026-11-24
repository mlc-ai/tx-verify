-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.PrologueInitProgress
public import Kernels.TmlFa4Fwd.Proof.PrologueWarp0Progress
public import Lemmas.Step.WarpElect

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Prologue
open PTX PTX.Flow PTX.Proof

noncomputable section

/-- A lane at an initialization election, with no previous event at or past this instruction. -/
structure InitElectCursor (l : Launch) (X : Execution) (g n : Nat) (j : Fin 16)
    (t : TState) : Prop where
  cursor : InitCursor l X g n t
  pc : t.pc = (electSite j).pc
  fault : t.fault = none
  earlier : ∀ k < n, ∀ e, X.get (g, k) = some e → e.pc < (electSite j).pc
  released : n = (X.tr g).length → Step.Released l X g

theorem electionAtCursor {l : Launch} {X : Execution} {g n : Nat} {j : Fin 16} {t : TState}
    (h : InitElectCursor l X g n j t) (hLt : n < (X.tr g).length) :
    ∃ inst leader, X.Elect (g, n) (electSite j).pc (2 ^ 32 - 1) inst leader ∧
      InitCursor l X g (n + 1) (electedState l g t (electSite j) leader) := by
  obtain ⟨_, u, hRun, hLocal, o, hRest⟩ := h.cursor
  have hOut : out kernel Assumptions.all l g t = .ev
      (.elect (2 ^ 32 - 1) (electedState l g t (electSite j))) := by
    have hPc : StartupPc (electSite j).pc := by fin_cases j <;> decide
    exact startupOut (h.pc ▸ hPc) (electOut j h.pc h.fault)
  have hNext : Next kernel Assumptions.all l g u t
      (.elect (2 ^ 32 - 1) (electedState l g t (electSite j))) := ⟨hLocal, hOut⟩
  rw [List.drop_eq_getElem_cons hLt] at hRest
  obtain ⟨v, ⟨i, lead, he, hv⟩, hTail⟩ := hNext.continuing_event (by
    rintro ⟨_, _, _, hh⟩
    cases hh) hRest
  obtain rfl := Option.some.inj hv
  refine ⟨i, lead, ?_, Nat.succ_le_of_lt hLt, _, ?_, .refl, o, hTail⟩
  · change (X.tr g)[n]? = _
    rw [List.getElem?_eq_getElem hLt, he, h.pc]
  · rw [List.take_succ_eq_append_getElem hLt]
    exact hRun.snoc hLocal ⟨_, hOut, i, lead, he, rfl⟩

/-- If all lanes of warp zero have reached the same initialization election, the entire warp
records it in a maximal execution. Followers may have fewer preceding records than the leader. -/
theorem initElectionProgress {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X) {g : Nat}
    (hg : g < l.threads) (hw : warpIndex l g = 0) {j : Fin 16}
    (n : Nat → Nat) (t : Nat → TState)
    (hPos : ∀ h, SameWarp l g h → 0 < n h)
    (hC : ∀ h, SameWarp l g h → InitElectCursor l X h (n h) j (t h)) :
    ∀ h, SameWarp l g h → n h < (X.tr h).length := by
  intro q hq
  by_contra hn
  have hEq : n q = (X.tr q).length := by have := (hC q hq).cursor.length; omega
  have hPeer (h : Nat) (hh : SameWarp l g h) : n h = (X.tr h).length := by
    have hLen := (hC h hh).cursor.length
    by_contra hne
    obtain ⟨i, lead, he, _⟩ := electionAtCursor (hC h hh) (by omega)
    have hW := Step.sameWarp_trans (sameWarp_symm hh) hq
    obtain ⟨k, pcOld, pc, maskOld, mask, inst, oldLeader, leader, hOld, hGet⟩ :=
      ElectOrd.partner hMax.1 hW he (electMember_full l q)
    have hPc := (hMax.1.elect.2.1 _ _ _ _ _ _ _ _ _ hOld hGet hW).1
    have hk : k < (X.tr q).length := ElectOrd.lt_len hGet
    have hn' := (hC q hq).earlier k (by omega) ⟨pc, .elect mask inst leader⟩ hGet
    change pc < (electSite j).pc at hn'
    have hOld' : X.get (h, n h) = some ⟨pcOld, .elect maskOld inst oldLeader⟩ := hOld
    have he' : X.get (h, n h) = some ⟨(electSite j).pc, .elect (2 ^ 32 - 1) i lead⟩ := he
    have hOriginal : (electSite j).pc = pcOld :=
      congrArg Event.pc (Option.some.inj (he'.symm.trans hOld'))
    omega
  obtain ⟨lead, hLead, hDet⟩ := Step.exists_leader hMax.1 (g := g) (electMember_full l g)
  apply hMax.not_grows
  refine Step.elect_counted_extension (pc := (electSite j).pc) hMax.1 hg
    (fun lane hmem => warp0LaneWitness hp hg hw hmem.1) (fun h _ => electMember_full l h)
    hLead hDet ?_ ?_ ?_ ?_
  · intro h hh
    apply Or.inl
    intro hNil
    have hLen := hPeer h hh
    rw [hNil, List.length_nil] at hLen
    have := hPos h hh
    omega
  · exact fun h hh => (hC h hh).released (hPeer h hh)
  · intro h hh inst
    obtain ⟨_, u, hRun, hLocal, _, _⟩ := (hC h hh).cursor
    rw [List.take_of_length_le (hPeer h hh).ge] at hRun
    have hPc := (hC h hh).pc
    have hSite : StartupPc (electSite j).pc := by fin_cases j <;> decide
    exact ⟨u, t h, _, hRun, hLocal,
      ⟨_, startupOut (hPc ▸ hSite) (electOut j hPc (hC h hh).fault),
        inst, lead, by rw [hPc]; rfl, rfl⟩⟩
  · intro inst
    exact Assumptions.wfStep.quiet hMax.1 le_appendLanes rfl (noNewRead_appendLanes fun _ => by rfl)

end
end PTX.Kernels.TmlFa4Fwd.Prologue
