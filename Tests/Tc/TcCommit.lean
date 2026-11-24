-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assembly.Correctness
public import Core.Thread.Run
public import Core.Source.Decode
public import Lemmas.Tcgen05.TcCommit

namespace PTX.Tests.TcCommit
noncomputable section

private def launch : Launch :=
  { grid := 8, block := 384, params := fun _ => none, clusterSize := 4 }
private def targets : TcCommit.Spec := ⟨.two, ⟨.shared, 6, 40⟩, 5, 4, 4⟩
-- Target bits are cluster ranks, not relative to the issuer or to its CTA pair.
example : TcCommit.resolve launch .two 7 ⟨.shared, 6, 40⟩ 5 = some targets := rfl
example : TcCommit.target targets 0 = some ⟨.shared, 4, 40⟩ := rfl
example : TcCommit.target targets 2 = some ⟨.shared, 6, 40⟩ := rfl
example : TcCommit.target targets 1 = none := rfl
example : TcCommit.resolve launch .two 7 ⟨.shared, 6, 40⟩ 16 = none := rfl
example : TcCommit.resolve launch .two 7 ⟨.shared, 2, 40⟩ 5 = none := rfl

private def env : Decode.Env :=
  { classes := [⟨"r".toList, 1, 32⟩, ⟨"rs".toList, 1, 16⟩], labels := [], params := [] }
example : Decode.op env
    "tcgen05.commit.cta_group::2.mbarrier::arrive::one.shared::cluster.multicast::cluster.b64"
    [.address [.register "r0"], .register "rs0"] =
    .ok (.tcCommit .two 0 0 (some (.reg 1))) := rfl
private def state : TState := { regs := fun
  | 0 => some (.bits 32 40)
  | 1 => some (.bits 16 3)
  | _ => none }
example : eventTmpl [] launch (7 * 384) state (.tcCommit .two 0 0 (some (.reg 1))) =
    .tc (.commit ⟨.two, ⟨.shared, 7, 40⟩, 3, 4, 4⟩) (next state) := rfl
-- Without a mask, the only target is the addressed mbarrier, for either cta_group.
example : Decode.op env
    "tcgen05.commit.cta_group::1.mbarrier::arrive::one.shared::cluster.b64"
    [.address [.register "r0"]] = .ok (.tcCommit .one 0 0 none) := rfl
example : eventTmpl [] launch (7 * 384) state (.tcCommit .one 0 0 none) =
    .tc (.commit ⟨.one, ⟨.shared, 7, 40⟩, 8, 4, 4⟩) (next state) := rfl
example : TcCommit.target ⟨.one, ⟨.shared, 7, 40⟩, 8, 4, 4⟩ 3 = some ⟨.shared, 7, 40⟩ := rfl

private def spec : TcCommit.Spec := ⟨.two, ⟨.shared, 0, 40⟩, 3, 0, 2⟩
private def operands : TcMma.OperandSpec :=
  ⟨⟨.two, .f16 .f16 .f32, 128, 16, false, false, false, false, false⟩,
   ⟨0, 0, 1024, 0, false, false, .b128⟩,
   ⟨0, 0, 1024, 0, false, false, .b128⟩, 0, 1, none, {}⟩
private def mma : Event := ⟨0, .tc (.mma 0 operands false [])⟩
private def commit : Event := ⟨1, .tc (.commit spec)⟩
private def oneDelivery : Execution where
  tr := fun g => if g = 0 then [mma, commit] else []
  rf := fun _ _ => none
  tcNotified := fun i => if i = (0, 1) then {0} else ∅

-- Only rank 0's arrival has occurred. The peer has no arrival yet.
example : AsyncCopy.objectAction oneDelivery oneDelivery.async ⟨.shared, 0, 40⟩
    (.async (0, 1) (.tcNotify 0)) = some (.arrive 1 0) := rfl
example : AsyncCopy.objectAction oneDelivery oneDelivery.async ⟨.shared, 1, 40⟩
    (.async (0, 1) (.tcNotify 1)) = none := rfl
example : AsyncCopy.objectAction oneDelivery oneDelivery.async ⟨.shared, 1, 40⟩
    (.async (0, 1) (.tcNotify 0)) = none := rfl

-- No notification can be delivered while a tracked MMA remains incomplete.
example : ¬ AsyncCopy.CommitOk oneDelivery := by
  intro h
  have hn : (0 : Fin 16) ∈ oneDelivery.tcNotified (0, 1) := by simp [oneDelivery]
  have hd := (h (0, 1) 0 hn).2 (0, 0)
    ⟨rfl, by decide, .inl ⟨0, operands, false, [], 0, rfl⟩, spec, 1, rfl⟩
  cases hd

-- All tracked work can finish while only one target has received its notification.
private def done : Execution :=
  { oneDelivery with async := { mmaDone := fun i => i = (0, 0) } }
example : AsyncCopy.CommitOk done := by
  intro i rank hn
  have hi : i = (0, 1) := by
    by_contra h
    simp only [done, oneDelivery, ite_eq_right h, Finset.notMem_empty] at hn
  subst i
  have hr : rank = 0 := by
    change rank ∈ ({0} : Finset (Fin 16)) at hn
    exact Finset.mem_singleton.mp hn
  subst rank
  refine ⟨⟨spec, ⟨.shared, 0, 40⟩, ⟨1, rfl⟩, rfl⟩, ?_⟩
  intro x hx
  have ht : x.1 = 0 := hx.1
  have hn : x.2 < 1 := hx.2.1
  have he : x = (0, 0) := Prod.ext ht (by omega)
  subst x
  rfl

-- A missing peer delivery remains a completion obligation even after MMA completion.
example : ¬ AsyncDrained done := by
  intro h
  have hn := h (0, 1) (.tcNotify 1)
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨spec, 1, ⟨.shared, 1, 40⟩, ⟨1, rfl⟩, rfl, rfl⟩)))))))
  change (1 : Fin 16) ∈ ({0} : Finset (Fin 16)) at hn
  have hnot : (1 : Fin 16) ∉ ({0} : Finset (Fin 16)) := by decide
  exact hnot hn

-- Another thread's work is not silently included in this commit.
example {X : Execution} {mma commit : EvId} (h : mma.1 ≠ commit.1) :
    ¬ AsyncCopy.TracksMma X mma commit := fun ht => h ht.1

end
end PTX.Tests.TcCommit
