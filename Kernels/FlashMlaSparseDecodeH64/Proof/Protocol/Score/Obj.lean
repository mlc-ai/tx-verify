-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Close.Obj
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.MbarUse.NotifyObj
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.Elect.Mma

@[expose] public section

/-! # The main loop's score and PV barriers as objects

From `mbar_use` and the rows only, for slot `s` of CTA `c`:

* `qkDone s` is named by the initialization (count 1), the MMA lane's commits at pc 2105 and
  warpgroup 0's polls at pc 272 with the parity of their earlier successful polls. It is a commit
  object `MbarRing.Notify.Obj` of the CTA's `mmaLane`, polled with offset 0 (`qkDone_obj`;
  library pattern `UnitNotify`).
* `soReady s` is named by the initialization (count 128), warpgroup 0's unit arrivals at pc 1122
  and the MMA lane's polls at pc 2107 with the parity of its earlier successful polls. It is a
  `MbarRing.Unit.Obj` of the warpgroup-0 lanes, polled with offset 0 (`soReady_obj`).
* `svDone s` is named by the initialization (count 1), the MMA lane's commits at pc 2148,
  warpgroup 0's epilogue poll at pc 1184 and the dequant lanes' polls at pc 2684 with the parity
  of their earlier successful polls plus one. It is a commit object of the MMA lane whose
  selected pollers, the threads of warps 4 and up (so the dequant lanes), use offset 1
  (`svDone_obj`): the epilogue's parity is that of its QK polls, not of its `svDone` polls.

Each object takes `MmaOne` (lane B, row-proved as `mmaOne`) besides the inputs of `initFirst`.

**Observe / Lag** (not here): `qkDone` / `soReady` form the score ring of the MMA lane and
warpgroup 0 (`KRing`: full `qkDone` of one commit kind, empty `soReady` of 128 notifications; the
commit's issue precedes its notification by `Reach.commit_notify`), with inputs of lane B (the
commit of use `u` follows `u + 1` polls of `soReady`, the MMA lane's first `soReady` poll being
for use 0 of the opposite slot as the row's parities say) and W1 (the arrival of use `u` follows
`u + 1` polls of `qkDone`); `svDone`'s observes are `Notify.Obj.observes` with the reuse paths
`Reach` through `dequantReady` (see `Protocol/Dequant/Obj.lean`); their Lags need, as
`QueryTime`, the slot-waiter time facts of lanes B, W1 and D. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow PTX.MbarRing

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **The uses of the score and PV barriers of slot `s` of CTA `c`.** For `qkDone s`, `soReady s`
and `svDone s`: the initialization, the MMA lane's commits and polls, warpgroup 0's arrivals and
polls, and the dequant lanes' polls, by family. -/
theorem score_use (hR : MbarRows P L X) {c g k : Nat} {e : Event} {f : MbarFam}
    (hf : ∃ s, f = .qkDone s ∨ f = .soReady s ∨ f = .svDone s)
    (hg : g < L.threads) (he : X.get (g, k) = some e) (hm : Frame.MbarOf e (mbarLoc L c f)) :
    (∃ n, e.kind = .mbInit (mbarLoc L c f) n) ∨ g / L.block = c ∧
      ((MmaOn L g e.pc ∧ ((∃ s, f = .qkDone s ∨ f = .svDone s) ∧ MbarRow.Commit e (mbarLoc L c f) ∨
          (∃ s, f = .soReady s) ∧ MbarRow.Wait e (mbarLoc L c f)
            (okPolls (mbarLoc L c f) ((X.tr g).take k) % 2))) ∨
        (MbarRow.Wg0At L g e.pc ∧ ((∃ s, f = .qkDone s) ∧ MbarRow.Wait e (mbarLoc L c f)
            (okPolls (mbarLoc L c f) ((X.tr g).take k) % 2) ∨
          (∃ s, f = .soReady s) ∧ MbarRow.Arrive e (mbarLoc L c f) 0 ∨
          (∃ s, f = .svDone s) ∧ ∃ q, MbarRow.Wait e (mbarLoc L c f) q)) ∨
        (MbarRow.DequantAt L g e.pc ∧ (∃ s, f = .svDone s) ∧ MbarRow.Wait e (mbarLoc L c f)
          ((okPolls (mbarLoc L c f) ((X.tr g).take k) + 1) % 2))) := by
  obtain ⟨s, hs⟩ := hf
  rcases mbar_use hR hg he hm with ⟨-, ⟨-, j, -, -, hk⟩⟩ | ⟨hw, h⟩ | ⟨hw, h⟩ | ⟨-, h⟩ |
    ⟨-, h⟩ | ⟨hw, h⟩
  · exact .inl ⟨_, hk⟩
  · cases h with
    | lastStore _ hl _ | coordReady _ hl _ | coordFree _ hl _ =>
      rcases hs with rfl | rfl | rfl <;> nomatch (fam_eq hl).2
    | qkDone _ hl hk =>
      exact .inr ⟨(fam_eq hl).1.symm, .inr (.inl ⟨hw, .inl ⟨⟨_, (fam_eq hl).2⟩, hk⟩⟩)⟩
    | soReady _ hl hk =>
      exact .inr ⟨(fam_eq hl).1.symm, .inr (.inl ⟨hw, .inr (.inl ⟨⟨_, (fam_eq hl).2⟩, hk⟩)⟩)⟩
    | svDone _ hl hk =>
      exact .inr ⟨(fam_eq hl).1.symm,
        .inr (.inl ⟨hw, .inr (.inr ⟨⟨_, (fam_eq hl).2⟩, _, hk⟩)⟩)⟩
  · cases h with
    | qLoad _ hl _ | qArrive _ hl _ | qWait _ hl _ _ | qCommit _ hl _ | qCopyWait _ hl _ _
    | kvWait _ hl _ => rcases hs with rfl | rfl | rfl <;> nomatch (fam_eq hl).2
    | qkCommit hpc hl hk =>
      exact .inr ⟨(fam_eq hl).1.symm, .inl ⟨⟨hw, by omega⟩, .inl ⟨⟨_, .inl (fam_eq hl).2⟩, hk⟩⟩⟩
    | svCommit hpc hl hk =>
      exact .inr ⟨(fam_eq hl).1.symm, .inl ⟨⟨hw, by omega⟩, .inl ⟨⟨_, .inr (fam_eq hl).2⟩, hk⟩⟩⟩
    | soWait hpc hl hk =>
      exact .inr ⟨(fam_eq hl).1.symm, .inl ⟨⟨hw, by omega⟩, .inr ⟨⟨_, (fam_eq hl).2⟩, hk⟩⟩⟩
  · cases h with
    | qWait _ hl _ _ | lastWait _ hl _ _ | coordWait _ hl _ | freeWait _ hl _ | rawLoad _ hl _
    | rawArrive _ hl _ | coordFree _ hl _ =>
      rcases hs with rfl | rfl | rfl <;> nomatch (fam_eq hl).2
  · cases h with
    | freeWait _ hl _ | readyArrive _ hl _ =>
      rcases hs with rfl | rfl | rfl <;> nomatch (fam_eq hl).2
  · cases h with
    | qWait _ hl _ _ | rawWait _ hl _ | readyArrive _ hl _ | freeArrive _ hl _ =>
      rcases hs with rfl | rfl | rfl <;> nomatch (fam_eq hl).2
    | svWait _ hl hk =>
      exact .inr ⟨(fam_eq hl).1.symm, .inr (.inr ⟨hw, ⟨_, (fam_eq hl).2⟩, hk⟩)⟩

/-- **`qkDone s` of CTA `c` is a commit object of the CTA's MMA lane**, polled with offset 0. -/
theorem qkDone_obj (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hR : MbarRows P L X) (hI : InitRows L X) (hB : Bar0Rows L X)
    (hO : MmaOne L X) (c : Nat) (s : Fin 2) :
    Notify.Obj X (mbarLoc L c (.qkDone s)) (mmaLane L X c) (mbarLoc L c (.qkDone s)) 0 :=
  notify_of_uses hX hR (Nat.zero_le _) (initFirst hp hX hFw hR hI hB c (.qkDone s))
    fun he hm => by
    rcases score_use hR ⟨s, .inl rfl⟩ (Frame.lt_of_get hX he) he hm with hk | ⟨hc, ⟨hat,
      ⟨-, hk⟩ | ⟨⟨_, hf⟩, -⟩⟩ | ⟨-, ⟨-, hk⟩ | ⟨⟨_, hf⟩, -⟩ | ⟨⟨_, hf⟩, -⟩⟩ | ⟨-, ⟨_, hf⟩, -⟩⟩
    · exact .inl hk
    · have hy := laneOn_eq hO he (notUb_of_kind (mbar_kind hX hR he hm)) hat
      rw [hc] at hy
      exact .inr (.inr ⟨hy, hk⟩)
    · cases hf
    · exact .inr (.inl ⟨_, hk, fun _ => by omega⟩)
    all_goals cases hf

/-- **`soReady s` of CTA `c` is a unit object of warpgroup 0's 128 lanes**, polled with
offset 0. -/
theorem soReady_obj (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hR : MbarRows P L X) (hI : InitRows L X) (hB : Bar0Rows L X)
    (c : Nat) (s : Fin 2) :
    Unit.Obj X (mbarLoc L c (.soReady s)) 128 (wg0Lane L c) 0 :=
  unit_of_uses hX hR (by decide) (wg0Lane_inj L c) (Nat.zero_le _)
    (initFirst hp hX hFw hR hI hB c (.soReady s)) fun he hm => by
    rcases score_use hR ⟨s, .inr (.inl rfl)⟩ (Frame.lt_of_get hX he) he hm with hk | ⟨hc, ⟨-,
      ⟨⟨_, hf | hf⟩, -⟩ | ⟨-, hk⟩⟩ | ⟨hw, ⟨⟨_, hf⟩, -⟩ | ⟨-, hk⟩ | ⟨⟨_, hf⟩, -⟩⟩ |
      ⟨-, ⟨_, hf⟩, -⟩⟩
    · exact .inl hk
    · cases hf
    · cases hf
    · exact .inr (.inl ⟨_, hk, by omega⟩)
    · cases hf
    · obtain ⟨b, hb⟩ := wg0_lane hp hw
      rw [hc] at hb
      exact .inr (.inr ⟨⟨b, hb⟩, hk⟩)
    all_goals cases hf

/-- **`svDone s` of CTA `c` is a commit object of the CTA's MMA lane**, whose pollers of warps 4
and up (the dequant lanes) use offset 1. -/
theorem svDone_obj (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hR : MbarRows P L X) (hI : InitRows L X) (hB : Bar0Rows L X)
    (hO : MmaOne L X) (c : Nat) (s : Fin 2) :
    Notify.Obj X (mbarLoc L c (.svDone s)) (mmaLane L X c) (mbarLoc L c (.svDone s)) 1
      (fun h => 4 ≤ MbarRow.warp L h) :=
  notify_of_uses hX hR le_rfl (initFirst hp hX hFw hR hI hB c (.svDone s))
    fun he hm => by
    rcases score_use hR ⟨s, .inr (.inr rfl)⟩ (Frame.lt_of_get hX he) he hm with hk | ⟨hc, ⟨hat,
      ⟨-, hk⟩ | ⟨⟨_, hf⟩, -⟩⟩ | ⟨hw, ⟨⟨_, hf⟩, -⟩ | ⟨⟨_, hf⟩, -⟩ | ⟨-, q, hk⟩⟩ | ⟨-, -, hk⟩⟩
    · exact .inl hk
    · have hy := laneOn_eq hO he (notUb_of_kind (mbar_kind hX hR he hm)) hat
      rw [hc] at hy
      exact .inr (.inr ⟨hy, hk⟩)
    · cases hf
    · cases hf
    · cases hf
    · exact .inr (.inl ⟨q, hk, fun h4 => absurd hw.1 (by omega)⟩)
    · exact .inr (.inl ⟨_, hk, fun _ => Nat.mod_mod _ _⟩)

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
