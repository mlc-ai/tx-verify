-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Lib.BarOne
import Lemmas.Flow.NotBulk
import Lemmas.Flow.TmemOperands

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Lib
open PTX PTX.Flow

def zeroSite (p : Nat) := decide (p ∈ BarRow.fullZeroSites++BarRow.halfZeroSites)

private def zeroOpcode : Op → Bool
  | .barSync (.imm 0) true | .barSyncN (.imm 0) (.imm 128) true => true
  | _ => false

private theorem opcodes : (BarRow.fullZeroSites++BarRow.halfZeroSites).all
    (fun p => (kernel.code[p]?).any (fun ins => zeroOpcode ins.op))=true := by decide +kernel

/-- For ordinary events the decoded pc counts exactly one barrier-zero
arrival at every listed site and nowhere else. -/
theorem zero_event {L m X i e} (hX : Consistent L kernel Assumptions.all m X) (hb : L.block=256)
    (get : X.get i=some e) (nu : ∀ f, e.kind≠.ub f) :
    Execution.isBarId 0 e=zeroSite e.pc := by
  cases test : zeroSite e.pc with
  | false =>
    cases bar : Execution.isBarId 0 e with
    | false => rfl
    | true =>
      obtain ⟨p,k⟩ := e
      cases k <;> simp [Execution.isBarId] at bar
      subst bar
      obtain ⟨_,one|full|half⟩ := recorded_bar hX hb get
      · cases one.1
      · exact (Bool.noConfusion (test.symm.trans
          (decide_eq_true (List.mem_append_left _ full.2.2))))
      · exact (Bool.noConfusion (test.symm.trans
          (decide_eq_true (List.mem_append_right _ half.2.2))))
  | true =>
    obtain ⟨f,bad⟩|⟨_,ins,_,_,code,fire⟩ := get_source hX get
    · exact (nu f bad).elim
    have hit := List.all_eq_true.mp opcodes e.pc (of_decide_eq_true test)
    rw [code] at hit
    change zeroOpcode ins.op=true at hit
    unfold zeroOpcode at hit
    split at hit <;> try contradiction
    · rename_i op
      rw [op] at fire
      have kind : e.kind=.bar 0 none .sync := congrArg Event.kind fire.1
      simp [Execution.isBarId,kind]
    · rename_i op
      rw [op] at fire
      have kind := fires_barSyncN_imm (id := 0) (n := 128) (by decide) (by decide)
        (by decide) (by decide) (by rw [hb]; decide) fire
      have shape := congrArg Event.kind kind
      simp [Execution.isBarId,shape]

end PTX.Kernels.InklingRelDecode.Proof.Lib
