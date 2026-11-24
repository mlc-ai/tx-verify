-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Audit.PrefixRun
public import Core.Assembly.Correctness
import Lemmas.Clc.ClcExecution
import Lemmas.Flow.Final

/-! Connect the immutable read oracle to the actual memory model and all threads in one launch. -/
@[expose] public section
namespace FlashKda.Prefix
open PTX
noncomputable section

/-- Only the bytes of the input array are constrained at launch. -/
def initialized (mem : Mem0) (base : Nat) (offsets : List Nat) : Prop :=
  ∀ loc b, inputByte base offsets loc = some b → mem loc = some (some b)

theorem respects_memory {L mem X base offsets id e}
    (hx : Consistent L Decoded.kernel [readonly] mem X)
    (init : initialized mem base offsets) (he : X.get id = some e) : respects base offsets e := by
  obtain ⟨pc, kind⟩ := e
  cases kind <;> try trivial
  case nc a bs =>
    intro site data hd
    have wf := hx.asm readonly (by simp) id pc a bs he site
    have hlen : data.length = a.size := by simpa [readBytes] using congrArg List.length hd
    apply List.ext_getElem?
    intro i
    by_cases hi : i < a.size
    · have hdi : i < data.length := hlen ▸ hi
      have hb : inputByte base offsets (a.loc.at i) = some data[i] := by
        have eq := congrArg (fun l : List (Option Byte) => l[i]?) hd
        simpa [readBytes, hi, hdi] using eq.symm
      have obs := wf.2 i hi (some data[i]) (init _ _ hb)
      simpa [Execution.initialByte, hdi] using obs
    · simp [List.getElem?_eq_none (by omega : bs.length ≤ i),
            List.getElem?_eq_none (by omega : data.length ≤ i)]

/-- There is one thread block. A cancellation would require an issuing thread in that same
cluster, but a cluster containing an issuing thread has already been launched. -/
theorem uncanceled {n input output mem X g}
    (hx : Consistent (launch n input output) Decoded.kernel [readonly] mem X)
    (hg : g < 32) : ¬ ClcCanceled (launch n input output) X g := by
  rintro ⟨_, request, owner⟩
  obtain ⟨i, s, dest, _, issue, _⟩ := hx.clc.canceled_has_issue owner
  obtain ⟨pc, get⟩ := issue
  have nonempty : X.tr i.1 ≠ [] := by
    intro hempty
    simp [Execution.get, hempty] at get
  have hin : i.1 < (launch n input output).threads := by
    by_contra! hn
    exact nonempty (hx.outside i.1 hn)
  have hin32 : i.1 < 32 := hin
  have howner := hx.clc.running_not_canceled ⟨i, s, dest, pc, get⟩ (request := request) hin nonempty
  have eqBlock : i.1 / (launch n input output).block = g / (launch n input output).block := by
    change i.1 / 32 = g / 32
    rw [Nat.div_eq_of_lt hin32, Nat.div_eq_of_lt hg]
  rw [eqBlock] at howner
  exact howner owner

theorem run_with_exit {K A L g t es o pc}
    (run : Run K A L g t es o) (exit_mem : (⟨pc, .exit⟩ : Event) ∈ es) : o = none := by
  induction run with
  | nil => simp at exit_mem
  | step path step tail ih =>
    rcases List.mem_cons.mp exit_mem with he | hm
    · subst he
      obtain ⟨_, _, fire⟩ := step
      cases Flow.fires_end_none fire (Or.inr rfl)
    · exact ih hm
  | last => rfl

/-- Any complete consistent execution has the certified per-thread trace when its immutable
input bytes are present. Memory outside that input may be arbitrary. -/
theorem global_trace {n input output g offsets mem X es}
    (hx : Consistent (launch n input output) Decoded.kernel [readonly] mem X)
    (done : Complete (launch n input output) X) (hg : g < 32)
    (init : initialized mem input offsets)
    (cert : Exact [readonly] (launch n input output) g input offsets {} es) : X.tr g = es := by
  obtain ⟨o, run⟩ := hx.thr g hg
  rcases done.1 g hg with canceled | ⟨pc, last⟩
  · exact (uncanceled hx hg canceled).elim
  have exit_mem := List.mem_of_getLast? last
  obtain rfl := run_with_exit run exit_mem
  apply cert.unique _ run
  intro e he
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp he
  exact respects_memory (id := (g,k)) hx init hk

end
end FlashKda.Prefix
