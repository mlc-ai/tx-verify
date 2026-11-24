-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Spec
public import Kernels.FlashMlaSparseDecodeH64.Assumptions
import Kernels.FlashMlaSparseDecodeH64.Proof.Correct

public section

namespace PTX.Kernels.FlashMlaSparseDecodeH64

open PTX

/-! ## Readings this result depends on

The checks in `Tools/reading_uses.py` derive this list from the instruction forms, launch data
and assumption constructors of the public statement.

- EXT-ISA and EXT-IMPORT connect the frozen compiled PTX with the ISA implemented by the hardware.
- EXT-LAUNCH and EXT-FAIR provide the launch obligations and fair scheduling of threads and
  asynchronous completions.
- EXT-ADDR-WRAP, EXT-CVTA and EXT-SHARED interpret address arithmetic, pointer conversion and
  decoded shared offsets.
- EXT-WARP, EXT-ELECT-SITE and EXT-WARP-INSTANCE identify warp lanes and the corresponding
  instances of elections, shuffles and votes.
- EXT-DEPENDENCY-ORDER uses causal order to distinguish executions of guarded uniform branches.
- EXT-BAR-PARTICIPANTS and EXT-BAR-ZERO-COUNT interpret the participants and explicit counts
  of named barriers.
- EXT-SETMAXNREG-VIRTUAL and EXT-SETMAXNREG-EFFECTIVE preserve the virtual register values and
  model the register-count change and return at each warp request.
- EXT-GRIDDEP-SINGLE interprets grid dependency instructions in this single-grid launch.
- EXT-ENDIAN and EXT-VECTOR-ELEM determine the byte order and element offsets of packed accesses.
- EXT-IEEE754 and EXT-FLOAT-BITS cover rounding and the storage of floating results as bits.
- EXT-UE8M0 gives the scale values for nonzero finite encodings. The kernel's conversion
  assumption also supplies the value at encoding zero.
- EXT-OBJECT-ORDER, EXT-ASYNC-OBJECT and EXT-ENABLES-OBJECT order actions and observations on
  each synchronization object.
- EXT-STAGE-ORDER orders asynchronous issue and completion and the collective's blocking return.
- EXT-INIT-FENCE-ARRIVE supplies the publication order for the initialized barriers.
- EXT-TMA-BOX-ALIGN, EXT-TMA-GEOMETRY and EXT-TMA-STORE-OOB govern the alignment, backing,
  and boundary handling of the tensor maps.
- EXT-TMA-GATHER4 lays the four selected cache rows out in the shared TMA box.
- EXT-READ-WAIT-ORDER orders bulk-store source reads observed by the read wait before subsequent
  generic accesses.
- EXT-TMEM-ALLOC-ORDER orders allocation-management requests in the CTA allocator history.
- EXT-TCALLOC-STORER and EXT-TMEM-ALLOC-RESULT-ORDER identify the shared allocation result
  writer and order the participating lanes' subsequent reads of that word.
- EXT-TMEM-LANE-FIELD maps Tensor Memory load and store addresses to their lane and column.
- EXT-TCFIG and EXT-TCCP give coordinate maps for MMA operands and results and for the query
  copy into Tensor Memory.
- EXT-TCACQUIRE and EXT-TC-EXEC-ORDER supply acquire and execution order for Tensor Core
  operations.
- EXT-TC-SOURCE-REUSE orders completed shared operand reads before reuse of the same bytes.
- EXT-TC-COMMIT-OPERAND-ORDER orders earlier operand writes before reuse through the
  observing commit, including reuse of the dequantization slot for output staging.
-/

/-- The frozen SM100 sparse decode head64 kernel satisfies its launch contract and exact
attention postcondition under the declared assumptions. -/
theorem correct {P : Params} {L : Launch} {mem0 : Mem0}
    (hpre : Pre P L mem0) : Correct kernel Assumptions.all L mem0 (Post P mem0) :=
  Proof.correct hpre

/-- Every admitted launch has a completed execution. -/
theorem completed_execution {P : Params} {L : Launch} {mem0 : Mem0}
    (hpre : Pre P L mem0) :
    ∃ X, Consistent L kernel Assumptions.all mem0 X ∧ Complete L X :=
  Proof.completed_execution hpre

/-- A completed execution realizes the exact attention result. -/
theorem realizable_result {P : Params} {L : Launch} {mem0 : Mem0}
    (hpre : Pre P L mem0) :
    ∃ X mf, Consistent L kernel Assumptions.all mem0 X ∧ Complete L X ∧
      IsFinal L mem0 X mf ∧ Post P mem0 mf :=
  Proof.realizable_result hpre

end PTX.Kernels.FlashMlaSparseDecodeH64
