# Cluster launch control

How the model treats `clusterlaunchcontrol`: the arbitration that launches or cancels clusters, the responses to cancellation requests, and their delivery to the CTAs of a cluster. Concepts come first, then the rules.

Generated from the Lean comments of `Core/` and `Assumption/` by `Tools/coredoc.py`. Every entry links to the Lean source it was generated from. [All chapters](README.md).

## Contents

- [Concepts](#concepts)
  - [Arbitration](#arbitration)
    - [`Clc.Owner`](#c-clc-owner)
    - [`Clc.State`](#c-clc-state)
    - [`Clc.Step`](#c-clc-step)
    - [`Clc.ValidTask`](#c-clc-validtask)
    - [`Clc.ArbitrationOk`](#c-clc-arbitrationok)
    - [`Clc.Result`](#c-clc-result)
  - [Requests and effects](#requests-and-effects)
    - [`Clc.Spec`](#c-clc-spec)
    - [`Clc.Target`](#c-clc-target)
    - [`Clc.Effects`](#c-clc-effects)
    - [`Clc.ResponseWrite`](#c-clc-responsewrite)
    - [`Clc.Completion`](#c-clc-completion)
    - [`ClcCanceled`](#c-clccanceled)
- [Rules](#rules)
  - [What a cluster launch control instruction does](#what-a-cluster-launch-control-instruction-does)
    - [issuing requests and decoding cancellation responses](#thread-clc-query) (`THREAD-CLC-QUERY`)
  - [Which executions are allowed](#which-executions-are-allowed)
    - [atomic launch or cancellation of a cluster](#obj-clc-ownership) (`OBJ-CLC-OWNERSHIP`)
    - [responses derived from grid arbitration](#obj-clc-arbitration) (`OBJ-CLC-ARBITRATION`)
    - [per-CTA response writes and completion notifications](#dep-clc-effects) (`DEP-CLC-EFFECTS`)
    - [actual requests, arbitration and per-target effects](#obj-clc-origin) (`OBJ-CLC-ORIGIN`)
  - [What counts as an error](#what-counts-as-an-error)
    - [a request after an observed failure](#err-clc-request-after-failure) (`ERR-CLC-REQUEST-AFTER-FAILURE`)

## Concepts

The definitions a reader needs to follow the rules. Each text is the Lean doc comment, and each entry links to its Lean source.

### Arbitration

Who owns each cluster task and how requests are resolved.

<a id="c-clc-owner"></a>
#### `Clc.Owner`

*inductive*

Who has claimed a cluster task: the launch of the cluster, or the cancellation request that
canceled it.

- `launched`
- `canceled`

[Lean source: `Core/Clc/ClcOwnership.lean` L36-L41](../../Core/Clc/ClcOwnership.lean#L36-L41)

<a id="c-clc-state"></a>
#### `Clc.State`

*structure*

The arbitration state of a grid: the claim on each cluster task and the response to each
request.

- `owner`: The claim on each cluster task; `none` while it is unclaimed.
- `response`: None: unresolved; some none: failed; some (some task): successful.

[Lean source: `Core/Clc/ClcOwnership.lean` L43-L49](../../Core/Clc/ClcOwnership.lean#L43-L49)

<a id="c-clc-step"></a>
#### `Clc.Step`

*inductive*

One atomic step of scheduler arbitration: launching an unclaimed cluster, canceling an
unclaimed cluster for a fresh request, or failing a fresh request. It is neither the issue of
an instruction nor the write of its response.

- `launch`
- `success`
- `failure`

[Lean source: `Core/Clc/ClcOwnership.lean` L54-L67](../../Core/Clc/ClcOwnership.lean#L54-L67)

<a id="c-clc-validtask"></a>
#### `Clc.ValidTask`

*def*

`task` designates a cluster of a valid launch whose first CTA's coordinates fit in 32 bits.

[Lean source: `Core/Clc/ClcEffects.lean` L47-L51](../../Core/Clc/ClcEffects.lean#L47-L51)

<a id="c-clc-arbitrationok"></a>
#### `Clc.ArbitrationOk`

*def*

`state` is reachable from the empty ownership state by arbitration steps.

[Lean source: `Core/Clc/ClcEffects.lean` L53-L55](../../Core/Clc/ClcEffects.lean#L53-L55)

<a id="c-clc-result"></a>
#### `Clc.Result`

*def*

`r` is the response that `state` assigns to the request of event `i`.

[Lean source: `Core/Clc/ClcEffects.lean` L80-L82](../../Core/Clc/ClcEffects.lean#L80-L82)

### Requests and effects

The operands of a request and what it does in each target CTA.

<a id="c-clc-spec"></a>
#### `Clc.Spec`

*structure*

The operands of a cancellation request: the shared address of the response, the shared
address of the mbarrier to notify, and whether the response is multicast to the cluster.

- `response`
- `mbar`
- `multicast`

[Lean source: `Core/Clc/ClcEffects.lean` L112-L118](../../Core/Clc/ClcEffects.lean#L112-L118)

<a id="c-clc-target"></a>
#### `Clc.Target`

*def*

CTA `cta` is a target of the request that `issuer` issues: the issuing CTA, or with
multicast every CTA of its cluster.

[Lean source: `Core/Clc/ClcEffects.lean` L120-L128](../../Core/Clc/ClcEffects.lean#L120-L128)

<a id="c-clc-effects"></a>
#### `Clc.Effects`

*structure*

The effects of one request so far: its resolved response, and the CTAs that received the
response write and the completion notification.

- `resolved`: Arbitration has resolved; this is not a shared memory write.
- `written`: The target CTAs whose response write is present.
- `notified`: The target CTAs whose completion notification is present.

[Lean source: `Core/Clc/ClcEffects.lean` L130-L138](../../Core/Clc/ClcEffects.lean#L130-L138)

<a id="c-clc-responsewrite"></a>
#### `Clc.ResponseWrite`

*def*

The write of the 16-byte response into the response address of CTA `cta`.

[Lean source: `Core/Clc/ClcEffects.lean` L148-L151](../../Core/Clc/ClcEffects.lean#L148-L151)

<a id="c-clc-completion"></a>
#### `Clc.Completion`

*def*

The 16-byte complete-tx on the mbarrier of CTA `cta` that notifies the response write.

[Lean source: `Core/Clc/ClcEffects.lean` L153-L155](../../Core/Clc/ClcEffects.lean#L153-L155)

<a id="c-clccanceled"></a>
#### `ClcCanceled`

*def*

Thread `g` belongs to a canceled cluster, so it executes no instruction.

[Lean source: `Core/Clc/ClcExecution.lean` L53-L56](../../Core/Clc/ClcExecution.lean#L53-L56)

## Rules

Each rule is a contract block of the Lean source. Its statement says what the rule means for programs. The source quotes the PTX ISA 9.5 text the rule rests on, and the direction says how the rule relates to that text. Interpretations (EXT) are readings of the PTX text that the model adopts beyond what the text states. The fields that reviewers check against the Lean bodies are collected under Details for reviewers.

### What a cluster launch control instruction does

The events that issue a request and decode its response.

<a id="thread-clc-query"></a>
#### issuing requests and decoding cancellation responses (`THREAD-CLC-QUERY`)

*Rule* · [Lean comment: `Core/Clc/ClcThread.lean` L11-L33](../../Core/Clc/ClcThread.lean#L11-L33)

`clusterlaunchcontrol.try_cancel` issues an asynchronous request whose 16-byte aligned response is written to shared memory, and which notifies an mbarrier. The query instructions decode a response: the status gives whether a cluster was canceled, and a coordinate query gives a coordinate of the first CTA of the canceled cluster. A coordinate query of a failed response is a fault.

Source:

- 

Direction: `reading` (the entry relies on an interpretation or a named external fact)

Lean definitions: [`clcQueryValue`](../../Core/Clc/ClcThread.lean#L35-L43), [`clcTmpl`](../../Core/Clc/ClcThread.lean#L45-L60)

<details>
<summary>Details for reviewers</summary>

- §9.7.15.18–19
- EXT-CLUSTER-RANK (the first CTA's coordinates, OBJ-CLC-ARBITRATION)

**Applies:** Shared::cta try_cancel (including multicast) and scalar response queries

**Premises:** The operand is an opaque response; extracting coordinates requires a successful cancellation.

**Effect:** Asynchronous request issue or register update with explicit response observation. The response write is the effect of DEP-CLC-EFFECTS. The vector query form is unsupported by the decoder.

</details>

### Which executions are allowed

The arbitration history, the responses derived from it and the per-CTA effects.

<a id="obj-clc-ownership"></a>
#### atomic launch or cancellation of a cluster (`OBJ-CLC-OWNERSHIP`)

*Rule* · [Lean comment: `Core/Clc/ClcOwnership.lean` L10-L33](../../Core/Clc/ClcOwnership.lean#L10-L33)

Each cluster of the grid is either launched or canceled, and only while no one has claimed it. A successful cancellation request claims exactly one unclaimed cluster, which stays assigned to that request; a failed request claims no cluster. Each request is resolved once. Task identifiers are abstract cluster identities; they are not CTA ranks or output tile numbers. A canceled task stays assigned to its successful request, including after the requesting cluster exits. Multicast copies of one response retain the same request identity.

Source:

- 

Direction: `reading` (the entry relies on an interpretation or a named external fact)

Lean definitions: [`Clc.Owner`](../../Core/Clc/ClcOwnership.lean#L36-L41) ([concept](#c-clc-owner)), [`Clc.State`](../../Core/Clc/ClcOwnership.lean#L43-L49) ([concept](#c-clc-state)), [`Clc.initial`](../../Core/Clc/ClcOwnership.lean#L51-L52), [`Clc.Step`](../../Core/Clc/ClcOwnership.lean#L54-L67) ([concept](#c-clc-step)), [`Clc.StateExtends`](../../Core/Clc/ClcOwnership.lean#L69-L72)

<details>
<summary>Details for reviewers</summary>

- §9.7.15.18 (clusterlaunchcontrol.try_cancel)

**Applies:** Cluster tasks of one grid and distinct dynamic cancellation requests

**Premises:** Task identifiers designate clusters in that grid; request identifiers designate individual dynamic requests.

**Effect:** An ownership history for launch/cancellation arbitration only; no ordering of kernel instructions or memory accesses. Execution.clcState stores this common arbitration state. ClcOk connects it to actual requests and launched traces; separate rules connect responses, notifications and failure observations.

</details>

<a id="obj-clc-arbitration"></a>
#### responses derived from grid arbitration (`OBJ-CLC-ARBITRATION`)

*Rule* · [Lean comment: `Core/Clc/ClcEffects.lean` L16-L42](../../Core/Clc/ClcEffects.lean#L16-L42)

The response to a cancellation request is the outcome that arbitration assigned to that request: failure, or the canceled cluster, reported as the coordinates of its first CTA. The response does not carry the shape of the cluster. Arbitration chooses among the clusters of the launch's placement, of either shape. The canceled CTAs are those of the canceled cluster (`Launch.clusterOfCta`, OBJ-CLC-OWNERSHIP). All requests of an execution share one arbitration history that starts from the empty ownership state.

Source:

- 

Direction: `scope` (the supported fragment or launch scope is restricted)

Lean definitions: [`Clc.requestId`](../../Core/Clc/ClcEffects.lean#L44-L45), [`Clc.ValidTask`](../../Core/Clc/ClcEffects.lean#L47-L51) ([concept](#c-clc-validtask)), [`Clc.validTask_oneDim`](../../Core/Clc/ClcEffects.lean#L72-L78), [`Clc.ArbitrationOk`](../../Core/Clc/ClcEffects.lean#L53-L55) ([concept](#c-clc-arbitrationok)), [`Clc.responseOf`](../../Core/Clc/ClcEffects.lean#L57-L62), [`Clc.responseOf_oneDim`](../../Core/Clc/ClcEffects.lean#L64-L70), [`Clc.Result`](../../Core/Clc/ClcEffects.lean#L80-L82) ([concept](#c-clc-result))

<details>
<summary>Details for reviewers</summary>

- §9.7.15.18 (unique canceled cluster and its first CTA)
- EXT-CLUSTER-RANK (the first CTA of cluster `t` is its CTA of rank 0, CTA number
    `Launch.clusterStart t`, whose `%ctaid` is the cluster's origin; in a one-dimensional launch it
    is `(t * clusterSize, 0, 0)`)
- EXT-PREFERRED-CLUSTER

**Applies:** Launches of any shape, with 32-bit CTA coordinates

**Premises:** One common arbitration state is reachable from the empty grid ownership state. Dynamic requests are identified by their actual issuing event.

**Effect:** Connects response payloads to the launch/cancellation ownership rules. The state must be shared by all requests of an execution; a response does not choose its own state.

</details>

<a id="dep-clc-effects"></a>
#### per-CTA response writes and completion notifications (`DEP-CLC-EFFECTS`)

*Rule* · [Lean comment: `Core/Clc/ClcEffects.lean` L84-L109](../../Core/Clc/ClcEffects.lean#L84-L109)

A cancellation request writes one 16-byte response to the response address in each target CTA, which is the issuing CTA or, with multicast, every CTA of its cluster. It then signals a 16-byte complete-tx on the mbarrier of that CTA. All copies carry the same response, and each write follows the resolution of the request and each notification follows its write.

Source:

- 

Direction: `reading` (the entry relies on an interpretation or a named external fact)

Lean definitions: [`Clc.Spec`](../../Core/Clc/ClcEffects.lean#L112-L118) ([concept](#c-clc-spec)), [`Clc.Target`](../../Core/Clc/ClcEffects.lean#L120-L128) ([concept](#c-clc-target)), [`Clc.Effects`](../../Core/Clc/ClcEffects.lean#L130-L138) ([concept](#c-clc-effects)), [`Clc.EffectsOk`](../../Core/Clc/ClcEffects.lean#L140-L146), [`Clc.ResponseWrite`](../../Core/Clc/ClcEffects.lean#L148-L151) ([concept](#c-clc-responsewrite)), [`Clc.Completion`](../../Core/Clc/ClcEffects.lean#L153-L155) ([concept](#c-clc-completion)), [`Clc.Extends`](../../Core/Clc/ClcEffects.lean#L157-L159)

<details>
<summary>Details for reviewers</summary>

- §9.7.15.18 (try_cancel, multicast and complete-tx)

**Applies:** One issued cancellation request with local shared response/mbarrier addresses, optionally multicast to every CTA of its cluster

**Premises:** The response is a result of this dynamic request. Writes and notifications target only the selected CTAs. A notification requires that CTA's response write.

**Effect:** Operation-local effects; their stage order (issue → resolve → write c → notify c) is `StageOrder` (DEP-ASYNC-STAGE-ORDER). A response failure is also written and notified. Neither it nor a successful response implicitly completes a memory write. A notification in one CTA does not establish that another CTA's copy or notification is present. The response location and mbarrier keep their offsets in every target CTA. Execution.clc stores these effects; the active memory and object queries use them.

</details>

<a id="obj-clc-origin"></a>
#### actual requests, arbitration and per-target effects (`OBJ-CLC-ORIGIN`)

*Rule* · [Lean comment: `Core/Clc/ClcExecution.lean` L11-L36](../../Core/Clc/ClcExecution.lean#L11-L36)

Every resolved request, response write and notification comes from an actual cluster launch control instruction, and all requests share one arbitration history. A cluster that is already running cannot be canceled, and a successful response names a canceled cluster that no other request has claimed. A target observes a response only through the notification to its own CTA.

Source:

- 

Direction: `reading` (the entry relies on an interpretation or a named external fact)

Lean definitions: [`ClcOk`](../../Core/Clc/ClcExecution.lean#L38-L51), [`ClcCanceled`](../../Core/Clc/ClcExecution.lean#L53-L56) ([concept](#c-clccanceled))

<details>
<summary>Details for reviewers</summary>

- §9.7.15.18–19

**Applies:** Actual CLC request events in the current one-dimensional launch

**Premises:** All requests share one reachable arbitration state; every resolved request and every nonempty effect has an actual issue event. Nonempty thread traces belong to launched clusters when CLC is used.

**Effect:** Consistent.clc and completion observation; ordinary memory read-source and safety checks remain independent. A target observes the response through the notification to its own CTA as OBJ-MBAR-OBSERVE defines it (`AsyncCopy.Notifies`). Before any CLC request, arbitration may remain implicit. Once a request appears, every nonempty trace's cluster must be recorded as launched, which also prevents canceling an earlier-started cluster when extending a prefix. Empty canceled threads execute no exit; ClcCanceled accounts for them in the completion definition.

</details>

### What counts as an error

Cluster launch control uses that are rejected as unsafe.

<a id="err-clc-request-after-failure"></a>
#### a request after an observed failure (`ERR-CLC-REQUEST-AFTER-FAILURE`)

*Rule* · [Lean comment: `Core/Assembly/Safety.lean` L336-L358](../../Core/Assembly/Safety.lean#L336-L358)

An execution is unsafe when a CLC request does not precede, in base causality order (`baseCausality`), a query in its CTA that observes a failed cancellation.

Source:

- 

Direction: `stricter` (the entry uses a stricter protocol; review its exact effect on executions and rejection)

Lean definitions: [`ClcUnsafe`](../../Core/Assembly/Safety.lean#L360-L365)

<details>
<summary>Details for reviewers</summary>

- §9.7.15.18 (request after observed failure)

**Applies:** Actual CLC issues and response observations

**Premises:** A request can follow an observed failure in its CTA.

**Effect:** Unsafe check. Outstanding response footprints also participate in races, and each target's notification is a use of its shared memory (ERR-SHARED-LIFETIME). The response mbarrier of each target CTA is an mbarrier operand of the request (`UsesMbar`): its initialization is ERR-MBAR-UNINITIALIZED and its storage ERR-UNALLOCATED-ACCESS.

</details>
