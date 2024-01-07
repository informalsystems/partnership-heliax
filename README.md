---
visibility: PUBLIC
---

# Partnership Workspace _of_ Informal Systems ⨯ Heliax

This repository is a workspace for [Informal Systems](https://informal.systems/)
and [Heliax](https://heliax.dev/) to collaborate on the system designed and developed
by Heliax in the course of the partnership.

The collaboration has focused on the design, formal modelling and correctness verification of Namada's proof-of-stake system. Namada is a proof-of-stake L1 for interchain asset-agnostic privacy built on top of ABCI that enables multi-asset shielded transfers for any native or non-native asset. Namada is the first fractal instance in the Anoma ecosystem. [This blogpost](https://informal.systems/blog/checking-namada-proof-of-stake) describes partly our approach and results.

The artifacts and its current state is summarized in the following table:

| ID | Name  | State     | Description    |
| ------------------------------------------------------------- | -------------------------- | --------------- | ------------- |
| 1 | [Quint specification](PoS-quint/README.md) | Finalized Q4 2023  | Full specification with fast redelegation and rewards in Quint. We have used the spec not only to design the redelegation and reward features, but also to check the correctness of the overall design using Quint's simulator. |
| 2 | [TLA+ specification](PoS-tla/README.md) | Finalized Q1 2023 | TLA+ specification used to check that Namada’s epoched staking and slashing approaches are secure in executions of bounded length. The specification includes a set of simplifications to allow the model-checker to analyze larger executions. The main simplifications are: (i) single validator; (ii) one tx per epoch; (iii) the validator can misbehave at most once with the same stake. |
| 3 | [Model based testing framework](PoS-mbt/README.md) | Finalized Q1 2023 | The existing end-to-end test framework for Namada was adapted to support model-based testing with the goal of executing tests on Namada's proof of stake module using the TLA+ specification. |
| 4 | [Pseudocode specification](Deprecated/PoS-pseudocode/PoS-model-redelegation.md) | Deprecated | We have used the pseudocode model extensively during the first half of the collaboration but stop maintaining it in favor of the Quint spec (easier to maintain and keep consistent). The slashing and redelegation is not up-to-date and may contain errors. It does not model rewards. |

## Issues & PRs

In order to support asynchronous collaboration, technical discussions between
Informal Systems & Heliax will usually happen in the form of either Issues,
or WIP documents submitted as PRs (both in this repository).