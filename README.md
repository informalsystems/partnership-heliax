---
visibility: PUBLIC
---

# Partnership Workspace _of_ Informal Systems ⨯ Heliax

This repository is a workspace for [Informal Systems](https://informal.systems/)
and [Heliax](https://heliax.dev/) to collaborate on the system designed and developed
by Heliax in the course of the partnership.

## Issues & PRs

In order to support asynchronous collaboration, technical discussions between
Informal Systems & Heliax will usually happen in the form of either Issues,
or WIP documents submitted as PRs (both in this repository).

## Artifacts

The artifacts and its current state is summarized in the following table:

| ID | Name  | State     | Notes    |
| ------------------------------------------------------------- | -------------------------- | --------------- | ------------- |
| 1 | [Quint specification](PoS-quint/README.md) | Finalized Q4 2023  | Full specification with redelegation and rewards|
| 2 | [TLA+ specification](PoS-tla/README.md) | Finalized Q1 2023 | Simplifications: (i) single validator; (ii) one tx per epoch; (iv) the validator can misbehave at most once with the same stake |
| 3 | [Model based testing framework](PoS-mbt/README.md) | Finalized Q1 2023 | |
| 4 | [Pseudocode specification](Deprecated/PoS-pseudocode/PoS-model-redelegation.md) | Deprecated | The slashing and redelegation is not up-to-date and may contain errors. It does not model rewards. |