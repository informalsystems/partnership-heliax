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

The artifacts for each engagement are gathered in a subdirectory named
after the year and quarter in which the project was carried out.

These artifacts include:

- The artifacts generated the course of the project.
- The artifacts under review, referenced as git submodules.

### Overview

The artifacts and its current state is summarized in the following artifacts table:

| ID | Name                                    | State     | WIP branch | Notes    |
| ------------------------------------------------------------- | -------------------------- | --------- | --------------- | ------------- |
| 1 | [Pseudocode model without redelegation](https://github.com/informalsystems/partnership-heliax/blob/trunk/2022/Q4/artifacts/PoS-pseudocode/PoS-model.md) | Finalized Q4 2024 | N/A | Models Namada's Cubic Proof-of-stake without redelegation |
| 2 | [TLA+ specification](https://github.com/informalsystems/partnership-heliax/tree/trunk/2023/Q1/artifacts/PoS-tla) | Finalized Q1 2023 | N/A | Simplifications w.r.t artifact #1: (i) it does not model validator's transactions; (ii) single validator; (iii) one tx per epoch; (iv) the validator can misbehave at most once with the same stake |
| 3 | [Model based testing framework](https://github.com/informalsystems/partnership-heliax/tree/trunk/2023/Q1/artifacts/PoS-mbt) | Finalized Q1 2023 | N/A | |
| 4 | [Pseudocode model with redelegation](https://github.com/informalsystems/partnership-heliax/blob/manuel/redelegation-q1/2023/Q1/artifacts/PoS-pseudocode/PoS-model-redelegation.md) | Ongoing | manuel/redelegation-q1 | Pending: (i) integrate the latest slashing with redelegation, which consists of integrating the cubic offset and preventing validators' stakes to become negative; and (ii) fix the issues found while modeling redelegation in Quint |
| 5 | [Quint specification without redelegation](https://github.com/informalsystems/partnership-heliax/blob/trunk/2023/Q2/artifacts/PoS-quint/namada.qnt) | Finalized Q2 2024 | N/A |  |
| 6 | [Quint specification with redelegation](https://github.com/informalsystems/partnership-heliax/tree/trunk/2023/Q3/artifacts/PoS-quint) | Ongoing | manuel/fix-slashValidator | Pending: fix `slashValidator` [#74](https://github.com/informalsystems/partnership-heliax/issues/74) |

### To clone just the artifacts Informal created during the audit

``` sh
git clone git@github.com:informalsystems/partnership-heliax.git
```

### To clone all artifacts, including Heliax's source code at the relevant commits

``` sh
git clone --recurse-submodules git@github.com:informalsystems/partnership-heliax.git
```


### To update the submodules if you've already cloned the repository

``` sh
git submodule init
git submodule update
```

### To add an artifact into an `artifacts` directory

```sh
git submodule add https://github.com/$CLIENT$/$PROJECT$
cd $PROJECT$
git checkout $TAG$
```

where $TAG$ is the tag or commit agreed to be under partnership.

Then

```sh
cd .. # back into the workspace repository
git commit -m "pin client artifact $PROJECT$"
```
