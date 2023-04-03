# Model Based Testing for Namada's Proof of Stake Module

## Executive Summary

In March 2023, Ranadeep undertook the task of executing model-based tests on
Namada's proof of stake module using a TLA+ specification provided by Manuel.
The goal was to generate valid and consistent traces as input data for a
generalized data-driven test harness. This report details the methodology,
framework, and findings of the model-based testing process.

## Table of Contents

1. [Introduction](#introduction)
2. [Model Based Testing Framework](#model-based-testing-framework)
3. [Test Parameters and Methodology](#test-parameters-and-methodology)
4. [Findings](#findings)
5. [Conclusion and Next Steps](#conclusion-and-next-steps)

## Introduction

Namada's proof of stake module was tested using model-based testing techniques,
where the TLA+ specification was used to generate valid and consistent traces.
These traces served as input data for the test harness. The test framework
employed eight types of transactions, executed by either normal account users or
validators. Invariants were also used to ensure consistency between the TLA+
trace data and the actual blockchain data.

## Model Based Testing Framework

The existing end-to-end test framework for Namada was adapted to support
model-based testing. A mini library was created at `mbt/mod.rs` in
`namada/tests/src/e2e` directory, which can be reused for any general system
implemented in Rust. The description of the model-based testing framework is
provided in a separate [readme file](mbt_doc.md).

In this project, the Informal Trace Format (ITF) is utilized to represent the
state of traces. ITF is a JSON-based data format, containing special types
designed for this purpose. For further information on the ITF format, please
refer to the
[official documentation](https://apalache.informal.systems/docs/adr/015adr-trace.html).

The ITF files are generated using the
[Apalache model checker](https://apalache.informal.systems), which processes
specifications authored by Manuel. Once the files are created, their paths are
dynamically provided to the testing framework. This approach enables seamless
integration of the model checking process into the project's testing pipeline.

## Test Parameters and Methodology

Several genesis parameters were controlled during the testing process:

- Number of validators
- Bonded stake
- Epoch duration
- Pipeline length
- Unbonding length

The transactions were mapped to function closures in Rust, and the trace states
were iterated over to execute each state action accordingly. Invariant hooks
were added at the end of each call, serving to maintain consistency between the
TLA+ trace data and the actual blockchain data.

## Findings

During the model-based testing process, two issues were discovered:

1. The blockchain does not progress. Collaborators suggest that when one
   validator is slashed and jailed, the logic may jail or shut down the other
   validator as well.
2. The blockchain crashes at runtime while processing a slash. Collaborators
   indicate that if the slashed amount is more than 1/3 (or 2/3) of the total
   validator power, it may cause this issue.

## Conclusion and Next Steps

Based on the findings, Manuel and the Anoma team are collaborating to address
the identified issues. Manuel is working on modifying the model and rerunning
the model-based tests, while the Anoma team continues to investigate the
problems. Further progress and updates will be provided as they become
available.

| **Parameter**         | **Value**                                                                                      |
| --------------------- | ---------------------------------------------------------------------------------------------- |
| **Date**              | Q1 2023                                                                                        |
| **Project**           | Namada's Proof of Stake Module                                                                 |
| **Testing Technique** | Model Based Testing with TLA+ Specification                                                    |
| **Issues Found**      | 1. Blockchain does not progress <br> 2. Blockchain crashes at runtime while processing a slash |
