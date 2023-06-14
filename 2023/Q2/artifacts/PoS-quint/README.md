# PoS Quint model

## Requirements

- [Quint](https://github.com/informalsystems/quint) (tested with v0.11.1)

## Resources

- [Quint cheatsheet](https://github.com/informalsystems/quint/blob/main/doc/quint-cheatsheet.pdf)
- [Quint tutorials](https://github.com/informalsystems/quint/tree/main/tutorials)

## Interact with the model in a REPL

```shell
# Load the main file
quint --require namada.qnt::namada
```

Then inside the Quint REPL:

```quint
// Initialize the state by executing the `init` action
init

// Run a step which executes one of the possible actions
step

// Evaluate the state of delegators (or any other var)
delegators

// Check which tx was executed by the step
lastTx
```

## Testing

To run successfully, you currently have to change `pure val enforceStateTransition = false` in namada.qnt before running tests.

The test `namadaScenarioTest` requires `UNBONDING_OFFSET == 4` and `PIPELINE_OFFSET == 2`.

```shell
quint test namada.qnt
```

### Run a simulator and check invariants

```shell
quint run --max-steps=20 --max-samples=100 --invariant=allInvariantsWithNoSlashPool namada.qnt
```
