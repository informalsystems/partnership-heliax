# Namada's Proof-of-Stake TLA+ Specification

The main focus of our TLA+ model is to check that Namada’s epoched staking and slashing approaches are secure, e.g., if an infraction is discovered on time, the validator is always slashed. The main concerns are the following. First, due to epoched staking, data structures are updated at different epoch offsets depending on the operation. Second, slashing is scattered throughout the code. For instance, users are only slashed when withdrawing tokens that were delegated to a misbehaving validator, while the validator is slashed as soon as the infraction is discovered.

## Simplifications

Considering the main concerns, our TLA+ model adopts the following simplifications:

- Namada’s PoS allows an arbitrary number of users and validators. Our model allows only a single validator and a bounded number of users.
- Namada’s PoS allows executing multiple user transactions per epoch. Our model considers that the system executes a single transaction per epoch.
- Our model considers that the validator can misbehave only once within an unbonding period and no more than twice in total. While this affects the completeness of the model by restricting the possible set of executions, it still allows us to check the properties we want, as we argue later.

The goal of these simplifications is to drastically decrease the state needed to represent the model without changing its behavior in a manner that prevents us from checking the required properties.

## A walk-through the TLA+ model

### Modeling the state

The main variables  defined by our model are: `balanceOf`, `bonded`, `unbonded`, `totalDeltas`, `totalUnbonded`, `totalDelegated`, `posAccount`, `slashPool` and `slashes`. Some of these variables are epoched. This means that the data is associated with a specific epoch.

- The variable `epoch` keeps track of the current epoch.
- The variable `balanceOf` keeps track of the balance of each user.
- The variable `bonded` keeps track of the tokens that each user has bonded. For each user, the variable stores a set of bond records. A bond record has two fields. An `amount` field that indicates the bonded amount, and the epoch at which the tokens were effectively bonded.
- The variable `unbonded` keeps track of the tokens that each user has unbonded. For each user, the variable stores a set of unbond records. An unbond record includes the amount of unbonded tokens, the epoch at which the unbonded tokens were bonded, and the epoch at which the tokens are effectively unbonded (withdrawable).
- The variable `totalDeltas` keeps track of the validator’s stake at a given epoch. The stake is the sum of all bonds. This variable encodes the validator’s voting power at a given epoch.
- The variable `totalUnbonded` keeps track of the set of bonds unbonded from the validator at a given epoch.
- The variable `totalDelegated` keeps track of the stake that each user has delegated to the validator.
- The variable `posAccount` keeps track of the balance of the PoS special account.
- The variable `slashPool` keeps track of the total amount of slashed tokens.
- The variable `slashes` keeps track of the already processed slashes. Each slash is represented by a slash record. A slash record includes the epoch of the infraction and a rate indicating how much should be slashed.

Our model is initialized assuming that all users start with the same initial balance (`initSupply`) and that the validator initially has `initValidatorStake`tokens bonded to itself. The default values for these constants are 10^27 and 10^21 respectively, but one can play with different values under the constraint that `initSupply` must be greater or equal to `initValidatorStake`. Thus, the variable `balanceOf` is initially `initSupply` for all users but for the validator, which is `initSupply-initValidatorStake`. The variable `totalDeltas` is initialized to `initValidatorStake`, as well as the `posAccount` variable. Furthermore, the validator’s entry in `bonded` includes a bond record to account for the validator’s initial self-bond, as well as the validator's entry in `totalDelegated` that it is set to `initValidatorStake` for the same reason. The remaining variables are either initialized to zero, e.g., `slashPool` and `totalUnbonded`, or to an empty set, e.g., `unbonded` and `slashes`.

### User transactions: the PoS system

We model three user transactions: delegate, unbond, and withdraw. Following, we describe what each transaction does and how they modify the variables.

The delegate transaction takes as arguments the user  delegating the tokens and the `amount`` to be delegated. The function first checks that the user has enough tokens. It then takes the following steps:

- It transfers `amount` from the user’s account to the PoS account. This is done by taking `amount` from `balanceOf[sender]` and adding it to `posAccount`.
- Next, a new bond record is created and appended to `bonded[sender]`. In Namada’s PoS, delegation only takes effect after the pipeline offset, thus the start field of the bond record is set to the current epoch + the pipeline offset, and the amount field is set to `amount`.
- Since the validator’s stake increases, we update `totalDeltas` accordingly. This only takes effect at the pipeline offset.
- Finally, we update the sender's entry in `totalDelegated` by adding `amount`.

The unbond transaction takes as arguments the user unbonding the tokens and the `amount` to be unbonded. The function first checks that the user has enough tokens delegated that have not been unbonded yet. It then takes the following steps:

- It iterates over the bonds until the sum of all iterated bonds hits `amount`. This is computed by the `ComputedUnbonds` function.
- The variable `unbonded[sender]` is updated with the unbonds produced when iterating over the `sender` bonds. For each iterated bond, the model creates a new unbond with ending epoch set to `epoch` plus the sum of the pipeline and unbonding offsets. This means that those unbonds cannot be withdrawn until that epoch.
- It removes all the iterated bonds from `bonded[sender]`.
- It updates `totalDeltas` and `totalUnbonded` at the pipeline offset to account for the unbonded tokens.
- Finally, we update the sender's entry in `totalDelegated` by subtracting `amount`.

The withdraw transaction takes as arguments the user. The function withdraws all tokens that are fully unbonded: those unbonds whose ending epoch has been reached. The function takes the following steps:

- It computes the set of unbonds that meet the criteria.
- For each unbond, it applies any processed slash. This is done by the function `ComputeAmountAfterSlashing`, which also sums them all in `amountAfterSlashing`.
- It transfers `amountAfterSlashing` from the `posAccount` to the user’s account.
- It removes the withdrawn unbonds.

### Allowed executions

The behaviour of the model is determined by the `Next` operator.

It alternates a user transaction with an `EndOfEpoch` event, which models what happens at the end of an epoch. Furthermore, an `Evidence` event can be scheduled between an `EndOfEpoch` and the execution of a user transaction. Nevertheless, this is not always allowed in order to satisfy Assumption #3.

The `Evidence` event models what happens when an infraction is submitted to the PoS system. The function first checks that the validator did not misbehave recently. Assuming that the infraction was committed at an epoch `e`, the function enqueues the evidence to be processed at the end of epoch determined by adding the unbonding offset to the epoch at which the infraction happened.

At the end of an epoch, the `EndOfEpoch` event is triggered. The main purpose of this function is to process enqueued evidence and slash the validator. Due to Assumption #3, there can only be one evidence to process at the end of each epoch. This is processed by computing the amount to be slashed, subtracting it from `totalDeltas` (effectively reducing the validator’s voting power), and moving the slashed amount to the slash pool.

## Semantic properties to check

In this section, we discuss what invariants we decided to check and why: what semantic properties they encode. Bear in mind that some of the following invariants, e.g., Invariant #1, hold given Assumption #3: a validator does not misbehave multiple times within the unbonding period.

### Invariant #1: the users' balance cannot become negative

The PoS system should disallow users’ balances to go negative. By Assumption #3, If a user's balance goes negative, then slashing is not well implemented.

### Invariant #2: the PoS balance is always greater or equal to zero

Although simple to check: we just need to check that `posAccount` is always greater or equal to zero, this is an important invariant. It guarantees that If an infraction is discovered in time and there are no repeated infractions within an unbonding period, then the PoS model guarantees slashing: any user whose bonds (including the validator’s self-bonds) were contributing to the misbehaving validator's voting power is slashed when withdrawing any of those bonds.

The logic is the following. When we slash a validator (reduce its voting power) at the end of an epoch, we move tokens from the `posAccount` to the `slashPool`. Thus, in the `posAccount`, we only have the bonded tokens that are withdrawable: this means, the bonded tokens minus the slashable amount. If a user is able to withdraw tokens that were contributing to the voting power of the misbehaving validator, then in an execution where all tokens are withdrawn, the `posAccount` should go negative.

### Invariant #3: if there are no bonds and all unbonds have been withdrawn, the PoS balance must be equal to zero

This implies that the implementation of the PoS account is correct. Tokens are moved to the PoS account when a user delegates tokens to a validator and taken from it when these are withdrawn. Thus, the PoS balance should be zero if there are no bonds and all unbonds have been withdrawn. Violating this invariant could for instance unveil problems with the slashing implementation.  

### Invariant #4: the validator's voting power at a given epoch is less or equal to the total amount of tokens delegated to that validator

This invariant may seem to be incorrect. One may think that the validator’s voting power and the total amount of tokens delegated should be equal. This is not the case in Namada’s PoS due to slashing being scattered throughout the implementation. When an infraction is found, the validator is slashed almost immediately, but its delegations are not updated. This is to avoid iterating over all bonds and unbonds, which could be expensive. Instead, users are slashed when withdrawing their tokens The invariant captures this. 

### Invariant #5: if no slashing occurs, the validator's voting power at a given epoch is equal to the total amount of tokens delegated to that validator

This is a refinement of Invariant #4. In the case that the validator does not misbehave, i.e., no slashing occurs, the validator’s voting powers and the sum of its delegations should match perfectly.

### Invariant #6: the total amount of tokens is constant

This implies that tokens cannot be created. The invariant is easy to check. Initially, the total number of tokens is the number of users multiplied by the initial supply. At any point of the execution, the sum of the users’ balances, the PoS balance, and the slash pool should match the initial number of tokens.

### Invariant #7: the validator’s voting power is greater or equal to zero

This invariant is the counterpart of Invariant #1: the same way that a user’s balance should not become negative, the validator’s voting power should not either (given Assumption #3).

### Invariant #8: a user cannot create money

This invariant complements Invariant #6 by guaranteeing that a user’s account cannot be greater than `initSupply`.

## Tutorial: Check it yourself!

Following, we present a short tutorial that explains how to check Namada’s PoS system using our TLA+ model from scratch. The process is fairly simple, it only includes three simple steps.

We have used Apalache - Informal’s in-house model checker. Apalache is a symbolic model checker for TLA+ that translates the verification problem to a set of logical constraints. In turn, these constraints are solved by Microsoft’s Z3  SMT solver. In the default mode, Apalache only analyzes executions of bounded length. This means that the properties below are only checked up to a certain execution length. Although this does not guarantee that these properties are satisfied in longer executions, when using a sufficiently long execution, one can argue it with reasonably high confidence.

### Step 1: Install Apalache

The installation is very simple from a prebuilt package. Detailed instructions can be found [here](https://apalache.informal.systems/docs/apalache/installation/jvm.html). We recommend installing version 0.30.1, which is the version of Apalache we used to check our TLA+ model.

### Step 2: Clone the TLA+ model

The TLA+ model is in a [github repository](https://github.com/informalsystems/partnership-heliax). You should clone it locally by following [these instructions](https://docs.github.com/en/repositories/creating-and-managing-repositories/cloning-a-repository).

### Step 3: Let’s check

The model is composed of three files:

- StakingRepeated.tla  specifies the model. 
- StakingRepeated_typedefs.tla  defines custom types aliases used by the other modules and Apalache.
- MC_StakingRepeated.tla instantiates the model in StakingRepeated.tla giving concrete values to `PipelineLenght` and `UnbondingLength`. This file also includes the invariants to check.

Apalache can be run in two modes: simulate and check. The simulate mode randomly picks a sequence of actions and checks the invariants for the subset of all executions which only admit actions in the selected order. The check mode checks invariants for all executions up to a configurable length. The simulate mode is typically faster, but it does not provide strong guarantees when an invariant is not violated.

To run Apalachein check mode, one needs to execute the following command:

`apalache-mc check --inv=TotalDeltasGreater MC_StakingRepeated.tla`

which tells Apalache to check if invariant TotalDeltasGreater can be violated by the model specified in  StalkingRepeated.tla in an execution of 10 steps.

To run Apalache in simulate mode, one just needs to substitute check with simulate. To learn how to play with other parameters such as the execution length, please check [Apalache's documentation](https://apalache.informal.systems/docs/apalache/running.html#1-model-checker-and-simulator-command-line-parameters).