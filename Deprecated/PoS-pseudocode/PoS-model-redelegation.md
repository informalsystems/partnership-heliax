# Namada's Cubic Proof-of-Stake

- [Namada's Cubic Proof-of-Stake](#namadas-cubic-proof-of-stake)
  - [Assumptions/simplifications](#assumptionssimplifications)
  - [Definitions](#definitions)
    - [Redelegations' Specific Terminology](#redelegations-specific-terminology)
  - [Technical Specification](#technical-specification)
    - [Data types](#data-types)
    - [Constants](#constants)
    - [Variables](#variables)
    - [Validator transactions](#validator-transactions)
    - [Bonding Mechanism Transactions](#bonding-mechanism-transactions)
    - [Main PoS functions](#main-pos-functions)
    - [Validator's functions](#validators-functions)
    - [Auxiliary functions](#auxiliary-functions)

## Assumptions/simplifications

- There is a single token type
- There is an initial set of active and inactive validators
- There are always enough non-jailed, candidate validators to fulfill the active set of validators at any given epoch

## Definitions

- `pipeline_length` and `unbonding_length` define two epoch offsets. Note that `unbonding_length` must be greater than or equal to `pipeline_length`.

### Redelegations' Specific Terminology

- A redelegation involves two validators. We use `source validator` to refer the validator from which the tokens are taken and `destination validator` to refer to the validator to which the tokens are delegated.

- Given a `redelegation`, the `redelegation's starting epoch` is the epoch at which the redelegation transaction is processed. The `redelegation's ending epoch` is the epoch at which the redelegated tokens start contributing to the destination delegator. In the current design, if a redelegation's starting epoch is `e`, then its ending epoch would be `e + pipeline_length`. In the text throughout the specification, for a given `redelegation`, we use `redelegation.start` and `redelegation.end` to refer to the starting and ending epoch of the redelegation.

- A redelegation is composed of one or more bonds (aka `redelegation bonds`). Each redelegation bond is a pair of the epoch at which the redelegated tokens started contributing to the stake of the source validator and the amount of tokens. It is important to keep track of the starting epochs in order to apply slashes precisely.

- Given a redelegation, we call `redelegation slashing window` the set of consecutive epochs in which the tokens redelegated to the destination validator may be slashed due to a misbehaviour of the source validator.
  - In the current design, the redelegation slashing window of a redelegation spans from `redelegation.start - unbonding_length` up to `redelegation.end - 1`.
  - The window's lower bound is determined by the fact that when a redelegation is created, we apply all slashes of the source validator already known. This means any slash for an infraction committed at an epoch `< redelegation.start - unbonding_length`.
  - The window's upper bound is determined by the epoch at which the redelegated tokens stop contributing to the stake of the source validator.

The aim of these bounds is to provide consistent accountability, in that any stake contributing to an infraction will be punished proportionally regardless of when the infraction is detected.

- We say a redelegation is a `chain redelegation` when the source validator redelegates some tokens that were redelegated by a second validator while infractions of the latter validator can still be processed. In the current design, a redelegation is considered a chain redelegation if already redelegated tokens are redelegated before the end of the initial redelegation `+ unbonding_length`. This is simple to compute:
  - Let `redelegation` be the initial redelegation and assume that `redelegation.start = e`.
  - The redelegation slashing window then spans from `redelegation.start - unbonding_length` up to `redelegation.end - 1`. Thus, the last epoch at which the source validator may misbehave and we need to account for it is `redelegation.end - 1 = redelegation.start + pipeline_length - 1 = e + pipeline_length - 1`.
  - An infraction is processed after `unbonding_length` epochs from the misbehaving epoch. Thus, if the source validator misbehaves at `redelegation.end - 1`, the infraction will be processed at the end of epoch `redelegation.end - 1 + unbonding_length`.
  - Therefore, a redelegation of the redelegated tokens of `redelegation` is only considered a chain redelegation if it occurs before `redelegation.end + unbonding_length` as required.

## Technical Specification

### Data types

```go
type Addr
type Key
type Epoch uint
type VotingPower uint

type JailRecord struct {
  is_jailed bool
  epoch Epoch
}

type UnbondRecord struct {
  start Epoch
  amount uint
}

type SlashedAmount struct {
  epoch Epoch
  amount uint
}

type Validator struct {
  consensus_key map<Epoch, Key>
  state map<Epoch, {inactive, candidate}>
  total_deltas map<Epoch, amount:int>
  total_unbonded map<(Epoch, Epoch), int>
  total_redelegated_unbonded map<(Epoch, Epoch), map<Addr, int>>
  voting_power map<Epoch, VotingPower>
  reward_address Addr
  jail_record JailRecord
  frozen map<Epoch, bool>
  incoming_redelegations map<Addr, map<Addr, int>>
  outgoing_redelegations map<Addr, map<Addr, map<(Epoch, Epoch), int>>>
}

type Bond struct {
  validator Addr //not used
  source Addr //not used
  deltas map<start:Epoch, int>
}

type Unbond struct {
  validator Addr //not used
  source Addr //not used
  deltas map<(start:Epoch, end:Epoch), int>
}

type Slash struct {
  epoch Epoch
  validator Addr
  rate float
  stake_fraction float //new in cubic slashing
}

type Redelegation struct {
  validator Addr
  bonds map<Epoch, int> // map from bond start epoch to bond amount
}

type WeightedValidator struct {
  validator Addr
  voting_power VotingPower
}

type ValidatorSet struct {
  active orderedset<WeightedValidator>
  inactive orderedset<WeightedValidator>
}
```

### Constants

```go
pipeline_length uint
unbonding_length uint
min_sentence uint
votes_per_token uint
duplicate_vote_rate float
light_client_attack_rate float
```

### Variables

```go
cur_epoch ← 0 in Epoch //current epoch

validators[] in Addr → Validator //map from address to validator
balances[] in Addr → int //map from address to integer
bonds[][] in (Addr X Addr) → Bond //map from address to map from address to bond
unbonds[][] in (Addr X Addr) → Unbond  //map from (address, address) to unbond
redelegated_bonds[][][] in (Addr X Addr X Epoch) → Redelegation //map from (address, address, epoch) to redelegation
redelegated_unbonds[][][] in (Addr X Addr X (Epoch, Epoch)) → Redelegation //map from (address, address, (epoch, epoch)) to redelegation
slashes[] in Addr → 2^Slash //map from address to list of slashes
enqueued_slashes[] in Epoch → 2^Slash //map from epoch to list of slashes

validator_sets[] in Epoch → ValidatorSet //map from epoch to validator_set
total_voting_power[] in Epoch to VotingPower //map from epoch to voting_power
```

### Validator transactions

```go
tx_become_validator(validator_address, consensus_key, staking_reward_address)
{
  // check that become_validator has not been called before for validator_address
  var state = read_epoched_field(validators[validator_address].state, cur_epoch+pipeline_length, ⊥)
  if (state == ⊥ && validator_address != staking_reward_address) then
    validators[validator_address].reward_address = staking_reward_address
    // set status to candidate and consensus key at n + pipeline_length
    validators[validator_address].consensus_key[cur_epoch+pipeline_length] = consensus_key
    validators[validator_address].state[cur_epoch+pipeline_length] = candidate
    validators[validator_address].jail_record = JailRecord{is_jailed: false, epoch: ⊥}
    validators[validator_address].frozen[cur_epoch] = false
    // add validator to the inactive set
    add_validator_to_sets(validator_address, pipeline_length)

}
```

```go
/* COMMENT
  - https://github.com/informalsystems/partnership-heliax/issues/10
    issue about bonds and deactivation
    conclusion: leave it as it is for the moment.
*/
tx_deactivate(validator_address)
{
  var state = read_epoched_field(validators[validator_address].state, cur_epoch+pipeline_length, ⊥)
  if (state == candidate) then
    // set status to inactive at n + pipeline_length
    validators[validator_address].state[cur_epoch+pipeline_length] = inactive
    remove_validator_from_sets(validator_address, pipeline_length)
    update_total_voting_power(pipeline_length)
}
```

```go
tx_reactivate(validator_address)
{
  var state = read_epoched_field(validators[validator_address].state, cur_epoch+pipeline_length, ⊥)
  if (state == inactive && !is_jailed(validator_address)) then
    // set status to candidate at n + pipeline_length
    validators[validator_address].state[cur_epoch+pipeline_length] = candidate
    // add validator to the inactive set
    add_validator_to_sets(validator_address, pipeline_length)
    update_total_voting_power(pipeline_length)
}
```

```go
tx_unjail(validator_address)
{
  // check validator is jailed and can be unjailed
  var epochs_jailed = cur_epoch + pipeline_length - validators[validator_address].jail_record.epoch
  if (is_jailed(validator_address) && (epochs_jailed > min_sentence)) then
    validators[validator_address].jail_record = JailRecord{is_jailed: false, epoch: ⊥}
    var state = read_epoched_field(validators[validator_address].state, cur_epoch+pipeline_length, ⊥)
    // add the validator to the validator sets if it is a candidate by pipeline_length
    if (state == candidate) then
      add_validator_to_sets(validator_address, pipeline_length)
      update_total_voting_power(pipeline_length)
}
```

```go
tx_change_consensus_key(validator_address, consensus_key)
{
  //set consensus key at n + pipeline_length
  validators[validator_address].consensus_key[cur_epoch+pipeline_length] = consensus_key
}
```
### Bonding Mechanism Transactions

The transaction `tx_self_bond` calls the `bond` function to self-bond `amount` tokens to a validator `validator_address`.

```go
tx_self_bond(validator_address, amount)
{
  bond(validator_address, validator_address, amount, pipeline_length)
}
```

The transaction `tx_delegate` calls the `bond` function to delegate `amount` tokens belonging to a delegator `delegator_address` to a validator `validator_address`.

```go
tx_delegate(validator_address, delegator_address, amount)
{
  bond(validator_address, delegator_address, amount)
}
```

The transaction `tx_unbond` calls the `unbond` function to unbond `amount` self-bond tokens from a validator `validator_address`.

```go
tx_unbond(validator_address, amount)
{
  unbond(validator_address, validator_address, amount)
}
```

The transaction `tx_undelegate` calls the `unbond` function to unbond `amount` tokens from a validator `validator_address` previously delegated by a delegator `delegator_address`.

```go
tx_undelegate(validator_address, delegator_address, amount)
{
  unbond(validator_address, delegator_address, amount, "")
}
```

The transaction `tx_withdraw_unbonds_validator` calls the `withdraw` function to withdraw all tokens that `validator_address` has unbonded from itself.

```go
tx_withdraw_unbonds_validator(validator_address)
{
  withdraw(validator_address, validator_address)
}
```

The transaction `tx_withdraw_unbonds_delegator` calls the `withdraw` function to withdraw all tokens that a delegator `delegator_address` has unbonded from a validator `validator_address`.

```go
tx_withdraw_unbonds_delegator(delegator_address)
{
  forall (validator_address in validators) do
    withdraw(validator_address, delegator_address)
}
```

The transaction `tx_redelegate` creates a redelegation from source validator `src_validator_address` to `dest_validator_address` for any tokens that a delegator `delegator_address` has currently delegated to the source validator. The transaction takes the following steps:

1. The function first checks that the source validator is not frozen. This is to prevent unbonding at an epoch `e` from a validator that is known to have misbehaved, but the slash has not been processed yet.
2. Then it checks that the redelegation is not a chain redelegation, in which case it prevents it by returning.
   - The design does not track chain redelegation precisely.
   - Instead approximates it by preventing a validator from redelegating tokens belonging to a delegator if it has received a redelegation of tokens belonging to the same delegator that ended less than `unbonding_length` epochs ago. Please read the definition of chain redelegation in [Definitions](#definitions) for more details.
   - The `incoming_redelegations` variable is used to implement this mechanism.
3. The function computes the total amount of tokens that the delegator has bonded at the source validator (`bonded_tokens`).
4. It unbonds `bonded_tokens` from the source validator indicating that it is a redelegation by calling `unbond` with the delegator's address.
5. It creates the bond at the destination validator.
6. It stores the redelegation's end epoch in the destination validator's `incoming_redelegations` variable.
7. It finally updates the destination validator `total_deltas`, voting power, total voting power and validator sets.

```go
tx_redelegate(src_validator_address, dest_validator_address, delegator_address)
{
  // Disallow re-delegation if the source validator is frozen (similar to unbonding)
  var src_frozen = read_epoched_field(validators[src_validator_address].frozen, cur_epoch, false)
  if (is_validator(src_validator_address, cur_epoch+pipeline_length) && src_frozen == false) then
    // Check that `incoming_redelegations[delegator_address]` for `src_validator_address` either don't exist
    // or if they do, they cannot be slashed anymore (`end + unbonding_length <= cur_epoch`)
    var end_epoch_redelegation = validators[src_validator_address].incoming_redelegations[delegator_address]
    if (end_epoch_redelegation >= 0 && end_epoch_redelegation + unbonding_length > cur_epoch) then
      return
    // Find the sum of bonded tokens to `src_validator_address`
    var delbonds = {<start, amount> | amount = bonds[delegator_address][src_validator_address].deltas[start] > 0 && start <= cur_epoch + unbonding_length}
    var bonded_tokens = sum{amount | <start, amount> in delbonds}
    // Unbond the tokens from `src_validator_address` at pipeline offset
    var amount_after_slashing = unbond(src_validator_address, delegator_address, bonded_tokens, dest_validator_address)
    // add a bond in the `dest_validator_address` for the amount after slashing
    // done manually to avoid account transfer
    bonds[delegator_address][dest_validator_address].deltas[cur_epoch+pipeline_length] += amount_after_slashing
    // save the epoch at which the redelegation occurs to track chained redelegations
    validators[dest_validator_address].incoming_redelegations[delegator_address] = cur_epoch + pipeline_length
    update_total_deltas(dest_validator_address, pipeline_length, amount_after_slashing)
    update_voting_power(dest_validator_address, pipeline_length)
    update_total_voting_power(pipeline_length)
    update_validator_sets(dest_validator_address, pipeline_length)
}
```

### Main PoS functions

The `bond` function delegates `amount` tokens belonging to a delegator `delegator_address` to a validator `validator_address`. It takes the following steps:

1. It checks that `validator_address` is a validator and that the delegator has enough balance.
2. Then it registers a bond with start epoch `cur_epoch+pipeline_length` of `amount` tokens.
3. It transfers `amount` from the delegator's account to the PoS account.
4. It finally updates the destination validator `total_deltas`, voting power, total voting power and validator sets.

```go
func bond(validator_address, delegator_address, amount)
{
  if (is_validator(validator_address, cur_epoch+pipeline_length) && 
     balances[delegator_address] >= amount) then
    // add amount bond to delta at n+pipeline_length
    bonds[delegator_address][validator_address].deltas[cur_epoch+pipeline_length] += amount
    // debit amount from delegator account and credit it to the PoS account
    balances[delegator_address] -= amount
    balances[pos] += amount
    update_total_deltas(validator_address, pipeline_length, amount)
    update_voting_power(validator_address, pipeline_length)
    update_total_voting_power(pipeline_length)
    update_validator_sets(validator_address, pipeline_length)
}
```

The `unbond` function unbonds `total_amount` tokens to belonging to a delegator `delegator_address` from a validator `validator_address`. The function takes a fourth argument `dest_validator_address`. If the function is called by the redelegation transaction, then the unbonding is triggered due to a redelegation and `dest_validator_address` determines the address of the destination validator. It is set to `""` otherwise. The function takes the following steps:

1. It first checks that `validator_address` is a validator and it is not frozen.
2. Then it computes the total amount of tokens that the delegator has currently bonded to the validator.
3. If the total amount is less than `total_amount`, the function returns.
4. If the total amount is at least `total_amount`, it computes how much of `total_amount` is effectively unbonded after slashing and stores it in `amount_after_slashing`. This computation is done by iterating over the bonds in `delbonds` while there are tokens to unbond. For each bond (a pair of bond start epoch `start` and amount `amount`), it computes how much should be unbonded after slashing (`amount_unbonded_after_slashing`) as follows:
   - It checks whether some of the tokens in the bond were redelegated and if so computes the total amount of redelegated tokens (`redelegated_amount`).
   - It computes how much has to be unbonded by taking the minimum between the remainder and the bond amount (`amount_unbonded`).
   - The protocol prioritizes unbonding first redelegated tokens. Thus, it checks that if the amount to be unbonded is greater than the amount of redelegated tokens
   - If the amount to be unbonded is greater, then adds `amount_unbonded - redelegated_amount` to `amount_unbonded_after_slashing` after applying any slash that ocurred while the bonded tokens were contributing to the misbehaving validator stake (`start <= slash.epoch`). At this point, the function also updates `total_unbonded`.
   - Then if some of the tokens in the bond were redelegated, the function proceeds to compute for each of the redelegated bond how much should be unbonded while there remains tokens to be unbonded. For each of the redelegated bonds, the function applies to set of slashes. First, any slash that occurred while the bonded tokens were contributing to the validator stake (`start <= slash.epoch`). Second, any slash of the source validator of the redelegation such that (i) the redelegation slashing window includes the misbehaving epoch, and (ii) the redelegation bond was contributing to the source validator when this misbehaved.
   - While iterating over redelegation bonds, the function updates three key variables: `redelegated_bonds`, `total_unbonded_redelegated` and `redelegated_unbonds` if the `unbond` function is not called by a redelegation transaction, i.e., `dest_validator_address=""`, in which case we do not need to record unbonds.
   - Finally, the function updates the bond by subtracting `amount_unbonded`, and registers an unbond if the `unbond` function was not triggered by a redelegation transaction or registers the new bond in `redelegated_bonds` otherwise.
5. It finally updates the validator's `total_deltas` with `amount_after_slashing`, voting power, total voting power and validator sets.

```go
func unbond(validator_address, delegator_address, total_amount, dest_validator_address)
{
  // disallow unbonding if the validator is frozen
  var frozen = read_epoched_field(validators[validator_address].frozen, cur_epoch, false)
  if (is_validator(validator_address, cur_epoch+pipeline_length) && frozen == false) then
    // compute total bonds from delegator to validator
    var delbonds = {<start, amount> | amount = bonds[delegator_address][validator_address].deltas[start] > 0 && start <= cur_epoch + unbonding_length}
    // check if there are enough bonds
    // this serves to check that there are bonds (in the docs) and that these are greater than the amount we are trying to unbond
    if (sum{amount | <start, amount> in delbonds} >= total_amount) then
      var remain = total_amount
      var amount_after_slashing = 0
      // iterate over bonds and create unbonds
      forall (<start, amount> in delbonds while remain > 0) do
        // Retrieve the bond's associated redelegation records (if any)
        var number_redelegations = redelegated_bonds[delegator_address][validator_address][start].size()
        // Take the minimum between the remainder and the unbond. This is equal to amount if remain > amount and remain otherwise 
        var amount_unbonded = min{amount, remain}
        var redelegated_amount = 0
        if number_redelegations > 0 then
          forall (let [validator, redelegation_bonds] of redelegated_bonds[delegator_address][validator_address][start]) do
            redelegated_amount += sum(redelegation_bonds.values())

        var amount_unbonded_after_slashing = 0
        // set of slashes that happened while the bond was contributing to the validator's stake
        var set_slashes = {slash | slash in slashes[validator_address] && start <= slash.epoch }

        // compute amount after slashing if some of the tokens do not come from redelegation
        if redelegated_amount < amount_unbonded then 
          amount_unbonded_after_slashing = compute_amount_after_slashing(set_slashes, amount_unbonded - redelegated_amount)
          validators[validator_address].total_unbonded[cur_epoch+pipeline_length][start] += amount_unbonded - redelegated_amount

        // compute amount after slashing the tokens coming from redelegation
        remain -= amount_unbonded - redelegated_amount
        // initialize unbond_redelegation_record to bottom
        if number_redelegations > 0 then
          forall (let [redelegation_validator, redelegation_bonds] of redelegated_bonds[delegator_address][validator_address][start]) do
            forall (let [red_bond_start, red_bond_amount] of redelegation_bonds while remain > 0) do
              var final_set_slashes = set_slashes \union {slash | slash in slashes[redelegation_validator] &&
                                                                  //start - pipeline_length is the epoch when the redelegation was issued
                                                                  //any slashed processed at an epoch < slash - pipeline_length - unbonding_length has been applied already
                                                                  start - pipeline_length - unbonding_length <= slash.epoch < start &&
                                                                  red_bond_start <= slash.epoch}
              amount_unbonded_after_slashing += compute_amount_after_slashing(final_set_slashes, min{red_bond_amount, remain})
              redelegated_bonds[delegator_address][validator_address][start][redelegation_validator][red_bond_start] -= min{red_bond_amount, remain}
              // if it is not a redelegation, then create a redelegated unbond
              if dest_validator_address != "" then
                var unbond_end = cur_epoch+pipeline_length+unbonding_length
                redelegated_unbonds[delegator_address][validator_address][(start, unbond_end)][redelegation_validator][red_bond_start] += min{red_bond_amount, remain}
                                    
              validators[validator_address].total_unbonded_redelegated[cur_epoch+pipeline_length][redelegation_validator][(start, red_bond_start)] += min{red_bond_amount, remain}

              remain -= min{red_bond_amount, remain}

        amount_after_slashing += amount_unbonded_after_slashing

        // update bond
        bonds[delegator_address][validator_address].deltas[start] = amount - amount_unbonded

        // if it is a redelegation, then create redelegated bonds at the dest_validator_address
        // and record the outgoing redelegation at the source validator
        // if it is not a redelegation, then create unbonds at validator_address and manage redelegated unbonds
        if dest_validator_address != "" then
          redelegated_bonds[delegator_address][dest_validator_address][cur_epoch+pipeline_length][src_validator_address][bond_start] += amount
          validators[validator_address].outgoing_redelegations[dest_validator_address][(start, cur_epoch)] += amount_unbonded_after_slashing
        else
          unbonds[delegator_address][validator_address].deltas[start, cur_epoch+pipeline_length+unbonding_length] += amount_unbonded

      update_total_deltas(validator_address, pipeline_length, -1*amount_after_slashing)
      update_voting_power(validator_address, pipeline_length)
      update_total_voting_power(pipeline_length)
      update_validator_sets(validator_address, pipeline_length)
      return amount_after_slashing
}
```

The `withdraw` function withdraws all tokens unbonded by a delegator `delegator_address` from a validator `validator_address` whose unbonding period has expired. It takes the following steps:

1. It first computes the total amount of tokens that the delegator has unbonded from the validator whose unbonding period has expired.
2. Then it iterates over the unbonds in `delunbonds`. For each unbond (a triple of bond start epoch `start`, unbond end epoch 'end', and amount `amount`), it computes how much should be withdrawn after slashing (`amount_after_slashing`) as follows:
   - It checks whether some of the tokens in the unbond were redelegated and if so computes the total amount of redelegated tokens (`redelegated_amount`).
   - It computes the set of slashes that ocurred while the tokens were contributing to the validator's stake.
   - Then it computes the how much is left after slashing the non-redelegated chunk of tokens (`amount - redelegated_amount`) after applying the set of slashes previously computed and adds it to `amount_after_slashing`.
   - If some of the tokens were redelegated, then the function iterates over all redelegations. For each redelegation, it iterates over the redelegation bonds and computes for each redelegation bond how much is left after slashing. The set of slashes applied includes the set of slashes computed before and any slash of the source validator of the redelegation such that (i) the redelegation slashing window includes the misbehaving epoch, and (ii) the redelegation bond was contributing to the source validator when this misbehaved. Once this is computed, the amount is added to `amount_after_slashing`.
   - It sets the associated `redelegated_unbonds` entry to 0 to register that those redelegated tokens have been withdrawn.
3. It transfers `amount_after_slashing` from the PoS account to the delegator's account.
4. It finally updates `unbonds` to register that the unbonds have been withdrawn.

```go
/* COMMENT: Something to check for correctness https://github.com/informalsystems/partnership-heliax/pull/16#discussion_r924319213 */
func withdraw(validator_address, delegator_address)
{
  var delunbonds = {<start,end,amount> | amount = unbonds[delegator_address][validator_address].deltas[(start, end)] > 0 && end <= cur_epoch }
  // subtract any pending slash before withdrawing
  forall (<start,end,amount> in delunbonds) do
    // retrieve redelegation record
    var number_redelegations = redelegated_unbonds[delegator_address][validator_address][(start, end)].size()
    var redelegated_amount = 0
    if number_redelegations > 0 then
      forall (let [validator, redelegation_bonds] of redelegated_unbonds[delegator_address][validator_address][(start, end)]) do
        redelegated_amount += sum(redelegation_bonds.values())
    // set of slashes that happened while the bond was contributing to the validator's stake
    var set_slashes = {s | s in slashes[validator_address] && start <= s.epoch && s.epoch < end - unbonding_length }
    var amount_after_slashing = compute_amount_after_slashing(set_slashes, amount - redelegated_amount)
    if number_redelegations > 0 then
      forall (let [redelegation_validator, redelegation_unbonds] of redelegated_unbonds[delegator_address][validator_address][(start, end)]) do
        forall (let [red_bond_start, red_bond_amount] of redelegation_unbonds s.t. red_bond_amount > 0) do
          // add slashes if the tokens were redelegated
          var final_set_slashes = set_slashes \union {slash | slash in slashes[redelegation_validator] &&
                                                              //start - pipeline_length is the epoch when the redelegation was issued
                                                              //any slashed processed at an epoch < slash - pipeline_length - unbonding_length
                                                              //has been applied already
                                                              start - pipeline_length - unbonding_length <= slash.epoch < start &&
                                                              red_bond_start <= slash.epoch}
          amount_after_slashing += compute_amount_after_slashing(final_set_slashes, red_bond_amount)
        // manage redelegation records
        redelegated_unbonds[delegator_address][validator_address][(start, end)][redelegation_validator][red_bond_start] = 0

    balance[delegator_address] += amount_after_slashing
    balance[pos] -= amount_after_slashing
    // remove unbond
    unbonds[delegator_address][validator_address].deltas[(start,end)] = 0

}
```
The function `compute_amount_after_slashing` applies a set of slashes to a initial stake `amount`. It applies them in slash epoch order as follows:

1. For each `slash`, the function computes the slashable amount: how much of the stake should be slashed due to the infraction. To do so, it first computes how much it is left from initial stake after all slashes ordered before have been applied. This is computed by subtracting from the initial stake the slashable amount of any infraction that was processed before the current infraction (`slash.epoch`).
2. The returned amount is the initial stake minus the sum of all slashable amounts.

```go
func compute_amount_after_slashing(set_slashes, amount) {
  var computed_amounts = {}
    var updated_amount = amount
    forall (slash in set_slashes in slash.epoch order) do
      // Update amount with slashes that happened more than `unbonding_length` before this slash
      forall (slashed_amount in computed_amounts s.t. slashed_amount.epoch + unbonding_length < slash.epoch) do
        updated_amount -= slashed_amount.amount
        computed_amounts = computed_amounts \ {slashed_amount}
      computed_amounts.add(SlashedAmount{epoch: slash.epoch, amount: updated_amount*slash.rate})

    return updated_amount - sum({computed_amount.amount | computed_amount in computed_amounts})
}
```

The function `new_evidence` is called when a new infraction is submitted. The function takes the following steps:

1. It first creates a slash record base on the submitted evidence and then schedules the slash to be processed at the end of the epoch resulting from adding `unbonding_length` to the misbehaving epoch.
2. It jails the validator, removes it from the validator sets, and updates the total voting power.
3. Finally, the function freezes the validator to prevent unbonds from it until the slash is processed.

```go
/* COMMENT
  the model assumes that the evidence cannot be too much in the past
  CHECK: can some evidences be lost on translation? epochs are based in time and heights.
  ALTERNATIVE: it may be simple to filter them out at the PoS module rather than in Tendermint.
*/
/* COMMENT
  what about if the evidence is for the very last epoch? Problem with ranges: +1 may not exist.
*/
func new_evidence(evidence)
{
  // create slash
  var total_staked = read_epoched_field(validators[evidence.validator].total_deltas, evidence.epoch, 0)
  var slash = Slash{epoch: evidence.epoch, validator: evidence.validator, rate: 0, stake_fraction: compute_stake_fraction(evidence.type, total_staked)}
  // enqueue slash (Step 1.1 of cubic slashing)
  append(enqueued_slashes[evidence.epoch + unbonding_length], slash)
  // jail validator (Step 1.2 of cubic slashing)
  validators[validator_address].jail_record = JailRecord{is_jailed: true, epoch: cur_epoch+1}
  remove_validator_from_sets(validator_address, 1)
  update_total_voting_power(1)
  // freeze validator to prevent delegators from altering their delegations (Step 1.3 of cubic slashing)
  freeze_validator(validator_address)
}
```

```go
func compute_stake_fraction(infraction, voting_power){
  switch infraction
    case duplicate_vote: return duplicate_vote_rate * voting_power
    case light_client_attack: return light_client_attack_rate * voting_power
    default: panic()
}
```

The function `end_of_epoch` is called at the end of every epoch. It takes the following steps:

1. It first computes the slash rate for any slash that has to be processed at the end of the current epoch.
2. It then iterates over the enqueued slashes. For each slash:
   - It appends the slash to the misbehaving validator's set of slashes.
   - It uses the `slash_validator` function to slash the misbehaving validator.
   - It iterates over all validators to which there is an ongoing redelegation from the misbehaving validator. For each destination validator, the function computes the total amount of tokens that are slashable: those belonging to a redelegation for which (i) the redelegation's slashing window includes the misbehaving epoch, and (ii) that were bonded to the the source validator before the misbehaving epoch. If there are tokens to be slashed (`total_amount > 0`), then the function uses `slash_validator` to slash the destination validator.
3. Finally, it advances the epoch by increasing `cur_epoch`.

```go
end_of_epoch()
{
  // iterate over all slashes for infractions within (-1,+1) epochs range (Step 2.1 of cubic slashing)
  var set_slashes = {s | s in enqueued_slashes[epoch] && cur_epoch-1 <= epoch <= cur_epoch+1}
  // calculate the slash rate (Step 2.2 of cubic slashing)
  var rate = compute_final_rate(set_slashes)

  var set_validators = {val | val = slash.validator && slash in enqueued_slashes[cur_epoch]}
  forall (validator_address in set_validators) do
    forall (slash in {s | s in enqueued_slashes[cur_epoch] && s.validator == validator_address}) do
      // set the slash on the now "finalized" slash amount in storage (Step 2.3 of cubic slashing)
      slash.rate = rate
      append(slashes[validator_address], slash)
      var total_staked = read_epoched_field(validators[validator_address].total_deltas, slash.epoch, 0)
      
      slash_validator(validator_address, slash, total_staked, "")

      forall (dest_validators in validators[validator_address].outgoing_redelegations.keys()) do
        var total_amount = 0
        var redelegations = validators[validator_address].outgoing_redelegations[dest_validators].entries()
        // selects all outgoing redelegations issued within the redelegation window defined by slash.epoch
        // and whose tokens were contributing the source validator when this misbehaved 
        forall (let [(bond_start, redelegation_start), amount] of redelegations s.t. amount > 0 &&
                                                                      redelegation_start - unbonding_length <= slash.epoch < redelegation_start + pipeline_length &&
                                                                      bond_start <= slash.epoch) do
          total_amount += amount
        if total_amount > 0 then 
          slash_validator(dest_validators, slash, total_amount, validator_address)

    // unfreeze the validator (Step 2.5 of cubic slashing)
    // this step is done in advance when the evidence is found
    // by setting validators[validator_address].frozen[cur_epoch+unbonding_length+1]=false
    // note that this index could have been overwritten if more evidence for the same validator
    // where found since then
  cur_epoch = cur_epoch + 1
}
```

The `slash_validator` function is called by the `end_of_epoch` function for a given validator `validator_address`, slash `slash` and amount `staked_amount`, which is the stake that must be slashed. The function also includes a fourth parameter `src_validator` that it is only assigned (`!=""`) if the validator is slashed because the source validator of a redelegation misbehaved. In that case `src_validator` indicates the address of the misbehaving validator. The function proceeds as follows:

1. It first computes `total_unbonded` up to the cur_epoch: the total amount of tokens from `staked_amount` that have been unbonded by `cur_epoch`. For each epoch from the misbehaving epoch (`slash.epoch`) up to `cur_epoch`, the function uses `compute_total_unbonded` or `compute_total_unbonded_redelegated` to compute the total amount of tokens unbonded in that epoch depending on whether `validator_address` is slashed due to a redelegation or not.
2. Then for each `epoch` from `cur_epoch` to `cur_epoch+pipeline_length`, the function updates the validator's `total_deltas` and voting power by taking the following steps:
     - Add the amount of tokens from `staked_amount` that have been unbonded at `epoch` to `total_unbonded`.
     - Compute how much we should slash in `this_slash`.
     - Since `update_total_deltas` updates the validator's `total_deltas` from given epoch `cur_epoch+offset` up to `cur_epoch+unbonding_length`, we may over slash in cases when tokens are unbonded at higher epochs. For instance, assume that we slash `X` tokens at epoch `e`. Then, we take `X` tokens from `total_deltas` at `e+1` when calling `update_total_deltas`. If the validator unbonded `Y <= X` of those `X` tokens at `e+1`, we need to add `Y` tokens to `total_deltas` at `e+1` when iterating over `e+1`.  `last_slash - this_slash` compensates for that.
     - Finally, the function updates the validator's `total_deltas` and voting power by calling `update_total_deltas` and `update_voting_power`.

```go
func slash_validator(validator_address, slash, staked_amount, src_validator)
{
  var total_unbonded = 0
  // find the total unbonded from the slash epoch up to the current epoch first
  // a..b notation determines an integer range: all integers between a and b inclusive
  forall (epoch in slash.epoch+1..cur_epoch) do
    if (src_validator == "") then
      total_unbonded += compute_total_unbonded(validator_address, slash, epoch)
    else
      total_unbonded += compute_total_unbonded_redelegated(validator_address, src_validator, slash, epoch)

  var last_slash = 0
  // up to pipeline_length because there cannot be any unbond in a greater epoch (cur_epoch+pipeline_length is the upper bound)
  forall (offset in 1..pipeline_length) do
    if (src_validator == "") then
      total_unbonded += compute_total_unbonded(validator_address, slash, cur_epoch+offset)
    else
      total_unbonded += compute_total_unbonded_redelegated(validator_address, src_validator, slash, cur_epoch+offset)

    var this_slash = (staked_amount - total_unbonded) * slash.rate
    var diff_slashed_amount = last_slash - this_slash
    last_slash = this_slash
    update_total_deltas(validator_address, offset, diff_slashed_amount)
    update_voting_power(validator_address, offset)
}
```

The `compute_total_unbonded` function computes `total_unbonded` for a given epoch `epoch`, slash `slash` and validator `validator_address`.
The function computes `total_unbonded` in two steps: first considers exclusively non-redelegated tokens, i.e., those delegated directly to the validator, and then tokens that were redelegated. In more detail:

1. It iterates over the non-redelegated tokens unbonded in `epoch` (`validators[validator_address].total_unbonded[epoch]`) that were contributing to the validator's stake when this misbehaved (at `slash.epoch`).
   - At each iteration, it adds the amount unbonded to `total_unbonded` after applying any slash that was processed before `slash.epoch`.
2. The second step consists in adding to `total_unbonded` any amount of tokens, which belong to a redelegation, that were unbonded at `epoch`.
   - This only includes redelegations that ended before the misbehaving epoch, i.e., `red_start <= slash.epoch`. Otherwise, those tokens would not have contributed to the misbehaving validator's stake when this misbehaved, so we would not need to add them to `total_unbonded`.
   - For each of those redelegations, we first compute the set of slashes for any infractions committed by the misbehaving validator that was processed before `slash.epoch`.
   - Finally, for each of the bonds belonging to a redelegation, the function adds to the above set of slashes any slash for an infraction committed by the redelegation's source validator that (i) was processed before `slash.epoch`, (ii) the redelegation slashing window includes the misbehaving epoch, and (iii) the bonds were contributing to the source validator when this misbehaved. The function then adds the amount to `total_unbonded` after slashing it with the computed set of slashes.

```go
func compute_total_unbonded(validator_address, slash, epoch){
  var total_unbonded = 0
  // select the epochs (start_epochs) at which bonds contributing to the misbehaving validator
  // were unbonded at epoch
  var start_epochs = { start | start in validators[validator_address].total_unbonded[epoch].keys() &&
                               validators[validator_address].total_unbonded[epoch][start] > 0 &&
                               start <= slash.epoch }
  // add those tokens to total_unbonded after slashing
  forall (start in start_epochs)
    // the set of slashes only includes those that were processed before slash.epoch: s.epoch + unbonding_length < slash.epoch
    var set_slashes = {s | s in slashes[validator_address] &&
                       start <= s.epoch &&
                       s.epoch + unbonding_length < slash.epoch }
    total_unbonded += compute_amount_after_slashing(set_slashes, validators[validator_address].total_unbonded[epoch][start])

  forall (let [(red_start, redelegation_validator), redelegation_bonds] of validators[validator_address].total_unbonded_redelegated[epoch] s.t. red_start <= slash.epoch) do
    var set_slashes = {s | s in slashes[validator_address] &&
                       red_start <= s.epoch &&
                       s.epoch + unbonding_length < slash.epoch }
    // iterate over all redelegated tokens that were unbonded at epoch and that were contributing to the misbehaving validators stake at slash.epoch
    forall (let [red_bond_start, red_bond_amount] of redelegation_bonds s.t. red_bond_amount > 0) do
      // apply the set of slashes including those that were processed before slash.epoch: s.epoch + unbonding_length < slash.epoch and that
      // were not processed when the redelegation ocurred: red_start - pipeline_length - unbonding_length <= s.epoch < red_start
      var final_set_slashes = set_slashes \union {s | s in slashes[redelegation_validator] &&
                                                    red_start - pipeline_length - unbonding_length <= s.epoch < red_start &&
                                                    s.epoch + unbonding_length < slash.epoch &&
                                                    red_bond_start < s.epoch}
      total_unbonded += compute_amount_after_slashing(final_set_slashes, red_bond_amount)
  return total_unbonded
}
```

The `compute_total_unbonded_redelegated` function computes `total_unbonded` for a given epoch `epoch`, slash `slash`, validator `validator_address`, and source validator `src_validator` (the misbehaving validator).
The function computes `total_unbonded` in as follows:

1. It first selects from of all redelegated tokens unbonded at `epoch` those that were redelegated (i) by `src_validator`, and (ii) the redelegation slashing window includes the misbehaving epoch (`slash.epoch`).
2. Then it iterates over all of the selected redelegations. For each redelegation, it iterates over all bonds (`> 0`) that were contributing to the misbehaving validator `src_validator` when it misbehaved (at `slash.epoch`).
3. For each of the iterated bonds, the function applies any slash that (i) falls within the associated redelegation slashing window and that was processed before `slash.epoch`. Note that it is unclear at the moment if this is possible given the size of the redelegation slashing window and the constraint that it has to be processed before `slash.epoch`.

```go
func compute_total_unbonded_redelegated(validator_address, src_validator, slash, epoch){
  var total_unbonded = 0
  // only consider unbonded tokens that were redelegated by the misbehaving validator
  var redelegations = validators[validator_address].total_unbonded_redelegated[epoch].entries()
  forall (let [(red_start, redelegation_validator), redelegation_bonds] of redelegations s.t. redelegation_validator == src_validator &&
                                                                                              red_start - unbonding_length - pipeline_length <= slash.epoch < red_start) do
    forall (let [red_bond_start, red_bond_amount] of redelegation_bonds s.t. red_bond_start <= slash.epoch && red_bond_amount > 0) do
      // apply any slash to red_bond_amount processed before slash.epoch and that was not already applied when the redelegation was created
      // TODO: check that this set is not always empty
      var set_slashes = {s | s in slashes[validator_address] &&
                             red_start - unbonding_length - pipeline_length <= s.epoch &&
                             s.epoch + unbonding_length < slash.epoch}

      total_unbonded += compute_amount_after_slashing(set_slashes, red_bond_amount)
  return total_unbonded
}
```

```go
// Cubic slashing function
compute_final_rate(slashes)
{
  var voting_power_fraction = 0
  forall (slash in slashes) do
    voting_power_fraction += slash.voting_power_fraction
  return max{0.01, min{1, voting_power_fraction^2 * 9}}
}
```

### Validator's functions

```go
add_validator_to_sets(validator_address, offset)
{
  var epochs = {epoch | cur_epoch+offset <= epoch <= cur_epoch+unbonding_length && (epoch > cur_epoch+offset => validator_sets[epoch] != ⊥)}
  forall (epoch in epochs) do
    var sets = read_epoched_field(validator_sets, epoch, ⊥)
    var min_active = first(sets.active)
    var voting_power = read_epoched_field(validators[validator_address].voting_power, epoch, 0)
    if (voting_power > min_active.voting_power) then
      sets = remove(sets.active, min_active.validator)
      sets = add(sets.active, WeightedValidator{validator: validator_address, voting_power: voting_power})
    else
      sets = add(sets.inactive, WeightedValidator{validator: validator_address, voting_power: voting_power})
    validator_sets[epoch] = sets
}
```

```go
remove_validator_from_sets(validator_address, offset)
{
  var epochs = {epoch | cur_epoch+offset <= epoch <= cur_epoch+unbonding_length && (epoch > cur_epoch+offset => validator_sets[epoch] != ⊥)}
  forall (epoch in epochs) do
    var sets = read_epoched_field(validator_sets, epoch, ⊥)
    if (validator_address in sets.active) then
      var max_inactive = last(sets.inactive)
      remove(sets.active, validator_address)
      remove(sets.inactive, max_inactive.validator)
      add(sets.active, max_inactive)
    else if (validator_address in sets.inactive) then
      remove(validator_sets[epoch].inactive, validator_address)
    validator_sets[epoch] = sets
}
```

```go
update_total_deltas(validator_address, offset, amount)
{
  var epochs = {epoch | cur_epoch+offset <= epoch <= cur_epoch+unbonding_length &&
                        (epoch > cur_epoch+offset => validators[validator_address].total_deltas[epoch] != ⊥)}
  forall (epoch in epochs) do
    var total = read_epoched_field(validators[validator_address].total_deltas, epoch, 0)
    validators[validator_address].total_deltas[epoch] = total + amount
}
```

```go
func update_voting_power(validator_address, offset)
{
  var epochs = {epoch | cur_epoch+offset <= epoch <= cur_epoch+unbonding_length &&
                        (epoch > cur_epoch+offset => validators[validator_address].voting_power[epoch] != ⊥)}
  forall (epoch in epochs) do
    // compute bonds from total_deltas 
    var bonds = read_epoched_field(validators[validator_address].total_deltas, epoch, 0)
    // compute the new voting power
    var power_after = votes_per_token*bonds
    // update voting power and return it
    validators[validator_address].voting_power[epoch] = power_after
    return power_after
}
```

```go
func update_total_voting_power(offset)
{
  var epochs = {epoch | cur_epoch+offset <= epoch <= cur_epoch+unbonding_length &&
                        (epoch > cur_epoch+offset => validator_sets[epoch] != ⊥)}
  forall (epoch in epochs) do
    var total = 0
    var sets = read_epoched_field(validator_sets, epoch, ⊥)
    forall (validator in sets.active \union sets.inactive) do
      total += validator.voting_power
    total_voting_power[epoch] = total
}
```

```go
func update_validator_sets(validator_address, offset)
{
  var epochs = {epoch | cur_epoch+offset <= epoch <= cur_epoch+unbonding_length &&
                        (epoch > cur_epoch+offset => validator_sets[epoch] != ⊥) &&
                        read_epoched_field(validators[validator_address].state, epoch, ⊥) == candidate}
  forall (epoch in epochs) do
    var sets = read_epoched_field(validator_sets, epoch, ⊥)
    var min_active = first(sets.active)
    var max_inactive = last(sets.inactive)
    power_before = get(sets.active U sets.inactive, validator_address).voting_power
    power_after = read_epoched_field(validators[validator_address].voting_power, epoch, 0)
    if (power_before >= max_inactive.voting_power) then
      // if active but it loses power below the max_inactive then move validator to inactive
      // and promote max_inactive
      if (power_after < max_inactive.voting_power) then
        remove(sets.active, validator_address)
        add(sets.active, max_inactive)
        remove(sets.inactive, max_inactive.validator)
        add(sets.inactive, WeightedValidator{validator: validator_address, voting_power: power_after})
      // if active and its change in power does not degrade it to inactive, then update its voting power
      else
        remove(sets.active, validator_address)
        add(sets.active, WeightedValidator{validator: validator_address, voting_power: power_after})
    else
      // if inactive and gains power above the min_active, then insert into active and
      // degrade min_active 
      if (power_after > min_active.voting_power) then
        remove(sets.inactive, validator_address)
        add(sets.inactive, min_active)
        remove(sets.active, min_active.validator)
        add(sets.active, WeightedValidator{validator: validator_address, voting_power: power_after})
      // if inactive and its change in power does not promote it to active, then update its voting power
      else
        remove(sets.inactive, validator_address)
        add(sets.inactive, WeightedValidator{validator: validator_address, voting_power: power_after})
    validator_sets[epoch] = sets
}   
```

```go
freeze_validator(validator_address)
{
  var epochs = {epoch | cur_epoch <= epoch <= cur_epoch+unbonding_length &&
                        (epoch > cur_epoch => validators[validator_address].frozen[epoch] != ⊥)}
  forall (epoch in epochs) do
    var total = read_epoched_field(validators[validator_address].frozen, epoch, false)
    validators[validator_address].frozen[epoch] = true
  // schedule when to unfreeze the validator: after processing the enqueued slash
  validators[validator_address].frozen[cur_epoch+unbonding_length+1] = false
}
```

```go
func is_validator(validator_address, epoch){
    return read_epoched_field(validators[validator_address].state, epoch, ⊥) != ⊥
}
```

```go
is_jailed(validator_address)
{
  return validators[validator_address].jail_record.is_jailed
}
```

### Auxiliary functions

```go
func read_epoched_field(field, upper_epoch, bottom){
  var assigned_epochs = {epoch | field[epoch] != ⊥ && epoch <= upper_epoch}
  if (assigned_epochs is empty) then return bottom
  else return field[max{assigned_epochs}]
}
```