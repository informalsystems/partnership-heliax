## Assumptions/simplifications

- There is a single token type
- There is an initial set of active and inactive validators
- There are always enough non-jalied, candidate validators to fulfill the active set of validators at any given epoch

## Data types

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
  amount uint
  start Epoch
}

type SlashedAmount struct {
  epoch Epoch
  amount uint
}

type Validator struct {
  consensus_key map<Epoch, Key>
  state map<Epoch, {inactive, candidate}>
  total_deltas map<Epoch, amount:int>
  unbond_records map<Epoch, map<Epoch, amount:int>> // outer epoch for the unbond start (when the tokens stopped contributing to the validator's stake), inner for the underlying bond start
  voting_power map<Epoch, VotingPower>
  reward_address Addr
  jail_record JailRecord
  frozen map<Epoch, bool>
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
  type string
  voting_power VotingPower // the voting power used to commit the infraction
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

## Constants

```go
pipeline_length uint
unbonding_length uint
cubic_slash_window_width uint
min_sentence uint
votes_per_token uint
duplicate_vote_rate float
ligth_client_attack_rate float
```

## Variables

```go
cur_epoch ← 0 in Epoch //current epoch

validators[] in Addr → Validator //map from address to validator
balances[] in Addr → int //map from address to integer
bonds[][] in (Addr X Addr) → Bond //map from address to map from address to bond
unbonds[][] in (Addr X Addr) → Unbond  //map from (address, address) to unbond
slashes[] in Addr → 2^Slash //map from address to list of slashes
enqueued_slashes[] in Epoch → 2^Slash //map from epoch to list of slashes

validator_sets[] in Epoch → ValidatorSet //map from epoch to validator_set
total_voting_power[] in Epoch to VotingPower //map from epoch to voting_power
```

## Validator transactions

```go
tx_become_validator(validator_address, consensus_key)
{
  // Check that become_validator has not been called before for validator_address
  var state = read_epoched_field(validators[validator_address].state, cur_epoch+pipeline_length, ⊥)
  if (state == ⊥) then
    // Set status to candidate and consensus key at n + pipeline_length
    validators[validator_address].consensus_key[cur_epoch+pipeline_length] = consensus_key
    validators[validator_address].state[cur_epoch+pipeline_length] = candidate
    validators[validator_address].jail_record = JailRecord{is_jailed: false, epoch: ⊥}
    validators[validator_address].frozen[cur_epoch] = false
    // Add validator to the inactive set
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
    //set status to inactive at n + pipeline_length
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
    //set status to candidate at n + pipeline_length
    validators[validator_address].state[cur_epoch+pipeline_length] = candidate
    //add validator to the inactive set
    add_validator_to_sets(validator_address, pipeline_length)
    update_total_voting_power(pipeline_length)
}
```

```go
tx_unjail(validator_address)
{
  // Check validator is jailed and can be unjailed
  var epochs_jailed = cur_epoch + pipeline_length - validators[validator_address].jail_record.epoch
  if (is_jailed(validator_address) && (epochs_jailed > min_sentence)) then
    validators[validator_address].jail_record = JailRecord{is_jailed: false, epoch: ⊥}
    var state = read_epoched_field(validators[validator_address].state, cur_epoch+pipeline_length, ⊥)
    //add the validator to the validator sets if it is a candidate by pipeline_length
    if (state == candidate) then
      add_validator_to_sets(validator_address, pipeline_length)
      update_total_voting_power(pipeline_length)
}
```

```go
tx_self_bond(validator_address, amount)
{
  bond(validator_address, validator_address, amount, pipeline_length)
}
```

```go
tx_unbond(validator_address, amount)
{
  unbond(validator_address, validator_address, amount)
}
```

```go
tx_withdraw_unbonds_validator(validator_address)
{
  withdraw(validator_address, validator_address)
}
```

```go
tx_change_consensus_key(validator_address, consensus_key)
{
  //set consensus key at n + pipeline_length
  validators[validator_address].consensus_key[cur_epoch+pipeline_length] = consensus_key
}
```
## Delegator transactions

```go
tx_delegate(validator_address, delegator_address, amount)
{
  bond(validator_address, delegator_address, amount)
}
```

```go
tx_undelegate(validator_address, delegator_address, amount)
{
  unbond(validator_address, delegator_address, amount)
}
```

<!-- 
```go
tx_redelegate(src_validator_address, dest_validator_address, delegator_address, amount)
{
  unbond(src_validator_address, delegator_address, amount)
  bond(dst_validator_address, delegator_address, amount, unbonding_length)
}
```
-->

```go
tx_withdraw_unbonds_delegator(delegator_address)
{
  forall (validator_address in validators) do
    withdraw(validator_address, delegator_address)
}
```

## PoS functions


```go
//This function is called by transactions tx_self_bond, tx_delegate and tx_redelegate
/* COMMENT
//When adding redelegate, the bond function may be parametrized with offset_length.
//A priori, the only possible values for offset_length are pipeline_length and unbonding_length.
//This would mean that epoched variables may be update at different offsets which would require special handling.
*/
// Bond tokens to a validator address. This can be done even if a validator is frozen or jailed.
func bond(validator_address, delegator_address, amount)
{
  if is_validator(validator_address, cur_epoch+pipeline_length) then
    // Add bond amount to deltas at n + pipeline_length
    bonds[delegator_address][validator_address].deltas[cur_epoch+pipeline_length] += amount
    // Debit amount from delegator account and credit it to the PoS account
    balances[delegator_address] -= amount
    balances[pos] += amount
    // Update voting powers and validator set
    update_total_deltas(validator_address, pipeline_length, amount)
    update_voting_power(validator_address, pipeline_length)
    update_total_voting_power(pipeline_length)
    update_validator_sets(validator_address, pipeline_length)
}
```

```go
/* COMMENT
  two issues:
  - https://github.com/informalsystems/partnership-heliax/issues/6
    delbonds and epoch_counter are considered from the unbonding_length offset.
    This could lead to scenarios in which one starts unbonding before a bond is materialized.
    Furthermore, there cannot be positive bonds beyond cur_epoch + pipeline_length, so it does not
    make sense for delbonds.
    conclusion: intended
  - https://github.com/informalsystems/partnership-heliax/issues/7
    there is a problem with unbonding, slashing and total_deltas becoming negative
    conclusion: it is an actual issue, unresolved
*/
// This function is called by transactions tx_unbond, tx_undelegate and tx_redelegate.
// Unbonds tokens from one or more existing bonds. The validator deltas are updated and include the effects of slashing. The amount deducted from the stake may be less than the `total_amount` unbonded because an already-processed slash may have effectively slashed the validator's stake already due to the bond that is currently being unbonded. Unbonding is forbidden while the target validator is frozen, but is allowed while the validator is jailed and not frozen.
func unbond(validator_address, delegator_address, total_amount)
{
  // Disallow unbonding if validator is frozen, ensure that the address is a validator at pipeline epoch
  var frozen = read_epoched_field(validators[validator_address].frozen, cur_epoch, false)
  if (is_validator(validator_address, cur_epoch+pipeline_length) && frozen == false) then
    // Compute sum of bonds from delegator to validator at the pipeline epoch (where an unbond will affect the deltas) and ensure that it is enough to accomodate the `total_amount` requested for unbonding
    var delbonds = {<start, amount> | amount = bonds[delegator_address][validator_address].deltas[start] > 0 && start <= cur_epoch + pipeline_len}
    if (sum{amount | <start, amount> in delbonds} >= total_amount) then
      var remain = total_amount // Track the remaining bond amount to unbond
      var amount_after_slashing = 0 // Track the amount to change the deltas (may be less than `total_amount` due to previous slash processing)
      var withdraw_epoch = cur_epoch + pipeline_length + unbonding_length + cubic_slash_window_width

      // Iterate over bonds and create unbond
      forall (<start, amount> in delbonds while remain > 0) do
        // Get the minimum of the remainder and the unbond, equal to amount if remain > amount and remain otherwise 
        var amount_unbonded = min{amount, remain}
        bonds[delegator_address][validator_address].deltas[start] = amount - amount_unbonded
        unbonds[delegator_address][validator_address].deltas[start, withdraw_epoch] += amount_unbonded
        // Set of slashes that happened while the bond was contributing to the validator's stake
        var set_slashes = {s | s in slashes[validator_address] && start <= s.epoch }
        amount_after_slashing += compute_amount_after_slashing(set_slashes, amount_unbonded)

        validators[validator_address].unbond_records[cur_epoch+pipeline_length][start] += amount_unbonded
        remain -= amount_unbonded
      update_total_deltas(validator_address, pipeline_length, -1*amount_after_slashing)
      update_voting_power(validator_address, pipeline_length)
      update_total_voting_power(pipeline_length)
      update_validator_sets(validator_address, pipeline_length)
}
```

```go
/* COMMENT: Something to check for correctness https://github.com/informalsystems/partnership-heliax/pull/16#discussion_r924319213 */
// This function is called by transactions tx_withdraw_unbonds_validator and tx_withdraw_unbonds_delegator.
// Withdraws all tokens from PoS for all unbonds between the delegator adn validator that are fully matured as of the current epoch. Applies slashes to the unbonds, transferring all slashed tokens to the slash pool address and all unslashed tokens back to the source delegator.
func withdraw(validator_address, delegator_address)
{
  var delunbonds = {<start,end,amount> | amount = unbonds[delegator_address][validator_address].deltas[(start, end)] > 0 && end <= cur_epoch }
  forall (<start,end,amount> in selfunbonds) do
    // Apply slashes that happened while the bond associated with the unbond was contributing to the validator's stake
    var set_slashes = {s | s in slashes[validator_address] && start <= slash.epoch && slash.epoch < end - unbonding_length - cubic_slash_window_width }
    var amount_after_slashing = compute_amount_after_slashing(set_slashes, amount)
    balance[delegator_address] += amount_after_slashing
    balance[pos] -= amount_after_slashing
    // Remove the unbond
    unbonds[delegator_address][validator_address].deltas[(start,end)] = 0
}
```

```go
compute_amount_after_slashing(set_slashes, amount) {
  var computed_amounts = {}
  var updated_amount = amount
  forall (slash in set_slashes in slash.epoch order) do
    // Update amount with slashes that happened more than `unbonding_length` before this slash
    forall (slashed_amount in computed_amounts s.t. slashed_amount.epoch + unbonding_length + cubic_slash_window_width < slash.epoch) do
      updated_amount -= slashed_amount.amount
      computed_amounts = computed_amounts \ {slashed_amount}
    computed_amounts = computed_amounts \union {SlashedAmount{epoch: slash.epoch, amount: updated_amount*slash.rate}}

  return updated_amount - sum({computed_amount.amount | computed_amount in computed_amounts})
}
```

```go
/* COMMENT
  the model assumes that the evidence cannot be too much in the past
  CHECK: can some evidences be lost on translation? epochs are based in time and heights.
  ALTERNATIVE: it may be simple to filter them out at the PoS module rather than in Tendermint.
*/
/* COMMENT
  what about if the evidence is for the very last epoch? Problem with ranges: +1 may not exist.
*/
// Record evidence of a slash for future processing. Update the validator set with the removal of the offending validator, and mark the validator as jailed and frozen
func new_evidence(validator, infraction_epoch, type)
{
  // Create slash
  var total_staked = read_epoched_field(validators[validator].total_deltas, infraction_epoch, 0)
  var slash = Slash{epoch: infraction_epoch, validator: validator, rate: 0, type: type, voting_power: total_staked}
  // Enqueue slash (Step 1.1 of cubic slashing)
  append(enqueued_slashes[infraction_epoch + unbonding_length + cubic_slash_window_width], slash)
  // Jail validator (Step 1.2 of cubic slashing)
  validators[validator].jail_record = JailRecord{is_jailed: true, epoch: cur_epoch+1}
  remove_validator_from_sets(validator, 1)
  update_total_voting_power(1)
  // Freeze validator to prevent delegators from altering their delegations (Step 1.3 of cubic slashing)
  freeze_validator(validator)
}
```

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
    //compute bonds from total_deltas 
    var bonds = read_epoched_field(validators[validator_address].total_deltas, epoch, 0)
    //compute the new voting power
    var power_after = votes_per_token*bonds
    //update voting power and return it
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
    power_before = get(sets.active U sets.active, validator_address).voting_power
    power_after = read_epoched_field(validators[validator_address].voting_power, epoch, 0)
    if (power_before >= max_inactive.voting_power) then
      //if active but it loses power below the max_inactive then move validator to inactive
      //and promote max_inactive
      if (power_after < max_inactive.voting_power) then
        remove(sets.active, validator_address)
        add(sets.active, max_inactive)
        remove(sets.inactive, max_inactive.validator)
        add(sets.inactive, WeightedValidator{validator: validator_address, voting_power: power_after})
      //if active and its change in power does not degrade it to inactive, then update its voting power
      else
        remove(sets.active, validator_address)
        add(sets.active, WeightedValidator{validator: validator_address, voting_power: power_after})
    else
      //if inactive and gains power above the min_active, then insert into active and
      //degrade min_active 
      if (power_after > min_active.voting_power) then
        remove(sets.inactive, validator_address)
        add(sets.inactive, min_active)
        remove(sets.active, min_active.validator)
        add(sets.active, WeightedValidator{validator: validator_address, voting_power: power_after})
      //if inactive and its change in power does not promote it to active, then update its voting power
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
    validators[validator_address].frozen[epoch] = true
  //schedule when to unfreeze the validator: after processing the enqueued slash
  validators[validator_address].frozen[cur_epoch+unbonding_length+1] = false
}
```

```go
func is_validator(validator_address, epoch){
    return read_epoched_field(validators[validator_address].state, epoch, ⊥) != ⊥
}
```

```go
func get_min_slash_rate(infraction){
  switch infraction
    case "duplicate_vote": return duplicate_vote_rate
    case "light_client_attack": return light_client_attack_rate
    default: panic()
}
```

```go
// Processes the enqueued slashes by calculating the cubic slashing rate and then slashing the validator's deltas (stake)
end_of_epoch()
{
  var infraction_epoch = cur_epoch - unbonding_length - cubic_slash_window_width
  // Iterate over all slashes for infractions within (-1,+1) epochs range (Step 2.1 of cubic slashing)
  var set_slashes = {s | s in enqueued_slashes[epoch] && cur_epoch-1 <= epoch <= cur_epoch+1}
  // Calculate the cubic slash rate for all slashes processed this epoch (Step 2.2 of cubic slashing)
  var cubic_rate = compute_cubic_rate(set_slashes, infraction_epoch)
  // Iterate over validators with enqueued slashes this epoch
  var set_validators = {val | val = slash.validator && slash in enqueued_slashes[cur_epoch]}
  forall (validator_address in set_validators) do
    forall (slash in {s | s in enqueued_slashes[cur_epoch] && s.validator == validator_address}) do
      // Set the slash on the now "finalized" slash amount in storage (Step 2.3 of cubic slashing)
      slash.rate = min{1.0, max{get_min_slash_rate(slash.slash_type), cubic_rate}}
      append(slashes[validator_address], slash)
      var total_staked = read_epoched_field(validators[validator_address].total_deltas, slash.epoch, 0)
      
      var total_unbonded = 0
      // Find the total unbonded from the slash epoch up to the current epoch first
      // a..b notation determines an integer range: all integers between a and b inclusive
      forall (epoch in slash.epoch+1..cur_epoch) do
        forall ((unbond_start, unbond_amount) in validators[validator_address].unbond_records[epoch] s.t. unbond_start <= slash.epoch && unbond_amount > 0)
          var set_prev_slashes = {s | s in slashes[validator_address] && unbond_start <= s.epoch && s.epoch + unbonding_length + cubic_slash_window_width < slash.epoch}
          total_unbonded += compute_amount_after_slashing(set_prev_slashes, unbond_amount)

      var last_slash = 0
      // Up to pipeline_length because there cannot be any unbond in a greater ß (cur_epoch+pipeline_length is the upper bound)
      forall (offset in 1..pipeline_length) do
        forall ((unbond_start, unbond_amount) in validators[validator_address].unbond_records[cur_epoch + offset] s.t. unbond_start <= slash.epoch && unbond_amount > 0) do
          // We only need to apply a slash s if s.epoch < unbond.end - unbonding_length
          // It is easy to see that s.epoch + unbonding_length < slash.epoch implies s.epoch < unbond.end - unbonding_length
          // 1) slash.epoch = cur_epoch - unbonding_length
          // 2) unbond.end = cur_epoch + offset + unbonding_length => cur_epoch = unbond.end - offset - unbonding_length
          // By 1) s.epoch + unbonding_length < cur_epoch - unbonding_length
          // By 2) s.epoch + unbonding_length < unbond.end - offset - 2*unbonding_length => s.epoch < unbond.end - offset - 3*unbonding_length, as required.
          var set_prev_slashes = {s | s in slashes[validator_address] && unbond_start <= s.epoch && s.epoch + unbonding_length + cubic_slash_window_width < slash.epoch}
          total_unbonded += compute_amount_after_slashing(set_prev_slashes, unbond_amount)
        var this_slash = (total_staked - total_unbonded) * slash.rate
        var diff_slashed_amount = last_slash - this_slash
        last_slash = this_slash
        update_total_deltas(validator_address, offset, diff_slashed_amount)
        update_voting_power(validator_address, offset)
    //unfreeze the validator (Step 2.5 of cubic slashing)
    //this step is done in advance when the evidence is found
    //by setting validators[validator_address].frozen[cur_epoch+unbonding_length+1]=false
    //note that this index could have been overwritten if more evidence for the same validator
    //where found since then
  cur_epoch = cur_epoch + 1
}
```

```go
// Get total stake of active (consensus-participating) validators
get_total_active_voting_power(epoch)
{
  var voting_power = 0
  forall (validator in validator_sets[epoch].active)
    voting_power += read_epoched_field(validators[validator].voting_power, epoch, 0)
  return voting_power
}
```

```go
// Cubic slashing function
compute_cubic_rate(slashes, epoch)
{
  var total_active_voting_power = get_total_active_voting_power(epoch)
  var voting_power_fraction = 0
  forall (slash in slashes) do
    voting_power_fraction += slash.voting_power / total_active_voting_power
  return 9 * voting_power_fraction^2
}
```

```go
is_jailed(validator_address)
{
  return validators[validator_address].jail_record.is_jailed
}
```

## Auxiliary functions

```go
func read_epoched_field(field, upper_epoch, bottom){
  var assigned_epochs = {epoch | field[epoch] != ⊥ && epoch <= upper_epoch}
  if (assigned_epochs is empty) then return bottom
  else return field[max{assigned_epochs}]
}
```
