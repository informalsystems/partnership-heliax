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

type Validator struct {
  consensus_key map<Epoch, Key>
  state map<Epoch, {inactive, candidate}>
  total_deltas map<Epoch, amount:int>
  voting_power map<Epoch, VotingPower>
  reward_address Addr
  jail_record JailRecord
  frozen bool
}

type Bond struct {
  validator Addr //not used
  source Addr //not used
  deltas map<Epoch, int>
}

type Unbond struct {
  validator Addr //not used
  source Addr //not used
  deltas map<(start:Epoch, end:Epoch), int>
}

type Slash struct {
  epoch Epoch
  rate float
  stake_fraction float //new in cubic slashing
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
tx_become_validator(validator_address, consensus_key, staking_reward_address)
{
  //check that become_validator has not been called before for validator_address
  var state = read_epoched_field(validators[validator_address].state, cur_epoch+pipeline_length, ⊥)
  if (state == ⊥ && validator_address != staking_reward_address) then
    validators[validator_address].reward_address = staking_reward_address
    //set status to candidate and consensus key at n + pipeline_length
    validators[validator_address].consensus_key[cur_epoch+pipeline_length] = consensus_key
    validators[validator_address].state[cur_epoch+pipeline_length] = candidate
    validators[validator_address].jail_record = JailRecord{is_jailed: false, epoch: ⊥}
    validators[validator_address].frozen = false
    //add validator to the inactive set
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
  //check validator is jailed and can be unjailed
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
func bond(validator_address, delegator_address, amount)
{
  if is_validator(validator_address, cur_epoch+pipeline_length) then
    //add amount bond to delta at n+pipeline_length
    bonds[delegator_address][validator_address].deltas[cur_epoch+pipeline_length] += amount
    //debit amount from delegator account and credit it to the PoS account
    balances[delegator_address] -= amount
    balances[pos] += amount
    update_total_deltas(validator_address, pipeline_lenght, amount)
    update_voting_power(validator_address, pipeline_lenght)
    update_total_voting_power(pipeline_lenght)
    update_validator_sets(validator_address, pipeline_lenght)
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
//This function is called by transactions tx_unbond, tx_undelegate and tx_redelegate
func unbond(validator_address, delegator_address, amount)
{
  //disallow unbonding if the validator is frozen
  if (is_validator(validator_address, cur_epoch+pipeline_length) && validators[validator_address].frozen == false) then
    //compute total bonds from delegator to validator
    var delbonds = compute_total_from_deltas(bonds[delegator_address][validator_address].deltas, cur_epoch + unbonding_length)
    //check if there are enough bonds
    //this serves to check that there are bonds (in the docs) and that these are greater than the amount we are trying to unbond
    if (delbonds >= amount) then
      //Decrement bond deltas and create unbonds
      var remain = amount
      var epoch_counter = cur_epoch + unbonding_length + 1
      while remain > 0 do
        epoch_counter = max{epoch | bonds[delegator_address][validator_address].deltas[epoch] > 0 && epoch < epoch_counter}
        var bond = bonds[delegator_address][validator_address].deltas[epoch_counter]
        if bond > remain then var unbond_amount = remain
        else var unbond_amount = bond
        unbonds[delegator_address][validator_address].deltas[(epoch_counter,cur_epoch+unbonding_length)] += unbond_amount
        remain -= unbond_amount
      bonds[delegator_address][validator_address].deltas[cur_epoch+unbonding_length] -= amount
      update_total_deltas(validator_address, unbonding_length, -1*amount)
      update_voting_power(validator_address, unbonding_length)
      update_total_voting_power(unbonding_length)
      update_validator_sets(validator_address, unbonding_length)
}
```

```go
/* COMMENT: Somehting to check for correctness https://github.com/informalsystems/partnership-heliax/pull/16#discussion_r924319213 */
//This function is called by transactions tx_withdraw_unbonds_validator and tx_withdraw_unbonds_delegator
func withdraw(validator_address, delegator_address)
{
  var delunbonds = {<start,end,amount> | amount = unbonds[delegator_address][validator_address].deltas[(start, end)] > 0 && end <= cur_epoch }
  //substract any pending slash before withdrawing
  forall (<start,end,amount> in selfunbonds) do
    var amount_after_slashing = amount
    forall (slash in slashes[validator_address] s.t. start <= slash.epoch && slash.epoch <= end)
      amount_after_slashing += amount*slash.rate
    balance[delegator_address] += amount_after_slashing
    balance[pos] -= amount_after_slashing
    //remove unbond
    unbonds[delegator_address][validator_address].deltas[(start,end)] = 0
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
func new_evidence(evidence)
{
  //create slash
  var total_staked = read_epoched_field(validators[evidence.validator].total_deltas, evidence.epoch, 0)
  var slash = Slash{epoch: evidence.epoch, rate: 0, stake_fraction: compute_stake_fraction(evidence.type, total_staked)}
  //enqueue slash (Step 1.1 of cubic slashing)
  append(enqueued_slashes[evidence.epoch + unbonding_length], slash)
  //jail validator (Step 1.2 of cubic slashing)
  validators[validator_address].jail_record = JailRecord{is_jailed: true, epoch: cur_epoch+1}
  remove_validator_from_sets(validator_address, 1)
  update_total_voting_power(1)
  //freeze validator to prevent delegators from altering their delegations (Step 1.3 of cubic slashing)
  validators[validator_address].frozen = true
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
    forall (validator in sets.active U sets.inactive) do
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
func is_validator(validator_address, epoch){
    return read_epoched_field(validators[validator_address].state, epoch, ⊥) != ⊥
}
```

```go
func compute_stake_fraction(infraction, voting_power){
  switch infraction
    case duplicate_vote: return duplicate_vote_rate * voting_power
    case ligth_client_attack: return ligth_client_attack_rate * voting_power
    default: panic()
}
```

```go
end_of_epoch()
{
  var set_validators = {val | val = slash.validator && slash in enqueued_slashes[cur_epoch]}
  forall (validator_address in set_validators) do
    //iterate over all slashes for infractions within (-1,+1) epochs range (Step 2.1 of cubic slashing)
    var set_slashes = {s | s in enqueued_slashes[epoch] && cur_epoch-1 <= epoch <= cur_epoch+1 && s.validator == validator_address}
    //calculate the slash rate (Step 2.2 of cubic slashing)
    var rate = compute_final_rate(set_slashes)
    forall (slash in {s | s in enqueued_slashes[cur_epoch] && s.validator == validator_address}) do
      //set the slash on the now "finalised" slash amount in storage (Step 2.3 of cubic slashing)
      slash.rate = rate
      append(slashes[validator_address], slash)
      var total_staked = read_epoched_field(validators[validator_address].total_deltas, slash.epoch, 0)
      var slashed_amount = total_staked * slash.rate
      //update voting power (Step 2.4 of cubic slashing)
      update_total_deltas(validator_address, 1, -1*slashed_amount)
      update_voting_power(validator_address, 1)
    //unfreeze the validator (Step 2.5 of cubic slashing)
    validators[validator_address].frozen = false
  cur_epoch = cur_epoch + 1
}
```

```go
//Cubic slashing function
compute_final_rate(slashes)
{
  var voting_power_fraction = 0
  forall (slash in slashes) do
    voting_power_fraction += slash.voting_power_fraction
  return max{0.01, min{1, voting_power_fraction^2 * 9}}
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

```go
func compute_total_from_deltas(deltas, upper_epoch)
{
  var epoch = 0
  var sum = 0
  while (epoch <= upper_epoch)
    sum += delta[epoch]
    epoch++
  }
  return sum
}
```
<!--
## Invariants (WIP)

### From the PoS validity predicate

These are derived from the check on the accumulators that the PoS validity predicate does.

Following, some simplifications on the notation and functions that we use in the invariants.

* To avoid convoluted notation, we avoid using functions such as read_epoched_field, total_deltas_at and compute_total_from_deltas to lookup epoched data. Thus, for instance when we write `validators[validator].total_deltas[epoch]`, we really mean `total_deltas_at(validators[validator].total_deltas, epoch)`. Similarly, when we write bonds[address][validator].deltas[epoch], we really mean compute_total_from_deltas(bonds[address][validator].deltas, epoch).

* Function `total_bonds(validator, epoch)` aggregates all the bonds of a given validator at a given epoch.

```go
total_bonds(validator, epoch)
{
  var total_bonds = 0
  var addresses = {address | bonds[address][validator].deltas[epoch] > 0}
  forall (address in addresses) do
    total_bonds += bonds[address][validator].deltas[epoch]
  return total_bonds
}
```

### Invariant 1
> for any epoch, validator . `validators[validator].total_deltas[epoch] >= 0`

https://github.com/anoma/anoma/blob/master/proof_of_stake/src/validation.rs#L694-L698
https://github.com/anoma/anoma/blob/master/proof_of_stake/src/validation.rs#L763-L767

### Invariant 2
> for any validator, epoch . `validators[validator].total_deltas[epoch] == total_bonds(validator, epoch)`

https://docs.anoma.network/master/explore/design/ledger/pos-integration.html:
"For each `total_deltas`, there must be the same delta value in `bond_delta`"
https://github.com/anoma/anoma/blob/master/proof_of_stake/src/validation.rs#L1244-L1250


### Invariant 3
> for any validator, epoch . `total_bonds(validator, epoch) `
-->

<!-- 
CUBIC SLASHING
```go
end_of_epoch()
{
  slashing()
  //Manu: is there an special state for jalied validators?
  jailing() //TODO
  rewarding() //TODO
}
```

```go
slashing(){
  //for each validator
  forall (address, validator in validators) do
    //compute set of slashes from the last two epochs
    var set_slashes = {slash | slash in slashes[address] && cur_epoch-1 <= slash.epoch] }
    //compute slash rate
    var slash_rate = calculate_slash_rate(set_slashes)
    forall (slash in set_slashes) do
      var max_epoch := max{epoch | validators[address].total_deltas[epoch] != 0 && epoch <= slash.epoch}
      var slashed_amount := validators[address].total_deltas[max_epoch]*slash_rate
      //compute new total_deltas and write it at n+pipeline_length
      var total = total_deltas_at(validators[address].total_deltas, cur_epoch+pipeline_length)
      validators[address].total_deltas[cur_epoch+pipeline_length] = total - slashed_amount 
      //update validator's voting_power, total_voting_power and validator_sets at n+pipeline_length
      validators[validator_address].voting_power[cur_epoch+pipeline_length] = compute_voting_power()
      total_voting_power[cur_epoch+pipeline_length] = compute_total_voting_power(cur_epoch+pipeline_length)
      validator_sets[cur_epoch+pipeline_length] = compute_validator_sets()
}
```
```go
//Cubic slashing function
calculate_slash_rate(slashes)
{
  var voting_power_fraction = 0
  forall (slash in slashes) do
    voting_power_fraction += slash.validator.voting_power
  return max{0.01, min{1, voting_power_fraction^2 * 9}}
}
```
-->