## Assumptions/simplifications

- There is a single token type

## Data types

```go
type Addr
type Key
type Epoch int
type VotingPower float

type Validator struct {
  consensus_key map<Epoch, Key>
  state map<Epoch, {inactive, pending, candidate}>
  total_deltas map<Epoch, amount:int> //amount default value = -1  
  voting_power map<Epoch, float>
  reward_address Addr
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
  validator Addr
  block_height int //not used
  rate float
  slash_type //not used
}

type WeightedValidator struct {
  validator Addr
  voting_power float
}

type ValidatorSet struct {
  active orderedset<WeightedValidator>
  inactive orderedset<WeightedValidator>
}
```

## Variables

```go
cur_epoch ← 0 in Epoch //current epoch

validators[] in Addr → Validator //map from address to validator
balances[] in Addr → int //map from address to integer
bonds[][] in (Addr X Addr) → Bond //map from address to map from address to bond
unbonds[][] in (Addr X Addr) → Unbond  //map from address to map from address to unbond
slashes[] in Addr → 2^Slash //map from address to list of slashes

validator_sets[] in Epoch → ValidatorSet //map from epoch to validator_set
total_voting_power[] in Epoch to VotingPower //map from epoch to voting_power
```

## Validator transactions:

```go
become_validator(validator_address, consensus_key, staking_reward_addresspanic)
{
  //reward_address is not in the docs/spec validator struct
  validators[validator_address].reward_address = staking_reward_address
  //set status to pending inmediately
  validators[validator_address].state[cur_epoch] = pending
  //set status to candidate and consensus key at n + pipeline_length
  validators[validator_address].consensus_key[cur_epoch+pipeline_length] = consensus_key
  validators[validator_address].state[cur_epoch+pipeline_length] = candidate
}
```

```go
//Manu: races between become_validate or reactivate and deactivate. deactivate does not write anything inmediately. This is related to the validity_predicate
deactivate(validator_address)
{
  //set status to inactive at n + pipeline_length
  validators[validator_address].state[cur_epoch+pipeline_length] = inactive
}
```

```go
reactivate(validator_address)
{
  //set status to pending inmediately
  validators[validator_address].state[cur_epoch] = pending
  //set status to candidate at n + pipeline_length
  validators[validator_address].state[cur_epoch+pipeline_length] = candidate
}
```

```go
self_bond(validator_address, amount)
{
  //add amount bond to delta at n+pipeline_length
  bonds[validator_address][validator_address].deltas[cur_epoch+pipeline_length] += amount
  //debit amount form validator account and credit it to the PoS account
  balances[validator_address] -= amount
  balances[pos] += amount
  //compute new total_deltas and write it at n+pipeline_length
  var total = total_deltas_at(validators[validator_address].total_deltas, cur_epoch+pipeline_length)
  validators[validator_address].total_deltas[cur_epoch+pipeline_length] = total + amount
  //update validator's voting_power, total_voting_power and validator_sets at n+pipeline_length
  power_before = validators[validator_address].voting_power[cur_epoch+pipeline_length]
  power_after = update_voting_power(validator_address, cur_epoch+pending_length)
  update_total_voting_power(cur_epoch+pipeline_length)
  update_validator_sets(validator_address, cur_epoch+pipeline_length, power_before, power_after)
}
```

```go
unbond(validator_address, amount)
{
  //compute total self-bonds
  var selfbond = compute_total_from_deltas(bonds[validator_address][validator_address].deltas)
  //check if there are enough selfbonds
  //this serves to check that there are selfbonds (in the docs) and that these are greater than the amount we are trying to unbond
  if (selfbonded < amount) then panic()
  //Decrement bond deltas and create unbonds
  var remain = amount
  var epoch_counter = cur_epoch + unbonding_length + 1
  while remain > 0 do
    epoch_counter = max{epoch | bonds[validator_address][validator_address].deltas[epoch] > 0 && epoch < epoch_counter}
    var bond = bonds[validator_address][validator_address].deltas[epoch_counter]
    if bond > remain then var unbond_amount = remain
    else var unbond_amount = bond
    unbonds[validator_address][validator_address].deltas[(epoch_counter,cur_epoch+unbonding_length)] += unbond_amount
    remain -= unbond_amount
  //Manu: still unsure about this. Now it only creates a single bond record at cur_epoch+unbonding_length.
  bonds[validator_address][validator_address].deltas[cur_epoch+unbonding_length] -= amount
  //compute new total_deltas and write it at n+unbonding_length
  var total = total_deltas_at(validators[validator_address].total_deltas, cur_epoch+unbonding_length)
  validators[validator_address].total_deltas[cur_epoch+unbonding_length] = total - amount
  //update validator's voting_power, total_voting_power and validator_sets at n+unbonding_length
  power_before = validators[validator_address].voting_power[cur_epoch+unbonding_length]
  power_after = update_voting_power(validator_address, cur_epoch+unbonding_length)
  update_total_voting_power(cur_epoch+unbonding_length)
  update_validator_sets(validator_address, cur_epoch+unbonding_length, power_before, power_after)
}
```

```go
withdraw_unbonds(validator_address)
{
  //panic if no self-unbonds
  //Manu: check that the epoch check is done on unbond.end and not somehting else. In docs says unbond.epoch, which is unclear
  var selfunbonds = {<start,end,amount> | amount = unbonds[validator_address][validator_address].deltas[(start, end)] > 0 && end <= cur_epoch }
  if (selfunbonds is empty) then panic()
  //substract any pending slash before withdrawing
  forall (<start,end,amount> in selfunbonds) do
    //Manu: is the amount slashed here the same than the one slashed when evidence is found? This is an important point
    var amount_after_slashing = unbond.amount
    forall (slash in slashes[validator_address] s.t. start <= slash.epoch && slash.epoch <= end)
      amount_after_slashing *= (10000 - slash.rate) / 10000)
    balance[validator_address] += amount_after_slashing
    balance[pos] -= amount_after_slashing
    //remove unbond
    unbonds[validator_address][validator_address].deltas[(start,end)] = 0
}
```

```go
change_consensus_key(validator_address, consensus_key)
{
  //set consensus key at n + pipeline_length
  validators[validator_address].consensus_key[cur_epoch+pipeline_length] = consensus_key
}
```
## Delegator transactions:

It is essentially a copy and paste of the validator transactions with minor changes. Once we converge on the validator transactions, we can spell out the delegators' transactions.

## PoS functions

```go
// assuming evidence is of type Slash for simplicity
new_evidence(evidence){
  append(slash[evidence.validator], evidence)
  //Manu: how to compute the slashed rate when there is no cubic slashing? now using evidence.slash_rate
  //Manu: the salshed amount is computed from total deltas up to evidence.epoch and its deducted at n+pipeline_length. Not saying this is a problem, but it is something to discuss
  //compute slash amount
  var total_evidence = total_deltas_at(validators[evidence.validator].total_deltas, evidence.epoch)
  var slashed_amount = total_evidence*evidence.rate
  //compute new total_deltas and write it at n+pipeline_length
  var total_offset = total_deltas_at(validators[evidence.validator].total_deltas, cur_epoch+pipeline_length)
  validators[evidence.validator].total_deltas[cur_epoch+pipeline_length] = total_offset - slashed_amount 
  //update validator's voting_power, total_voting_power and validator_sets at n+pipeline_length
  power_before = validators[evidence.validator].voting_power[cur_epoch+pipeline_length]
  power_after = update_voting_power(evidence.validator, cur_epoch+pending_length)
  update_total_voting_power(cur_epoch+pending_length)
  update_validator_sets(evidence.validator, cur_epoch+pending_length, power_before, power_after)
}
```

```go
//Sergio: Shall we do updates to this state to happen once at the end of an epoch?
//Manu: Still unclear from the docs. Why are unbonds substracted? When creating unbonds, we already decrement bonds,
//so we should not substract them here again, unless I am missing something
update_voting_power(validator_address, epoch)
{
  //compute self_bonds from total_deltas
  var self_bonds = total_deltas_at(bonds[validator_address][validator_address].total_deltas, epoch)
  //set of delegators with bonds at epoch
  var delegators = {delegator_address | total_deltas_at(bonds[delegator_address][validator_address].total_deltas, epoch) > 0)
  //sum of all delegated bonds
  var delegated_bonds = 0
  forall (delegator at delegators) do
    delegated_bonds += total_deltas_at(bonds[delegator_address][validator_address].total_deltas, epoch)
  //compute the new voting power
  var power_after = votes_per_token*(self_bonds+delegated_bonds)
  //update voting power and return it
  validators[validator_address].voting_power[epoch] = power_after
  return power_after
}
```
```go
update_total_voting_power(epoch)
{
  var total = 0
  forall (validator in validator_sets[epoch].active U validator_sets[epoch].inactive) do
    total += validator.voting_power
  total_voting_power[cur_epoch+unbonding_length] = sum
}
```
```go
update_validator_set(validator_address, epoch, power_before, power_after)
{
  var min_active = first(validator_sets[epoch].active)
  var max_inactive = last(validator_sets[epoch].inactive)
  if (power_before >= max_inactive.voting_power) then
    //if active but it loses power below the max_inactive then move validator to inactive
    //and promote max_inactive
    if (power_after < max_inactive.voting_power) then
      remove(validator_sets[epoch].active, validator_address)
      insert(validator_sets[epoch].active, max_inactive)
      remove(validator_sets[epoch].inactive, max_inactive.validator)
      insert(validator_sets[epoch].inactive, <validator_address, power_after>)
    //if active and its change in power does not degrade it to inactive, then update its voting power
    else
      remove(validator_sets[epoch].active, validator_address)
      insert(validator_sets[epoch].active, <validator_address, power_after>)
  else
    //if inactive and gains power above the min_active, then insert into active and
    //degrade min_active 
    if (power_after > min_active.voting_power) then
      remove(validator_sets[epoch].inactive, validator_address)
      add(validator_sets[epoch].inactive, min_active)
      remove(validator_sets[epoch].active, min_active.validator)
      add(validator_sets[epoch].active, <validator_address, power_after>)
    //if inactive and its change in power does not promote it to active, then update its voting power
    else
      remove(validator_sets[epoch].inactive, validator_address)
      insert(validator_sets[epoch].inactive, <validator_address, power_after>)
}
```
## Auxiliary functions

```go

total_deltas_at(total_deltas, upper_epoch){}
  var max_epoch = max{epoch | total_deltas[epoch] != -1 && epoch <= upper_epoch}
  return total_deltas[max_epoch]
}
```

```go
//There is no epoch upper-bound because the highest epoch must be cur_epoch+offset, and those must be considered.
compute_total_from_deltas(deltas)
{
  var sum = 0
  forall(delta in deltas){
    sum += delta.amount
  }
  return sum
}
```
<!-- 
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