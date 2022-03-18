## Assumptions/simplifications

- There is a single token type

## Data types

```go
epoch = int

validator = {
  consensus_key = map<epoch, key>,
  state = map<epoch, {inactive, pending, candidate}>,
  total_deltas = map<epoch, int>,
  voting_power = map<epoch, u64>,
  reward_address = address}

bond = {
  validator = address,
  source = address,
  deltas = map<epoch, int>}

unbond = {
  validator = address,
  source = address
  deltas = map<(start:epoch, end:epoch), int>}

slash = {
  epoch,
  block_height,
  rate,
  slash_type}

weighted_validator = {
  validator = address,
  voting_power = u64
}

validator_set = {
  active = orderedset<weighted_validator>
  inactive = orderedset<weighted_validator>
}
```

## Variables

```go
cur_epoch = 0 in \mathbb{Z} //current epoch

validators //map from address to validator
balances //map from address to integer
bonds //map from address to map from address to bond
unbonds //map from address to map from address to unbond
slashes //map from address to list of slashes

validator_sets //map from epoch to validator_set
total_voting_power //map from epoch to u64 (voting_power)
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
  validators[validator_address].status[cur_epoch+pipeline_length] = inactive
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
  validators[validator_address].voting_power[cur_epoch+pipeline_length] = compute_voting_power()
  total_voting_power[cur_epoch+pipeline_length] = compute_total_voting_power(cur_epoch+pipeline_length)
  validator_sets[cur_epoch+pipeline_length] = compute_validator_sets()
}
```

```go
//Manu: I have a doubt here. I do not know when the unbond record is created. The texts and Ray say that inmediately, Tomas said that at n+unbound_length
unbound(validator_address, amount)
{
  //compute total self-bonds
  var selfbond = compute_total_from_deltas(bonds[validator_address][validator_address].deltas)
  //check if there are enough selfbonds
  //this serves to check that there are selfbonds (in the docs) and that these are greater than the amount we are trying to unbond (surprisingly not in the docs)
  //Manu: why is the latter not checked?
  if (selfbonded < amount) then panic()
  //compute total self-unbonds and panic if the difference between selfbond and selfunbonds is less than 0 after taking amount from selfbonds
  //Manu: I have no clue why. This lets them to maintain the invariant that selfbonds >= selfunbonds
  var selfunbonds = compute_total_from_deltas(unbonds[validator_address][validator_address].deltas)
  if (selfbond - selfunbond < amount) then panic()
  //Decrement bond deltas and create unbonds
  //Manu: many questions here, waiting for reply
  var remain = amount
  var next_epoch = cur_epoch + 1
  while remain > 0 do
    next_epoch = max{epoch | bonds[validator_address][validator_address].deltas[epoch].amount > 0 && epoch < next_epoch}
    var bond = bonds[validator_address][validator_address].deltas[next_epoch]
    if bond.amount > remain then
      var unbond_amount = remain
      bonds[validator_address][validator_address].deltas[epoch_counter].amount -= remain
    else
      var unbond_amount = bond.amount
      bonds[validator_address][validator_address].deltas[epoch_counter].amount = 0
    unbonds[validator_address][validator_address].deltas[(bond.epoch,cur_epoch+unbonding_length)] = unbond_amount
    remain -= unbond_amount
  //compute new total_deltas and write it at n+unbonding_length
  var total = total_deltas_at(validators[validator_address].total_deltas, cur_epoch+unbonding_length)
  validators[validator_address].total_deltas[cur_epoch+unbonding_length] = total - amount
  //update validator's voting_power, total_voting_power and validator_sets at n+unbonding_length
  validators[validator_address].voting_power[cur_epoch+unbonding_length] = compute_voting_power()
  total_voting_power[cur_epoch+unbonding_length] = compute_total_voting_power(cur_epoch+unbonding_length)
  validator_sets[cur_epoch+unbonding_length] = compute_validator_sets())
}
```

```go
withdraw_unbonds(validator_address)
{
  //panic if no self-unbonds]
  //Manu: check that the epoch check is done on unbond.end and not somehting else. In docs says unbond.epoch, which is unclear
  var selfunbonds = {unbond | unbond in unbonds[validator_address][validator_address] && unbond.end <= cur_epoch && unbond.amount > 0}
  if (selfunbonds is empty) then panic()
  //substract any pending slash before withdrawing
  forall (unbond in selfunbonds) do
    var amount_after_slashing = unbond.amount
    forall (slash in slashes[validator_address] s.t. unbond.start <= slash.epoch && slash.epoch <= unbond.end)
      amount_after_slashing *= (10000 - slash.rate) / 10000)
    balance[validator_address] +=amount_after_slashing
    balance[pos] -= amount_after_slashing
    //Manu: removing unbonds and slashes? Am I missing something? This seems important.
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
new_evidence(evidence){
  append(slash[evidence.validator_address], evidence)
}
```

```go
end_of_epoch()
{
  slashing()
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
compute_voting_power()
{

}
```
```go
compute_total_voting_power(epoch)
{
  var total = 0
  forall (validator in validator_sets[epoch].active U validator_sets[epoch].inactive) do
    sum= += validator.voting_power
  return sum
}
```
```go
compute_validator_set()
{

}
```
```go
calculate_slash_rate(slashes)
{
  var voting_power_fraction = 0
  forall (slash in slashes) do
    voting_power_fraction += slash.validator.voting_power
  return max{0.01, min{1, voting_power_fraction^2 * 9}}
}
```


## Auxiliary functions

```go
//Manu: I am not sure about this. I am guessing total_deltas accumulate deltas, so to update it one has to add it to the previous total_deltas
total_deltas_at(total_deltas, upper_epoch){}
  var max_epoch = max{epoch | total_deltas[epoch] != 0 && epoch <= upper_epoch}
  return total_deltas[max_epoch]
}
```

```go
compute_total_from_deltas(deltas)
{
  var sum = 0
  forall(delta in deltas){
    sum += delta.amount
  }
  return sum
}
```