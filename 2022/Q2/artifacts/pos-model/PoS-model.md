## Assumptions/simplifications

- There is a single token type

## Data types

```go
epoch = int

validator = {
  consensus_key = map<epoch, key>,
  state = map<epoch, {inactive, pending, candidate}}>,
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
  deltas = map<(epoch, epoch), int>}

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
accounts //map from address to integer
bonds //map from address to map from address to bond
unbonds //map from address to map from address to unbond
slashes //map from address to list of slashes

validator_sets //map from epoch to validator_set
total_voting_power //map from epoch to u64 (voting_power)
```

## Validator transactions:

```go
become_validator(validator_address, consensus_key)
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
  accounts[validator_address] -= amount
  accounts[pos] += amount
  //compute new total_deltas and write it at n+pipeline_length
  var total = add_to_total_deltas(validators[validator_address].total_deltas, amount)
  validators[validator_address].total_deltas[cur_epoch+pipeline_length] = total
  validators[validator_address].voting_power[cur_epoch+pipeline_length] = compute_voting_power()
  var e3 = fun(update_voting_power(validator_address))
  var e4 = fun(update_total_voting_power())
  var e5 = fun(update_validator_set))
  append(pipeline[cur_epoch+pipeline_length], [e1,e2,e3,e4,e5])
}
```

```go
unbound(validator_address, amount)
{
  var total_bonded = compute_total_from_deltas(bond[validator_address][validator_address].deltas)
  if (total_bonded < amount) then panic
  var remain := amount
  foreach (bond in bonds[validator_address][validator_address].deltas)) while (remain > 0) do
    if amount > remain then
      var unbond_amount = remain
      bonds[validator_address][validator_address].deltas[bond.epoch].amount -= remain
    else
      var unbond_amount = next.amount
      bonds[validator_address][validator_address].deltas[bond.epoch].amount = 0
    unbonds[validator_address][validator_address].deltas[(bond.epoch,cur_epoch)] = unbond_amount
    remain -= unbond_amount
  var e1 = substract(validators[validator_address].total_deltas[token][cur_epoch+unbonding_length], amount)
  var e2 = fun(update_voting_power,validator_address)
  var e3 = fun(update_total_voting_power,[])
  var e4 = fun(update_validator_set,[])
  append(pipeline[cur_epoch+unbonding_length], [e1,e2,e3,e4])
}
```

```go
withdraw_unbonds(validator_address)
{
  var unbonds = unbonds[validator_address][validator_address].deltas)
  if (unbonds == []) then panic
  foreach (unbond in unbounds s.t. unbound.end <= cur_epoch) do
    var amount_after_slashing = unbond.amount
    foreach (slash in slashes[validator_address] s.t. unbond.start <= slash.epoch && slash.epoch <= unbond.end)
      amount_after_slashing *= (10000 - slash.rate) / 10000)
    balance[validator_address] +=amount_after_slashing
    balance[pos] -= amount_after_slashing
    //removing unbonds and slashes?
}
```

```go
change_consensus_key(validator_address)
{
  var e1 = set(validators[validator_address].consensus_key, consensus_key)
  append(pipeline[cur_epoch+pipeline_length], e1)
}
```
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
  jailing()
  rewarding()
}
```

```go
slashing(){
  //for each validator
  forall (address, validator in validators) do
    //compute set of slashes from the last two epochs
    var slashes = {slash | slash in slashes[validator && cur_epoch-1 <= slash.epoch] }
    //compute slash rate
    var slash_rate = calculate_slash_rate(slashes)
    forall (slash in slashes) do
      var max_epoch := max{epoch | validators[address].total_deltas[epoch] != 0 && epoch <= evidence.epoch}
      var slashed_amount := validators[address].total_deltas[max_epoch]*slash_rate
      e1 = substract(validators[validator_address].total_deltas[cur_epoch+pipeline_length], slashed_amount)
      e2 = fun(update_voting_power(validator_address))
      e3 = fun(update_total_voting_power())
      e4 = fun(update_validator_set))
      append(pipeline[cur_epoch+pipeline_length], [e1,e2,e3,e4])
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
```go
compute_voting_power()
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
add_to_total_deltas(total_deltas, amount){}
  var max_epoch := max{epoch | total_deltas[epoch] != 0 && epoch <= cur_epoch+pipeline_length}
  return amount + total_deltas[upper_epoch]
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