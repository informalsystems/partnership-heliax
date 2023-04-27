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
  redelegation Redelegation
}

type SlashedAmount struct {
  epoch Epoch
  amount uint
}

type Validator struct {
  consensus_key map<Epoch, Key>
  state map<Epoch, {inactive, candidate}>
  total_deltas map<Epoch, amount:int>
  set_unbonds map<Epoch, Set<UnbondRecord>>
  voting_power map<Epoch, VotingPower>
  reward_address Addr
  jail_record JailRecord
  frozen map<Epoch, bool>
  redelegations map<Addr, map<Addr, IncomingRedelegation>>
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
  amount uint
}

type IncomingRedelegation struct {
  epoch Epoch
  amount uint
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
redelegated_bonds[][][] in (Addr X Addr X Epoch) → Redelegation //map from (address, address, epoch) to redelegation
redelegated_unbonds[][][] in (Addr X Addr X (Epoch, Epoch)) → Redelegation //map from (address, address, (epoch, epoch)) to redelegation
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
    validators[validator_address].frozen[cur_epoch] = false
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

```go
func is_chained_redelegation(dest_validator_address, delegator_address)
  // avoid iteration over validators and do it over incoming_redelegations
  forall (val in validators) do
    var redelegation = validators[dest_validator_address].redelegations[val][delegator_address]
    if (redelegation.epoch >= 0 && redelegation.epoch + unbonding_length > cur_epoch) then
      return true
  return false
```

```go
tx_redelegate(src_validator_address, dest_validator_address, delegator_address)
{
  // Disallow re-delegation if the source validator is frozen (similar to unbonding)
  var src_frozen = read_epoched_field(validators[src_validator_address].frozen, cur_epoch, false)
  if (is_validator(src_validator_address, cur_epoch+pipeline_length) && src_frozen == false) then
    // Check that `incoming_redelegations[delegator_address]` for `dest_validator_address` either don't exist
    // or if they do, they cannot be slashed anymore (`end + unbonding_length <= cur_epoch`)
    if is_chained_redelegation(src_validator_address, delegator_address) then
      return
    // Find the sum of bonded tokens to `src_validator_address`
    var delbonds = {<start, amount> | amount = bonds[delegator_address][src_validator_address].deltas[start] > 0 && start <= cur_epoch + unbonding_length}
    var bonded_tokens = sum{amount | <start, amount> in delbonds}
    // Unbond the tokens from `src_validator_address` at pipeline offset, but 
    // without recording it in the `unbonds[delegator_address][src_validator_address]`
    var record_unbonds = false
    var amount_after_slashing = unbond(src_validator_address, delegator_address, bonded_tokens, record_unbonds)
    // add a bond in the `dest_validator_address` for the amount after slashing
    // done manually to avoid account transfer
    bonds[delegator_address][dest_validator_address].deltas[cur_epoch+pipeline_length] += amount_after_slashing
    redelegated_bonds[delegator_address][dest_validator_address][cur_epoch+pipeline_length] = Redelegation{validator: src_validator_address,
                                                                                                           amount: amount_after_slashing}
    //save the epoch at which the redelegation occurs to track chained redelegations
    validators[dest_validator_address].redelegations[src_validator_address][delegator_address] = IncomingRedelegation{epoch: cur_epoch,
                                                                                                                      amount: amount_after_slashing}
    update_total_deltas(dest_validator_address, pipeline_length, amount_after_slashing)
    update_voting_power(dest_validator_address, pipeline_length)
    update_total_voting_power(pipeline_length)
    update_validator_sets(dest_validator_address, pipeline_length)
}
```

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
func unbond(validator_address, delegator_address, total_amount, record_unbonds)
{
  //disallow unbonding if the validator is frozen
  var frozen = read_epoched_field(validators[validator_address].frozen, cur_epoch, false)
  if (is_validator(validator_address, cur_epoch+pipeline_length) && frozen == false) then
    //compute total bonds from delegator to validator
    var delbonds = {<start, amount> | amount = bonds[delegator_address][validator_address].deltas[start] > 0 && start <= cur_epoch + unbonding_length}
    //check if there are enough bonds
    //this serves to check that there are bonds (in the docs) and that these are greater than the amount we are trying to unbond
    if (sum{amount | <start, amount> in delbonds} >= total_amount) then
      var remain = total_amount
      var amount_after_slashing = 0
      //Iterate over bonds and create unbond
      forall (<start, amount> in delbonds while remain > 0) do
        //Retrieve the bond's associated redelegation record (if any)
        var redelegation_record = redelegated_bonds[delegator_address][validator_address][start]
        //Take the minimum between the remainder and the unbond. This is equal to amount if remain > amount and remain otherwise 
        var amount_unbonded = min{amount, remain}
        var redelegated_amount = 0
        if redelegation_record != ⊥ then
          redelegated_amount = redelegation_record.amount

        var amount_unbonded_after_slashing = 0
        //compute amount after slashing if some of the tokens do not come from redelegation
        if redelegated_amount < amount_unbonded then 
          // set of slashes that happened while the bond was contributing to the validator's stake
          var set_slashes = {s | s in slashes[validator_address] && start <= s.epoch }
          amount_unbonded_after_slashing = compute_amount_after_slashing(set_slashes, amount_unbonded - redelegated_amount)
        //compute amount after slashing  of the tokens coming from redelegation
        if redelegation_record != ⊥ then
          set_slashes = set_slashes \union {slash | slash in slashes[redelegation_record.validator] &&
                                                    //start - pipeline_length is the epoch when the redelegation was issued
                                                    //any slashed processed at an epoch < slash - pipeline_length - unbonding_length has been applied already
                                                    start - pipeline_length - unbonding_length <= slash.epoch < start}
          amount_unbonded_after_slashing += compute_amount_after_slashing(set_slashes, min{redelegated_amount, amount_unbonded})

        amount_after_slashing += amount_unbonded_after_slashing

        //update bond and create new unbond if record_unbonds=true
        bonds[delegator_address][validator_address].deltas[start] = amount - amount_unbonded

        var end = cur_epoch+pipeline_length+unbonding_length
        if record_unbonds then
          unbonds[delegator_address][validator_address].deltas[start, end] = amount_unbonded

        //manage redelegation records
        var redelegation_record_set_unbonds = ⊥
        if redelegation_record != ⊥ then
          
          if record_unbonds then
            update_unbond_redelegation_record(delegator_address,
                                              validator_address,
                                              redelegation_record.validator,
                                              start,
                                              end,
                                              min{redelegation_record.amount, amount_unbonded})
          if redelegation_record.amount > amount_unbonded then
            redelegation_record_set_unbonds = Redelegation{validator: redelegation_record.validator, amount: redelegation_record.amount - amount_unbonded}
            redelegated_bonds[delegator_address][validator_address][start] = redelegation_record_set_unbonds
          else
            redelegation_record_set_unbonds = Redelegation{validator: redelegation_record.validator, amount: redelegation_record.amount}
            redelegated_bonds[delegator_address][validator_address][start] = ⊥
  
        //The current model disregards a corner case that should be taken care of in the implementation:
        //- Assume a user delegates 10 tokens to a validator at epoch e1
        //- Assume the user unbonds twice 5 tokens from the same validator in the same epoch in two different transactions e2
        //- When executing the first undelegate tx, the model creates the record UnbondRecord{amount: 5, start: e1} and updates the bond to 5 tokens
        //- When executing the second undelegate tx, the model creates the same record UnbondRecord{amount: 5, start: e1} and removes the bond.
        //- The problem is that we keep unbond records in a set and when we try to add the second record, since it is a duplicate, it will be discarded.
        //It is an easy fix I'd say: use a bag instead of a set to allow duplicates, or check if the set includes the record and act upon
        //(remove it, create a new one with double the amount, and add it).
        var unbond_record = UnbondRecord{amount: amount_unbonded, start: start, redelegation: redelegation_record_set_unbonds}
        validators[validator_address].set_unbonds[cur_epoch+pipeline_length] = {unbond_record} \union validators[validator_address].set_unbonds[cur_epoch+pipeline_length]

        remain -= amount_unbonded
      update_total_deltas(validator_address, pipeline_length, -1*amount_after_slashing)
      update_voting_power(validator_address, pipeline_length)
      update_total_voting_power(pipeline_length)
      update_validator_sets(validator_address, pipeline_length)
      return amount_after_slashing
}
```

```go
func update_unbond_redelegation_record(delegator_address, src_validator_address, dest_validator_address, start, end, amount)
{
  var unbond_redelegation_record = redelegated_unbonds[delegator_address][dest_validator_address][start, end]
  if (unbond_redelegation_record = ⊥) then
    var new_record = Redelegation{validator: src_validator_address, amount: amount}
  else
    var new_record = Redelegation{validator: src_validator_address, amount: unbond_redelegation_record.amount + amount}
  redelegated_unbonds[delegator_address][dest_validator_address][start, end] = new_record
}   
```

```go
/* COMMENT: Something to check for correctness https://github.com/informalsystems/partnership-heliax/pull/16#discussion_r924319213 */
//This function is called by transactions tx_withdraw_unbonds_validator and tx_withdraw_unbonds_delegator
func withdraw(validator_address, delegator_address)
{
  var delunbonds = {<start,end,amount> | amount = unbonds[delegator_address][validator_address].deltas[(start, end)] > 0 && end <= cur_epoch }
  //substract any pending slash before withdrawing
  forall (<start,end,amount,redelegation_record> in delunbonds) do
    //retrieve redelegation record
    var redelegation_record = redelegated_unbonds[delegator_address][validator_address][start, end]
    var redelegated_amount = 0
    if redelegation_record != ⊥ then
      redelegated_amount = redelegation_record.amount
    // set of slashes that happened while the bond was contributing to the validator's stake
    var set_slashes = {s | s in slashes[validator_address] && start <= s.epoch && s.epoch < end - unbonding_length }
    var amount_after_slashing = compute_amount_after_slashing(set_slashes, amount - redelegated_amount)
    if redelegation_record != ⊥ then
      // add slashes if the tokens were redelegated
      set_slashes = set_slashes \union {slash | slash in slashes[redelegation_record.validator] &&
                                                //start - pipeline_length is the epoch when the redelegation was issued
                                                //any slashed processed at an epoch < slash - pipeline_length - unbonding_length
                                                //has been applied already
                                                start - pipeline_length - unbonding_length <= slash.epoch < start}
      amount_after_slashing += compute_amount_after_slashing(set_slashes, redelegated_amount)

    balance[delegator_address] += amount_after_slashing
    balance[pos] -= amount_after_slashing
    //remove unbond
    unbonds[delegator_address][validator_address].deltas[(start,end)] = 0
    //manage redelegation records
    redelegated_unbonds[delegator_address][dest_validator_address][start, end] = ⊥

}
```

```go
func compute_amount_after_slashing(set_slashes, amount) {
  var computed_amounts = {}
    var updated_amount = amount
    forall (slash in set_slashes in slash.epoch order) do
      //Update amount with slashes that happened more than `unbonding_length` before this slash
      forall (slashed_amount in computed_amounts s.t. slashed_amount.epoch + unbonding_length < slash.epoch) do
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
func new_evidence(evidence)
{
  //create slash
  var total_staked = read_epoched_field(validators[evidence.validator].total_deltas, evidence.epoch, 0)
  var slash = Slash{epoch: evidence.epoch, validator: evidence.validator, rate: 0, stake_fraction: compute_stake_fraction(evidence.type, total_staked)}
  //enqueue slash (Step 1.1 of cubic slashing)
  append(enqueued_slashes[evidence.epoch + unbonding_length], slash)
  //jail validator (Step 1.2 of cubic slashing)
  validators[validator_address].jail_record = JailRecord{is_jailed: true, epoch: cur_epoch+1}
  remove_validator_from_sets(validator_address, 1)
  update_total_voting_power(1)
  //freeze validator to prevent delegators from altering their delegations (Step 1.3 of cubic slashing)
  freeze_validator(validator_address)
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
    var total = read_epoched_field(validators[validator_address].frozen, epoch, false)
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
  //iterate over all slashes for infractions within (-1,+1) epochs range (Step 2.1 of cubic slashing)
  var set_slashes = {s | s in enqueued_slashes[epoch] && cur_epoch-1 <= epoch <= cur_epoch+1}
  //calculate the slash rate (Step 2.2 of cubic slashing)
  var rate = compute_final_rate(set_slashes)

  var set_validators = {val | val = slash.validator && slash in enqueued_slashes[cur_epoch]}
  forall (validator_address in set_validators) do
    forall (slash in {s | s in enqueued_slashes[cur_epoch] && s.validator == validator_address}) do
      //set the slash on the now "finalized" slash amount in storage (Step 2.3 of cubic slashing)
      slash.rate = rate
      append(slashes[validator_address], slash)
      var total_staked = read_epoched_field(validators[validator_address].total_deltas, slash.epoch, 0)
      slash_misbehaving_validator(validator_address, slash, total_staked)

      forall (val in validators) do
        var pairs = { pair = <delegator, <epoch, redelegation> | pair in validators[val].redelegations[validator_address] &&
                                                                 pair !=⊥ && 
                                                                 redelegation.epoch - unbonding_length <= slash.epoch < redelegation.epoch + pipeline_length}
        forall (<delegator, redelegation> in pairs) do
          var staked_redelegated = 
          slash_redelegated_validator(val, validator_address, slash, redelegation.amount)

    //unfreeze the validator (Step 2.5 of cubic slashing)
    //this step is done in advance when the evidence is found
    //by setting validators[validator_address].frozen[cur_epoch+unbonding_length+1]=false
    //note that this index could have been overwritten if more evidence for the same validator
    //where found since then
  cur_epoch = cur_epoch + 1
}
```

```go
func slash_misbehaving_validator(src_validator_address, dest_validator_address, slash, total_staked)
{
  var total_unbonded = 0
  //find the total unbonded from the slash epoch up to the current epoch first
  //a..b notation determines an integer range: all integers between a and b inclusive
  forall (epoch in slash.epoch+1..cur_epoch) do
    forall (unbond in validators[validator_address].set_unbonds[epoch] s.t. unbond.start <= slash.epoch)

      //retrieve redelegation record
      var redelegation_record = unbond.redelegation
      var redelegated_amount = 0
      if redelegation_record != ⊥ then
        redelegated_amount = redelegation_record.amount
      // set of slashes that happened while the bond was contributing to the validator's stake
      // We only need to apply a slash s if s.epoch < unbond.end - unbonding_length
      // It is easy to see that s.epoch + unbonding_length < slash.epoch implies s.epoch < unbond.end - unbonding_length
      // 1) slash.epoch = cur_epoch - unbonding_length
      // 2) unbond.end = cur_epoch + offset + unbonding_length => cur_epoch = unbond.end - offset - unbonding_length
      // By 1) s.epoch + unbonding_length < cur_epoch - unbonding_length
      // By 2) s.epoch + unbonding_length < unbond.end - offset - 2*unbonding_length => s.epoch < unbond.end - offset - 3*unbonding_length, as required.
      var set_slashes = {s | s in slashes[validator_address] &&
                             unbond.start <= s.epoch &&
                             s.epoch + unbonding_length < slash.epoch }
     total_unbonded += compute_amount_after_slashing(set_slashes, unbond.amount - redelegated_amount)
      if redelegation_record != ⊥ then
        // add slashes if the tokens were redelegated
        set_slashes = set_slashes \union {s | s in slashes[redelegation_record.validator] &&
                                              //unbond.start - pipeline_length is the epoch when the redelegation was issued
                                              //any slashed processed at an epoch < unbond.start - pipeline_length has
                                              //been applied already, so we ignore them.
                                              //a slash with epoch e is processed at e + unbonding_length, we should then consider slashes
                                              //such that slash.epoch + unbonding_length >= unbond.start - pipeline_length
                                              unbond.start - pipeline_length - unbonding_length <= s.epoch < unbond.start &&
                                              //slash s is processed before the misbehaving epoch (slash.epoch)
                                              s.epoch + unbonding_length < slash.epoch}
        total_unbonded += compute_amount_after_slashing(set_slashes, redelegated_amount)

  var last_slash = 0
  // up to pipeline_length because there cannot be any unbond in a greater ß (cur_epoch+pipeline_length is the upper bound)
  forall (offset in 1..pipeline_length) do
    forall (unbond in validators[validator_address].set_unbonds[cur_epoch + offset] s.t. unbond.start <= slash.epoch) do

      //retrieve redelegation record
      var redelegation_record = unbond.redelegation
      var redelegated_amount = 0
      if redelegation_record != ⊥ then
        redelegated_amount = redelegation_record.amount
      // set of slashes that happened while the bond was contributing to the validator's stake
      var set_slashes = {s | s in slashes[validator_address] &&
                              unbond.start <= s.epoch &&
                              s.epoch + unbonding_length < slash.epoch }
      var total_unbonded = compute_amount_after_slashing(set_slashes, unbond.amount - redelegated_amount)
      if redelegation_record != ⊥ then
        // add slashes if the tokens were redelegated
        set_slashes = set_slashes \union {s | s in slashes[redelegation_record.validator] &&
                                              unbond.start - pipeline_length - unbonding_length <= s.epoch < unbond.start &&
                                              s.epoch + unbonding_length < slash.epoch}
        total_unbonded += compute_amount_after_slashing(set_slashes, redelegated_amount)

    var this_slash = (total_staked - total_unbonded) * slash.rate
    var diff_slashed_amount = last_slash - this_slash
    last_slash = this_slash
    update_total_deltas(validator_address, offset, diff_slashed_amount)
    update_voting_power(validator_address, offset)
}
```

```go
func slash_redelegated_validator(validator_address, src_validator, slash, staked_amount)
{
  var total_unbonded = 0
  //find the total unbonded from the slash epoch up to the current epoch first
  //a..b notation determines an integer range: all integers between a and b inclusive
  forall (epoch in slash.epoch+1..cur_epoch) do
    //filter those unbonds that were contributing to the stake when the validator misbehaved
    forall (unbond in validators[validator_address].set_unbonds[epoch] s.t. unbond.start - unbonding_length - pipeline_length <= slash.epoch && 
                                                                            unbond.redelegation != ⊥ &&
                                                                            unbond.redelegation.validator == src_validator) do
      //TODO: check that this set is not always empty
      var set_slashes = {s | s in slashes[validator_address] &&
                             unbond.start - unbonding_length - pipeline_length <= s.epoch &&
                             s.epoch + unbonding_length < slash.epoch }

      total_unbonded += compute_amount_after_slashing(set_slashes, unbond.amount)

  var last_slash = 0
  // up to pipeline_length because there cannot be any unbond in a greater ß (cur_epoch+pipeline_length is the upper bound)
  forall (offset in 1..pipeline_length) do
    forall (unbond in validators[validator_address].set_unbonds[cur_epoch + offset] s.t. unbond.start - unbonding_length - pipeline_length <= slash.epoch && 
                                                                                         unbond.redelegation != ⊥ &&
                                                                                         unbond.redelegation.validator == src_validator) do

      //TODO: check that this set is not always empty
      var set_slashes = {s | s in slashes[validator_address] &&
                             unbond.start - unbonding_length - pipeline_length <= s.epoch &&
                             s.epoch + unbonding_length < slash.epoch }
      total_unbonded += compute_amount_after_slashing(set_slashes, unbond.amount)
    var this_slash = (staked_amount - total_unbonded) * slash.rate
    var diff_slashed_amount = last_slash - this_slash
    last_slash = this_slash
    update_total_deltas(validator_address, offset, diff_slashed_amount)
    update_voting_power(validator_address, offset)
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