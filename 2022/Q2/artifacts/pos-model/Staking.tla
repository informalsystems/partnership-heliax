------------------------- MODULE Staking ---------------------------------
(*
 * Modeling the Anoma's staking module.
 * This is a very minimal spec that includes delegate, unbond and withdraw
 *
 * Simplifications:
 *   - We assume only one validator to be delegated to.
 *   - Rewards are not specified.
 *   - Jailing is not specified.
 *   - Slashing and evidence handling is not specified.
 * 
 * Manuel Bravo, 2022
 *)
EXTENDS Integers, Apalache, Staking_typedefs

CONSTANTS
    \* Set of all addresses on Cosmos.
    \* @type: Set(ADDR);
    UserAddrs

VARIABLES
    \* Coin balance for every Cosmos account.
    \*
    \* @type: BALANCE;
    balanceOf,
    \* Balance of unbonded coins that cannot be used during the bonding period.
    \*
    \* @type: BALANCE;
    unbonded,
    \* Coins that are delegated to Validator.
    \*
    \* @type: BALANCE;
    delegated

\* Variables that model transactions, epochs and offsets, not the state machine.
VARIABLES    
    \* The last executed transaction.
    \*
    \* @type: TX;
    lastTx,
    \* A serial number to assign unique ids to transactions
    \* @type: Int;
    nextTxId,
    \* Counts the transactions executed within an epoch
    \* @type: Int;
    txCounter,
    \* A serial number used to identify epochs
    \* @type: Int;
    epoch,
    \* Whether at least one transaction has failed
    \* @type: Bool;
    failed

\* the maximum value in Cosmos
MAX_UINT == 2^(256 - 60) - 1

\* 1 billion coins in the initial supply
INITIAL_SUPPLY == 10^(9+18)

\* the number of coins the validator has staked
INIT_VALIDATOR_STAKE == 1000000000000000000000

\* tx per epoch
TXS_PER_EPOCH == 10

\* the validator account
Validator == "validator"

\* Initialize the balances
Init ==
    /\ balanceOf = [ a \in UserAddrs |->
        IF a /= "validator"
        THEN INITIAL_SUPPLY
        ELSE INITIAL_SUPPLY - INIT_VALIDATOR_STAKE
       ]
    /\ unbonded = [ a \in UserAddrs |-> 0 ]
    /\ delegated = [
        a \in UserAddrs |-> IF a /= "validator"
        THEN 0
        ELSE INIT_VALIDATOR_STAKE
       ]
    /\ nextTxId = 0
    /\ epoch = 1
    /\ txCounter = 0
    /\ lastTx = [ id |-> 0, tag |-> "None", fail |-> FALSE ]
    /\ failed = FALSE


\* delegate `amount` coins to Validator
Delegate(sender, amount) ==
    LET fail ==
        \/ amount < 0
        \/ amount > balanceOf[sender]
    IN
    /\ lastTx' = [ id |-> nextTxId, tag |-> "delegate", fail |-> fail,
                   sender |-> sender, toAddr |-> Validator, value |-> amount ]
    /\ nextTxId' = nextTxId + 1
    /\ failed' = (fail \/ failed)
    /\  IF fail
        THEN
          UNCHANGED <<balanceOf, unbonded, delegated>>
        ELSE
          \* transaction succeeds
          \* update the balance of 'sender'
          /\ balanceOf' =
                [ balanceOf EXCEPT ![sender] = @ - amount]
          /\ delegated' = [ delegated EXCEPT ![sender] = @ + amount ]
          /\ UNCHANGED unbonded


\* unbond `amount` coins from Validator
Unbond(sender, amount) ==
    LET fail ==
        \/ amount < 0
        \/ sender = Validator
        \/ amount > delegated[sender]
    IN
    /\ lastTx' = [ id |-> nextTxId, tag |-> "unbond", fail |-> fail,
                   sender |-> sender, toAddr |-> Validator, value |-> amount ]
    /\ nextTxId' = nextTxId + 1
    /\ failed' = (fail \/ failed)
    /\  IF fail
        THEN
          UNCHANGED <<balanceOf, unbonded, delegated>>
        ELSE
          \* transaction succeeds
          /\ unbonded' = [ unbonded EXCEPT ![sender] = @ + amount ]
          /\ delegated' = [ delegated EXCEPT ![sender] = @ - amount ]
          /\ UNCHANGED  balanceOf

\* withdraw unbonded coins
Withdraw(sender) ==
    LET fail ==
        \/ sender = Validator
        \/ unbonded[sender] <= 0
    IN
    /\ lastTx' = [ id |-> nextTxId, tag |-> "withdraw", fail |-> fail,
                   sender |-> sender, toAddr |-> Validator, value |-> unbonded[sender] ]
    /\ nextTxId' = nextTxId + 1
    /\ failed' = (fail \/ failed)
    /\  IF fail
        THEN
          UNCHANGED <<balanceOf, unbonded, delegated>>
        ELSE
          \* transaction succeeds
          /\ balanceOf' = [ balanceOf EXCEPT ![sender] = @ + unbonded[sender] ]
          /\ unbonded' = [ unbonded EXCEPT ![sender] = 0 ]
          /\ UNCHANGED  delegated

AdvanceEpoch ==
    /\  IF txCounter = TXS_PER_EPOCH
        THEN
          \* move to the next epoch
          /\ epoch' = epoch + 1
          /\ txCounter' = 0
        ELSE
          \* do not advance epoch
          /\ txCounter' = txCounter + 1
          /\ UNCHANGED  epoch

\* The transition relation, which chooses one of the actions
Next ==
    \/ \E sender \in UserAddrs:
       \E amount \in Int:
        /\ amount <= MAX_UINT
        /\ \/ Delegate(sender, amount)
           \/ Unbond(sender, amount)
           \/ Withdraw(sender)
        /\ AdvanceEpoch

\* The transition relation assuming that no failure occurs
NextNoFail ==
    Next /\ ~failed /\ ~failed'

(* False invariants to debug the spec *)


===============================================================================