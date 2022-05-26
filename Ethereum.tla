------------------------------ MODULE Ethereum ------------------------------

EXTENDS Integers

CONSTANTS
    AccountId, \* the set of all account identifiers
    StellarAccountId,
    Amount,
    Time,
    Hash

Transaction == [
  from : AccountId,
  to : AccountId,
  amount : Amount,
  stellarDst : StellarAccountId,
  hash : Hash,
  refundId : Hash ]

VARIABLES
    executed, \* executed transactions, per block
    time \* ethereum time

Executed == UNION {executed[t] : t \in Time}

UsedHashes == {tx.hash : tx \in Executed}

Init ==
    /\  executed = [t \in Time |-> {}]
    /\  time = 0

Tick ==
    /\  time' = time + 1
    /\  UNCHANGED <<executed>>
    /\  time' \in Time

ExecuteTx(tx) ==
    /\  tx \notin Executed
    /\  tx.hash \notin UsedHashes
    /\  tx.amount >= 0
    /\  tx.from # tx.to
    /\  executed' = [executed EXCEPT ![time] = @ \union {tx}]
    /\  UNCHANGED time

TypeOkay ==
    /\  executed \in [Time -> SUBSET Transaction]
    /\  time \in Time

Inv ==
  \* a transaction is executed at most once:
  \A tx1 \in Executed :
    /\ \A t1,t2 \in Time :
       \/  t1 = t2
       \/  tx1 \in executed[t1] => \neg tx1 \in executed[t2]
  \* all executed transactions have unique hashes:
    /\ \A tx2 \in Executed : tx1 = tx2 \/ tx1.hash # tx2.hash

=============================================================================
