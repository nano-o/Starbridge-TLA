------------------------------ MODULE Ethereum ------------------------------

EXTENDS Integers

CONSTANTS
    AccountId, \* the set of all account identifiers
    Amount,
    Hash,
    Time

Transaction == [from : AccountId, to : AccountId, amount : Amount, hash : Hash]

VARIABLES
    balance, \* a function mapping an account id to the account's balance
    mempool, \* pending transactions
    executed, \* executed transactions, per block
    usedHashes,
    time \* block time

\* balance is a private variables
\* mempool, executed, and usedHashes constitute the external interface of this module

Executed == UNION {executed[t] : t \in Time}

Init ==
    /\  balance \in [AccountId -> Amount]
    /\  mempool = {}
    /\  executed = [t \in Time |-> {}]
    /\  usedHashes = {}
    /\  time = 0

Tick ==
    /\  time' = time + 1
    /\  UNCHANGED <<balance, mempool, executed, usedHashes>>
    /\  time' \in Time

ReceiveTx(tx) ==
    /\  \neg tx.hash \in usedHashes
    /\  mempool' = mempool
          \union {tx}
    /\  usedHashes' = usedHashes \union {tx.hash}
    /\  UNCHANGED <<balance, executed, time>>

ExecuteTx == \E tx \in mempool :
    /\  tx.amount >= 0
    /\  tx.from # tx.to
    /\  tx.amount <= balance[tx.from]
    /\  balance' = [balance EXCEPT ![tx.from] = @-tx.amount, ![tx.to] = @+tx.amount]
    /\  mempool' = mempool \ {tx}
    /\  executed' = [executed EXCEPT ![time] = @ \union {tx}]
    /\  UNCHANGED <<usedHashes, time>>
    /\  balance'[tx.to] \in Amount \* for Apalache

TypeOkay ==
    /\  balance \in [AccountId -> Amount]
    /\  mempool \in SUBSET Transaction
    /\  executed \in [Time -> SUBSET Transaction]
    /\  usedHashes \in SUBSET Hash
    /\  time \in Time

Inv ==
  \A tx1 \in mempool \cup Executed :
    /\  tx1.hash \in usedHashes
    /\  \A tx2 \in mempool \cup Executed :
        tx1 = tx2 \/ tx1.hash # tx2.hash

=============================================================================
