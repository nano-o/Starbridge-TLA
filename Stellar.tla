------------------------------ MODULE Stellar ------------------------------

EXTENDS Integers

CONSTANTS
    AccountId, \* the set of all account identifiers
    Amount,
    SeqNum,
    Time,
    BridgeAccountId,
    Hash

Transaction == [src : AccountId, from : AccountId, to : AccountId, amount : Amount, seq : SeqNum, maxTime : Time, memo : Hash]
\* memo contains the hash of the initiating transaction on Ethereum

VARIABLES
    seqNum, \* a function mapping an account id to the account's sequence number
    time, \* last ledger close time
    mempool, \* pending mempool; that's the interface to the outer world
    executed \* executed transactions

\* balance is a private variable
\* mempool, executed, time, and seqNum are interface variables

Init ==
    /\  seqNum \in [AccountId -> SeqNum]
    /\  time = 0
    /\  mempool = {}
    /\  executed = {}

Tick  ==
    /\  time' = time + 1
    /\  UNCHANGED <<seqNum, mempool, executed>>
    /\  time' \in Time

ReceiveTx(tx) ==
    /\  mempool' = mempool \union {tx}
    /\  UNCHANGED <<time, seqNum, executed>>

ExecuteTx == \E tx \in mempool :
    /\  tx.seq = seqNum[tx.src]
    /\  time <= tx.maxTime
    /\  tx.amount >= 0
    /\  seqNum' = [seqNum EXCEPT ![tx.src] = @+1]
    /\  mempool' = mempool \ {tx}
    /\  executed' = executed \union {tx}
    /\  UNCHANGED time
    /\  seqNum'[tx.src] \in SeqNum

TypeOkay ==
    /\  seqNum \in [AccountId -> SeqNum]
    /\  time \in Time
    /\  time >= 0
    /\  mempool \in SUBSET Transaction
    /\  executed \in SUBSET Transaction

=============================================================================
