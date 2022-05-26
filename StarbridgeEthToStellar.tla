------------------------------ MODULE StarbridgeEthToStellar ------------------------------

EXTENDS Integers

\* @typeAlias: STELLAR_TX = [from : STELLAR_ACCNT, to : STELLAR_ACCNT, amount : Int, seq : Int, maxTime : Int];
\* @typeAlias: ETH_TX = [from : ETH_ACCNT, to : ETH_ACCNT, amount : Int, hash : HASH, memo : STELLAR_ACCNT];

StellarAccountId == {"1_OF_STELLAR_ACCNT","2_OF_STELLAR_ACCNT"}
EthereumAccountId == {"1_OF_ETH_ACCNT","2_OF_ETH_ACCNT"}
Amount == 0..1
SeqNum == 0..2
Time == 0..4
Hash == {"0_OF_HASH","1_OF_HASH"}

BridgeStellarAccountId == "1_OF_STELLAR_ACCNT"
BridgeEthereumAccountId == "1_OF_ETH_ACCNT"

VARIABLES
    \* state of Stellar and Ethereum:
    \* @type: STELLAR_ACCNT -> Int;
    stellarBalance,
    \* @type: STELLAR_ACCNT -> Int;
    stellarSeqNum,
    \* @type: Int;
    stellarTime,
    \* @type: Set(STELLAR_TX);
    stellarMempool,
    \* @type: Set(STELLAR_TX);
    stellarExecuted,
    \* @type: ETH_ACCNT -> Int;
    ethereumBalance,
    \* @type: Set(ETH_TX);
    ethereumMempool,
    \* @type: Int -> Set(ETH_TX);
    ethereumExecuted,
    \* @type: Set(HASH);
    ethereumUsedHashes,
    \* @type: Int;
    ethereumTime,

    \* state of the bridge:
    \* @type: HASH -> Bool;
    bridgeHasLastTx,
    \* @type: HASH -> STELLAR_TX;
    bridgeLastTx,
    \* @type: Int;
    bridgeStellarTime,
    \* @type: STELLAR_ACCNT -> Int;
    bridgeStellarSeqNum,
    \* @type: Set(STELLAR_TX);
    bridgeStellarExecuted,
    \* @type: Int -> Set(ETH_TX);
    bridgeEthereumExecuted

ethereumVars == <<ethereumBalance, ethereumMempool, ethereumExecuted, ethereumUsedHashes, ethereumTime>>
stellarVars == <<stellarBalance, stellarSeqNum, stellarTime, stellarMempool, stellarExecuted>>
bridgeVars == <<bridgeHasLastTx, bridgeLastTx, bridgeStellarTime, bridgeStellarSeqNum, bridgeStellarExecuted, bridgeEthereumExecuted>>

Stellar == INSTANCE Stellar WITH
    AccountId <- StellarAccountId,
    balance <- stellarBalance,
    seqNum <- stellarSeqNum,
    time <- stellarTime,
    mempool <- stellarMempool,
    executed <- stellarExecuted

Ethereum == INSTANCE Ethereum WITH
    AccountId <- EthereumAccountId,
    balance <- ethereumBalance,
    mempool <- ethereumMempool,
    executed <- ethereumExecuted,
    usedHashes <- ethereumUsedHashes,
    time <- ethereumTime

Init ==
    /\  bridgeHasLastTx = [h \in Hash |-> FALSE]
    /\  bridgeLastTx = [h \in Hash |-> CHOOSE tx \in Stellar!Transaction : TRUE]
    /\  bridgeStellarTime = 0
    /\  bridgeStellarSeqNum = [a \in StellarAccountId |-> 0]
    /\  bridgeStellarExecuted = {}
    /\  bridgeEthereumExecuted = [t \in Time |-> {}]
    /\  Stellar!Init /\ Ethereum!Init

TypeOkay ==
    /\  bridgeHasLastTx \in [Hash -> BOOLEAN]
    /\  bridgeLastTx \in [Hash -> Stellar!Transaction]
    /\  bridgeStellarTime \in Time
    /\  bridgeStellarSeqNum \in [StellarAccountId -> SeqNum]
    /\  bridgeStellarExecuted \in SUBSET Stellar!Transaction
    /\  bridgeEthereumExecuted \in [Time -> SUBSET Ethereum!Transaction]
    /\  Stellar!TypeOkay /\ Ethereum!TypeOkay

SyncWithStellar ==
    /\  bridgeStellarTime' = stellarTime
    /\  bridgeStellarSeqNum' = stellarSeqNum
    /\  bridgeStellarExecuted' = stellarExecuted
    /\  UNCHANGED <<ethereumVars, stellarVars, bridgeHasLastTx, bridgeLastTx, bridgeEthereumExecuted>>

SyncWithEthereum ==
    /\  bridgeEthereumExecuted' = ethereumExecuted
    /\  UNCHANGED <<ethereumVars, stellarVars, bridgeHasLastTx, bridgeLastTx, bridgeStellarExecuted, bridgeStellarSeqNum, bridgeStellarTime>>

\* A withdraw transaction is irrevocably invalid when its time bound has ellapsed or the sequence number of the receiving account is higher than the transaction's sequence number
\* @type: (STELLAR_TX) => Bool;
IrrevocablyInvalid(tx) ==
  \/  tx.maxTime < bridgeStellarTime
  \/  tx.seq < bridgeStellarSeqNum[tx.from]

BridgeEthereumExecuted == UNION {bridgeEthereumExecuted[t] : t \in Time}

\* timestamp of a transaction on Ethereum as seen by the bridge
TxTime(tx) == CHOOSE t \in Time : tx \in bridgeEthereumExecuted[t]

\* The bridge signs a new withdraw transaction when:
\* It never did so before for the same hash,
\* or the previous withdraw transaction is irrevocably invalid.
\* The transaction has a time bound set to N ahead of the current time (for some fixed N).
\* But what is the current time?
\* Initially it can be the time of the tx as recorded on ethereum, but what is it afterwards?
\* For now, we use previousTx.maxTime+N
SignWithdrawTransaction == \E tx \in BridgeEthereumExecuted :
  /\  \/  \neg bridgeHasLastTx[tx.hash]
      \/  IrrevocablyInvalid(bridgeLastTx[tx.hash])
  /\ \E seqNum \in SeqNum  : \* chosen by the client
      LET timeBound ==
            IF \neg bridgeHasLastTx[tx.hash]
              THEN TxTime(tx)
              ELSE bridgeLastTx[tx.hash].time+1 \* here N = 1
          (* withdrawTx == *)
            (* [from |-> BridgeStellarAccountId,  *)
      IN
        TRUE

Next ==
    \/  SyncWithStellar
    \/  SyncWithEthereum
    \/
      \* internal stellar transitions:
      /\ UNCHANGED <<ethereumVars, bridgeVars>>
      /\
           \/  Stellar!Tick
           \/  Stellar!ExecuteTx
    \/
      \* internal ethereum transitions:
      /\ UNCHANGED <<stellarVars, bridgeVars>>
      /\ \/ Ethereum!ExecuteTx
         \/ Ethereum!Tick
    \/
      \* a client initiates a transfer on Ethereum:
      /\ UNCHANGED <<stellarVars, bridgeVars>>
      /\ \E src \in EthereumAccountId \ {BridgeEthereumAccountId},
              x \in Amount \ {0}, h \in Hash, dst \in StellarAccountId \ {BridgeStellarAccountId} :
           LET tx == [from |-> src, to |-> BridgeEthereumAccountId, amount |-> x, hash |-> h, memo |-> dst]
           IN  Ethereum!ReceiveTx(tx)

Inv == Ethereum!Inv
Inv_ == TypeOkay /\ Inv
=============================================================================
