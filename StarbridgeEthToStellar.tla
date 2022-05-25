------------------------------ MODULE StarbridgeEthToStellar ------------------------------

EXTENDS Integers

\* @typeAlias: STELLAR_TX = [from : STELLAR_ACCNT, to : STELLAR_ACCNT, amount : Int, seq : Int, maxTime : Int];
\* @typeAlias: ETH_TX = [from : ETH_ACCNT, to : ETH_ACCNT, amount : Int, hash : HASH];

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
    bridgeStellarLedgerTime,
    \* @type: STELLAR_ACCNT -> Int;
    bridgeStellarSeqNum,
    \* @type: Set(STELLAR_TX);
    bridgeStellarExecuted,
    \* @type: Int -> Set(ETH_TX);
    bridgeEthereumExecuted

ethereumVars == <<ethereumBalance, ethereumMempool, ethereumExecuted, ethereumUsedHashes, ethereumTime>>
stellarVars == <<stellarBalance, stellarSeqNum, stellarTime, stellarMempool, stellarExecuted>>
bridgeVars == <<bridgeHasLastTx, bridgeLastTx, bridgeStellarLedgerTime, bridgeStellarSeqNum, bridgeStellarExecuted, bridgeEthereumExecuted>>

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
    /\  bridgeStellarLedgerTime = 0
    /\  bridgeStellarSeqNum = [a \in StellarAccountId |-> 0]
    /\  bridgeStellarExecuted = {}
    /\  bridgeEthereumExecuted = [t \in Time |-> {}]
    /\  Stellar!Init /\ Ethereum!Init

TypeOkay ==
    /\  bridgeHasLastTx \in [Hash -> BOOLEAN]
    /\  bridgeLastTx \in [Hash -> Stellar!Transaction]
    /\  bridgeStellarLedgerTime \in Time
    /\  bridgeStellarSeqNum \in [StellarAccountId -> SeqNum]
    /\  bridgeStellarExecuted \in SUBSET Stellar!Transaction
    /\  bridgeEthereumExecuted \in [Time -> SUBSET Ethereum!Transaction]
    /\  Stellar!TypeOkay /\ Ethereum!TypeOkay

SyncWithStellar ==
    /\  bridgeStellarLedgerTime' = stellarTime
    /\  bridgeStellarSeqNum' = stellarSeqNum
    /\  bridgeStellarExecuted' = stellarExecuted
    /\  UNCHANGED <<ethereumVars, stellarVars, bridgeHasLastTx, bridgeLastTx, bridgeEthereumExecuted>>

SyncWithEthereum ==
    /\  bridgeEthereumExecuted' = ethereumExecuted
    /\  UNCHANGED <<ethereumVars, stellarVars, bridgeHasLastTx, bridgeLastTx, bridgeStellarExecuted, bridgeStellarSeqNum, bridgeStellarLedgerTime>>

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
              x \in Amount \ {0}, h \in Hash :
           LET tx == [from |-> src, to |-> BridgeEthereumAccountId, amount |-> x, hash |-> h]
           IN  Ethereum!ReceiveTx(tx)

Inv == Ethereum!Inv
Inv_ == TypeOkay /\ Inv
=============================================================================
