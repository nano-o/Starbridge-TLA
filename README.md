`StarbridgeEthToStellar.tla` contains a simple model of the Ethereum->Stellar deposit flow.
This model in written in TLA+.
The main property (`MainInvariant`) is that it's always true that more funds have been deposited in the bridge than have been taken out.
This has been checked with the Apalache model-checker.
