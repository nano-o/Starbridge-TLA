# Starbridge

This repository contains formal models related to the
[Starbridge](https://github.com/stellar/starbridge) project.

[starbridge.ivy](https://github.com/nano-o/Starbridge/blob/main/ivy/shared/starbridge.ivy)
contains a model of the Ethereum to Stellar deposit flow (with refunds) and
a safety proof in the form of an inductive invariant. Check the proof with
`cd ivy; docker-compose run --rm starbridge-ivy`.

[starbridge-timelock.ivy](https://github.com/nano-o/Starbridge/blob/main/ivy/shared/starbridge-timelock.ivy)
contains a different model of the Ethereum to Stellar deposit flow based on an
idea of Tamir.
