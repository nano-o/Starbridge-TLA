# Starbridge

This repository contains formal models related to the Starbridge project.

Notably,
[starbridge.ivy](https://github.com/nano-o/Starbridge/blob/main/ivy/shared/starbridge.ivy)
contains a model of the Ethereum to Stellar deposit flow (with refunds) and
a safety proof in the form of an inductive invariant. Check the proof with
`cd ivy; docker-compose build starbridge-ivy; docker-compose run --rm starbridge-ivy`.
