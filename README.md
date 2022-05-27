Examples of checks that use a lot of memory and do not seem to terminate:

`apalache-mc check --inv=MainInvariant --init=MainInvariant_ --length=0 StarbridgeEthToStellar.tla`

Terminates but is slow (370 seconds on my laptop):

`apalache-docker check --inv=Inv3 --init=Inv3_  --length=1 StarbridgeEthToStellar.tla`
