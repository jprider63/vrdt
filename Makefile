
DIR=vrdt/src/
LIQUID=liquid --ghc-option=-XTypeFamilies --ghc-option=-cpp -i $(DIR)

verify:
	$(LIQUID) vrdt/src/VRDT/Class.hs
	$(LIQUID) vrdt/src/VRDT/LWW.hs
	$(LIQUID) vrdt/src/VRDT/MultiSet.hs
	$(LIQUID) vrdt/src/VRDT/MultiSet/Proof.hs
