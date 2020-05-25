
DIR=vrdt/src/
LIQUID=liquid --typeclass --ghc-option=-XTypeFamilies --ghc-option=-XFlexibleContexts --ghc-option=-cpp -i $(DIR)

verify:
	$(LIQUID) vrdt/src/Liquid/ProofCombinators.hs
	$(LIQUID) vrdt/src/Liquid/Data/Maybe.hs
	$(LIQUID) vrdt/src/Liquid/Data/Map.hs
	$(LIQUID) vrdt/src/VRDT/Class.hs
	$(LIQUID) vrdt/src/VRDT/Class/Proof.hs
	$(LIQUID) vrdt/src/VRDT/LWW.hs

	$(LIQUID) vrdt/src/VRDT/TwoPMap/Internal.hs
	$(LIQUID) vrdt/src/VRDT/TwoPMap/LemmaID.hs
	$(LIQUID) vrdt/src/VRDT/TwoPMap/LemmaDD.hs
	$(LIQUID) vrdt/src/VRDT/TwoPMap/LemmaAD.hs
	$(LIQUID) vrdt/src/VRDT/TwoPMap/LemmaDA.hs
	$(LIQUID) vrdt/src/VRDT/TwoPMap/LemmaDI.hs
	$(LIQUID) vrdt/src/VRDT/TwoPMap/LemmaII.hs
	$(LIQUID) vrdt/src/VRDT/TwoPMap/LemmaAA.hs
	$(LIQUID) vrdt/src/VRDT/TwoPMap/LemmaIA.hs
	$(LIQUID) vrdt/src/VRDT/TwoPMap/LemmaAI.hs
	$(LIQUID) vrdt/src/VRDT/TwoPMap.hs
	$(LIQUID) vrdt/src/VRDT/MultiSet/Internal.hs
	$(LIQUID) vrdt/src/VRDT/MultiSet.hs
	$(LIQUID) vrdt/src/VRDT/MultiSet/Proof.hs

# 39d5b54f43e9c62ce5e9aae592a6a15ca17b62d6 not working
