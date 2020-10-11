
DIR=vrdt/src/
LIQUID=liquid --typeclass --ghc-option=-XBangPatterns --ghc-option=-XTypeFamilies --ghc-option=-XFlexibleContexts --ghc-option=-cpp -i $(DIR)

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
	$(LIQUID) vrdt/src/Event/Types.hs
	$(LIQUID) vrdt/src/VRDT/CausalTree.hs

