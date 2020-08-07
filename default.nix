{ config ? { allowBroken = true; }, ... }:
let
  # fetch pinned version of nixpkgs
  nixpkgs = import (
    builtins.fetchTarball {
      url = "https://github.com/NixOS/nixpkgs-channels/archive/1a92d0abfcdbafc5c6e2fdc24abf2cc5e011ad5a.tar.gz";
      sha256 = "1f9ypp9q7r5p1bzm119yfg202fbm83csmlzwv33p1kf76m2p7mwd";
    }
  ) { inherit config; };
  # override haskell compiler version, add and override dependencies in nixpkgs
  haskellPackages = nixpkgs.haskellPackages.override (
    old: {
      overrides = self: super: with nixpkgs.haskell.lib; {
        # add dependencies not on hackage
        kyowon-client = self.callCabal2nix "kyowon-client" ./kyowon-client {};
        kyowon-core = self.callCabal2nix "kyowon-core" ./kyowon-core {};
        kyowon-reflex =
          dontCheck # the tests are missing language-extensions
            (
              dontHaddock # a commented application operator is a haddock parse error
                (
                  self.callCabal2nix "kyowon-reflex" ./kyowon-reflex {}
                )
            );
        vrdt =
          dontCheck # Spec.hs isn't checked into the repo
            (
              dontHaddock # commented guard case is a haddock parse error 
                (
                  self.callCabal2nix "vrdt" ./vrdt {}
                )
            );
        # fix dependency versions
        patch = self.callHackage "patch" "0.0.2.0" {}; # version used in stack.yaml
        dependent-map = self.callHackage "dependent-map" "0.3" {}; # version used in stack.yaml
        dependent-sum = self.callHackage "dependent-sum" "0.6.2.0" {}; # version used in stack.yaml
        witherable = self.callHackage "witherable" "0.3.1" {}; # version used in stack.yaml
        monoidal-containers = self.callHackage "monoidal-containers" "0.6.0.1" {}; # version used in stack.yaml
        bimap = self.callHackage "bimap" "0.3.3" {}; # version used in stack.yaml
      };
    }
  );
  # function to bring devtools in to a package environment
  devtools = old: { nativeBuildInputs = old.nativeBuildInputs ++ [ nixpkgs.cabal-install nixpkgs.ghcid ]; }; # ghc and hpack are automatically included
  # use overridden-haskellPackages to call source
  drv = haskellPackages.callCabal2nix "collaborate" ./examples/collaborate {};
in
if nixpkgs.lib.inNixShell then (drv.envFunc { hoogle = true; }).overrideAttrs devtools else drv
