{ config ? { allowBroken = true; }, ... }:
let
  # fetch pinned version of nixpkgs
  nixpkgs = import (
    builtins.fetchTarball {
      url = "https://github.com/NixOS/nixpkgs-channels/archive/1a92d0abfcdbafc5c6e2fdc24abf2cc5e011ad5a.tar.gz";
      sha256 = "1f9ypp9q7r5p1bzm119yfg202fbm83csmlzwv33p1kf76m2p7mwd";
    }
  ) { inherit config; };
  # function to respect gitignore files
  ign = src: nixpkgs.nix-gitignore.gitignoreSource [] src;
  # override haskell compiler version, add and override dependencies in nixpkgs
  haskellPackages = nixpkgs.haskellPackages.override (
    old: {
      overrides = self: super: with nixpkgs.haskell.lib; {

        # add dependencies not on hackage
        kyowon-client = self.callCabal2nix "kyowon-client" (ign ./kyowon-client) {};
        kyowon-core = self.callCabal2nix "kyowon-core" (ign ./kyowon-core) {};
        kyowon-reflex =
          # the tests are missing language-extensions
          dontCheck (
            # a commented application operator is a haddock parse error
            dontHaddock (
              self.callCabal2nix "kyowon-reflex" (ign ./kyowon-reflex) {}
            )
          );
        vrdt =
          # Spec.hs isn't checked into the repo
          dontCheck (
            # commented guard case is a haddock parse error
            dontHaddock (
              self.callCabal2nix "vrdt" ./vrdt {}
            )
          );

        # add executables also
        kyowon-server = haskellPackages.callCabal2nix "kyowon-server" (ign ./kyowon-server) {};
        example-collaborate = haskellPackages.callCabal2nix "collaborate" ./examples/collaborate {};
        example-max =
          # Spec.hs isn't checked into the repo
          dontCheck (
            haskellPackages.callCabal2nix "max" ./examples/max {}
          );
        # has a bug in the cabalfile
        example-event = haskellPackages.callCabal2nix "event" ./examples/event {};

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
  # specify the packages that we'll want to develop or build
  packages = pkg: [
    pkg.example-collaborate
    #pkg.example-event
    pkg.example-max
    pkg.kyowon-client
    pkg.kyowon-core
    pkg.kyowon-reflex
    pkg.kyowon-server
    pkg.vrdt
  ];
in
if nixpkgs.lib.inNixShell
then nixpkgs.stdenv.mkDerivation {
  name = "stub";
  buildInputs = [
    (haskellPackages.ghcWithPackages packages)
    haskellPackages.hpack
    nixpkgs.cabal-install
    nixpkgs.ghcid
  ];
}
else nixpkgs.buildEnv {
  name = "vrdt-project";
  paths = packages haskellPackages;
}
