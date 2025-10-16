{
  description = "agda-cardano-common";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs";

    flake-utils.url = "github:numtide/flake-utils";

    agda-nix = {
      url = "github:input-output-hk/agda.nix";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs =
    inputs@{
      self,
      nixpkgs,
      flake-utils,
      ...
    }:
    let
      systems = [
        "x86_64-linux"
        "aarch64-darwin"
      ];
      overlay = nixpkgs.lib.composeManyExtensions [
        inputs.agda-nix.overlays.default
        (final: prev: {
          agdaPackages = prev.agdaPackages.overrideScope (
            afinal: aprev: {
              cardano-common = afinal.callPackage ./nix/cardano-common.nix { };
            }
          );
        })
      ];
    in
    flake-utils.lib.eachSystem systems (
      system:
      let
        pkgs = import nixpkgs {
          inherit system;
          overlays = [
            inputs.agda-nix.overlays.shellFor
            overlay
          ];
        };
      in
      {
        packages.default = pkgs.agdaPackages.cardano-common;
        devShells.default = pkgs.agda.shellFor pkgs.agdaPackages.cardano-common;
        hydraJobs =
          let
            jobs = { inherit (self) packages devShells; };
          in
          jobs
          // {
            required = pkgs.releaseTools.aggregate {
              name = "${system}-required";
              constituents = with nixpkgs.lib; collect isDerivation jobs;
            };
          };
      }
    )
    // {
      overlays.default = overlay;
    };
}
