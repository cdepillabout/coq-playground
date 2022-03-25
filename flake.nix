{
  description = "Coq Playground";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-21.11";
  inputs.flake-utils.url = "github:numtide/flake-utils";

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        overlay = self: _: {
          software-foundations-shell = self.stdenv.mkDerivation {
            name = "coq-playground-shell";
            dontUnpack = true;
            nativeBuildInputs = [
              self.coq_8_13
              self.mustache-go # for regenerating files from meta.yml
            ];
            installPhase = "touch $out";
          };
        };
        pkgs = import nixpkgs {
          inherit system;
          overlays = [
            overlay
          ];
        };
      in
      {
        devShell = pkgs.software-foundations-shell;
      }
    );
}

