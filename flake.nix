{
  description = "Agda 2.8.0 + Cubical 0.9";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-26.05"; # Agda 2.8.0 and Cubical 0.9
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
    let
      pkgs = import nixpkgs { inherit system; };

      agdaWithCubical = pkgs.agda.withPackages (p: [
        p.cubical
      ]);
    in
    {
      devShells.default = pkgs.mkShell {
        buildInputs = [ agdaWithCubical ];

        # Make Cubical a default library.
        shellHook = ''
          export AGDA_DIR="$PWD/.agda"
          mkdir -p "$AGDA_DIR"
          echo "cubical" > "$AGDA_DIR/defaults"
          export AGDA_DEFAULTS="$AGDA_DIR/defaults"
          echo "Agda $(agda --version | head -n1) ready with cubical 0.9"
        '';
      };

      packages.agda = agdaWithCubical;
    });
}
