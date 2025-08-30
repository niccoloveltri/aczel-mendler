{
  description = "Agda 2.6.2 + Cubical from nixpkgs, registered for use";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-22.05";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
    let
      pkgs = import nixpkgs { inherit system; };

      # Agda and its libraries come matched in pkgs.agdaPackages.*
      agda = pkgs.agda;                          # 2.6.2 on nixos-22.05
      cubical = pkgs.agdaPackages.cubical;       # Cubical library from nixpkgs
    in
    {
      devShells.default = pkgs.mkShell {
        buildInputs = [ agda ];

        AGDA_DIR = ".agda";

        shellHook = ''
          mkdir -p "$AGDA_DIR"

          # Point Agda to the Cubical library shipped by nixpkgs
          echo "${cubical}/cubical.agda-lib" > "$AGDA_DIR/libraries"

          # Make Cubical the default library so imports work without extra flags
          echo "cubical" > "$AGDA_DIR/defaults"

          echo "Agda $(agda --version | head -n1) ready."
          echo "Cubical library registered from: ${cubical}/cubical.agda-lib"
        '';
      };

      packages.agda = agda;
      packages.cubical = cubical;
    });
}
