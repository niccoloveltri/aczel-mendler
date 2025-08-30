{
  description = "Agda 2.6.2 + Cubical from nixpkgs (registered via withPackages)";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-22.05";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
    let
      pkgs = import nixpkgs { inherit system; };

      # Wrap Agda so the Cubical lib is *registered* in the wrapper's library file.
      agda = pkgs.agda.withPackages (p: [ p.cubical ]);

      # For convenience, expose cubical too
      cubical = pkgs.agdaPackages.cubical;
    in
    {
      devShells.default = pkgs.mkShell {
        buildInputs = [ agda ];

        # Make Cubical the default library for ad-hoc files (no flags needed).
        shellHook = ''
          export AGDA_DIR="$PWD/.agda"
          mkdir -p "$AGDA_DIR"

          # Only set defaults; libraries are handled by the agda wrapper.
          echo "cubical" > "$AGDA_DIR/defaults"

          # Belt & suspenders: point Agda directly at the defaults file.
          export AGDA_DEFAULTS="$AGDA_DIR/defaults"

          echo "Agda $(agda --version | head -n1) ready."
          echo "Defaults -> $(cat "$AGDA_DIR/defaults")"
        '';
      };

      packages.agda = agda;
      packages.cubical = cubical;
    });
}
