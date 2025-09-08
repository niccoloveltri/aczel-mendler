{
  description = "Agda 2.6.2.2 + Cubical (overridden to known-good commit)";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-22.05"; # Agda 2.6.2.2
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
    let
      pkgs = import nixpkgs { inherit system; };

      # Override nixpkgs' cubical to the commit we know type-checks our code.
      cubicalPinned = pkgs.agdaPackages.cubical.overrideAttrs (_: {
        version = "git-dbe0176";
        src = pkgs.fetchFromGitHub {
          owner = "agda";
          repo  = "cubical";
          rev   = "dbe0176d3f873b2ec984720215e37c618c811d53";
          sha256 = "sha256-/rmVustRBKd7aeGxPr/wW2eRz2vvPlKcUmBHIgBY1gs=";
        };
      });

      # Wrap Agda so this cubical is registered (no messing with ~/.agda/libraries).
      agdaWith = pkgs.agda.withPackages (p: [
        cubicalPinned
      ]);
    in
    {
      devShells.default = pkgs.mkShell {
        buildInputs = [ agdaWith ];

        # Make Cubical the default library for ad-hoc files in this repo.
        shellHook = ''
          export AGDA_DIR="$PWD/.agda"
          mkdir -p "$AGDA_DIR"
          echo "cubical" > "$AGDA_DIR/defaults"
          export AGDA_DEFAULTS="$AGDA_DIR/defaults"
          echo "Agda $(agda --version | head -n1) ready with cubical @ dbe0176."
        '';
      };

      # (Optional) expose the wrapped Agda
      packages.agda = agdaWith;
    });
}
