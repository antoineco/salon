{
  description = "Salon";

  inputs = {
    nixpkgs.url = "https://flakehub.com/f/NixOS/nixpkgs/0.1"; # nixos-unstable
    rust-overlay.url = "https://flakehub.com/f/oxalica/rust-overlay/0.1";
    flake-schemas.url = "https://flakehub.com/f/DeterminateSystems/flake-schemas/0.1";
  };

  outputs =
    {
      nixpkgs,
      rust-overlay,
      flake-schemas,
      ...
    }:
    let
      allSystems = [
        "x86_64-linux"
        "aarch64-darwin"
      ];
      forAllSystems =
        f:
        nixpkgs.lib.genAttrs allSystems (
          system:
          f {
            pkgs = import nixpkgs {
              inherit system;
              overlays = [ rust-overlay.overlays.default ];
            };
          }
        );
    in
    {
      inherit (flake-schemas) schemas;

      formatter = forAllSystems ({ pkgs }: pkgs.nixfmt-tree);

      packages = forAllSystems (
        { pkgs }:
        {
          default = pkgs.rustPlatform.buildRustPackage (finalAttrs: {
            pname = "salon";
            version = "0.0.0";

            src = ./.;
            cargoLock = {
              lockFile = ./Cargo.lock;
            };

            meta = {
              description = "Simple appointment booking system for small businesses.";
              license = pkgs.lib.licenses.mit;
            };
          });
        }
      );

      devShells = forAllSystems (
        { pkgs }:
        {
          default =
            with pkgs;
            mkShell {
              packages =
                let
                  rust-nightly-custom = rust-bin.nightly.latest.default.override {
                    extensions = [
                      "rust-analyzer"
                      "rust-src"
                    ];
                  };
                in
                [
                  rust-nightly-custom
                  vscode-extensions.vadimcn.vscode-lldb.adapter
                  nixd
                  nixfmt-rfc-style
                ];
            };
        }
      );
    };
}
