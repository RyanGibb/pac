{
  description = "apt, apk, opam, cargo and npm at the versions eval/'s baselines were recorded with";

  # Two revisions because neither carries every recorded version: nixos-26.05
  # has apt 3.3.0 but opam 2.5.1 and Rust 1.95, nixos-unstable has opam 2.5.2
  # and Rust 1.97.1 but apt 3.3.3.
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/5dfba6236110080a54247d6460bc2ff5dda939cc";
    nixpkgs-unstable.url = "github:NixOS/nixpkgs/34ab99075ac4f7e40cf037eef32cb1c360bb85e9";
  };

  outputs = { self, nixpkgs, nixpkgs-unstable }:
    let
      system = "x86_64-linux";
      pkgs = nixpkgs.legacyPackages.${system};
      unstable = nixpkgs-unstable.legacyPackages.${system};
      tools = {
        inherit (pkgs) apt apk-tools nodejs jq python3 curl;
        inherit (unstable) opam cargo rustc;
      };
    in {
      packages.${system} = tools;

      devShells.${system}.default = pkgs.mkShellNoCC {
        packages = builtins.attrValues tools;
        # cargo resolves a goal that declares no rust-version for the rustc
        # it would build with, so nothing inherited may point it at another
        # toolchain; CARGO_CMP_OUT is the harness's own, not cargo's.
        shellHook = ''
          for v in $(compgen -e); do
            case $v in
              CARGO_CMP_OUT) ;;
              CARGO_*|RUSTUP_*|RUSTC|RUSTC_*|RUSTFLAGS|RUSTDOCFLAGS) unset "$v" ;;
            esac
          done
          export RUSTC=${tools.rustc}/bin/rustc
          export APT=${tools.apt}/bin/apt-get
          export APK=${tools.apk-tools}/bin/apk
        '';
      };
    };
}
