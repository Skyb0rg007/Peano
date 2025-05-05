{
  inputs.flake-utils.url = "github:numtide/flake-utils";
  outputs = {
    self,
    nixpkgs,
    flake-utils,
  }:
    flake-utils.lib.eachDefaultSystem (system: let
      pkgs = nixpkgs.legacyPackages.${system};
    in {
      devShells.default = pkgs.mkShellNoCC {
        buildInputs = [pkgs.coq pkgs.coqPackages.stdlib];
        shellHook = "unset COQPATH"; # messes with Coqtail
      };
      formatter = pkgs.alejandra;
    });
}
