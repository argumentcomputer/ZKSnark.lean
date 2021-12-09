{
  description = "My Lean package";

  inputs = {
    lean = {
      url = github:leanprover/lean4;
    };
    nixpkgs.url = github:nixos/nixpkgs/nixos-21.05;
    utils = {
      url = github:yatima-inc/nix-utils;
      inputs.nixpkgs.follows = "nixpkgs";
    };
    # A lean dependency
    lean-ipld = {
      url = github:yatima-inc/lean-ipld;
      inputs.lean.follows = "lean";
    };
    lean-neptune = {
      url = github:yatima-inc/lean-neptune;
      inputs.lean.follows = "lean";
    };
  };

  outputs = { self, lean, utils, nixpkgs, lean-ipld, lean-neptune }:
    let
      supportedSystems = [
        # "aarch64-linux"
        # "aarch64-darwin"
        "i686-linux"
        "x86_64-darwin"
        "x86_64-linux"
      ];
      inherit (utils) lib;
    in
    lib.eachSystem supportedSystems (system:
      let
        leanPkgs = lean.packages.${system};
        pkgs = nixpkgs.legacyPackages.${system};
        name = "zkSNARK";  # must match the name of the top-level .lean file
        project = leanPkgs.buildLeanPackage {
          inherit name;
          deps = [ lean-ipld.project.${system} ];
          # Where the lean files are located
          src = ./src;
        };
        test = leanPkgs.buildLeanPackage {
          name = "Tests";
          deps = [ project ];
          # Where the lean files are located
          src = ./test;
        };
        joinDepsDerivationns = getSubDrv:
          pkgs.lib.concatStringsSep ":" (map (d: "${getSubDrv d}") ([ project ] ++ project.allExternalDeps));
      in
      {
        inherit project test;
        packages = {
          ${name} = project.executable;
        };

        checks.test = test.executable;

        defaultPackage = self.packages.${system}.${name};
        devShell = pkgs.mkShell {
          inputsFrom = [ project.executable ];
          buildInputs = with pkgs; [
            leanPkgs.lean
          ];
          LEAN_PATH = joinDepsDerivationns (d: d.modRoot);
          LEAN_SRC_PATH = joinDepsDerivationns (d: d.src);
        };
      });
}
