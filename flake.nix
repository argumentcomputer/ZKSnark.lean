{
  description = "Zero Knowledge SNARKs in Lean";

  inputs = {
    lean = {
      url = github:leanprover/lean4;
    };
    nixpkgs.url = github:nixos/nixpkgs/nixos-21.11;
    flake-utils = {
      url = github:numtide/flake-utils;
      inputs.nixpkgs.follows = "nixpkgs";
    };
    blst = {
      url = github:yatima-inc/blst/acs/flake;
      inputs.nixpkgs.follows = "nixpkgs";
    };
    # A lean dependency
    lean-ipld = {
      url = github:yatima-inc/lean-ipld;
      inputs.lean.follows = "lean";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    lean-neptune = {
      url = github:yatima-inc/lean-neptune;
      inputs.lean.follows = "lean";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs = { self, lean, flake-utils, nixpkgs, blst, lean-ipld, lean-neptune }:
    let
      supportedSystems = [
        "aarch64-linux"
        "aarch64-darwin"
        "i686-linux"
        "x86_64-darwin"
        "x86_64-linux"
      ];
    in
    flake-utils.lib.eachSystem supportedSystems (system:
      let
        leanPkgs = lean.packages.${system};
        libblst = blst.packages.${system}.blst // {
          libName = "libblst.a";
        };
        pkgs = nixpkgs.legacyPackages.${system};
        lib = nixpkgs.lib // (import ./nix/lib.nix { inherit (nixpkgs) lib; });
        inherit (lib) concatStringsSep;
        buildCLib = import ./nix/buildCLib.nix { inherit nixpkgs system lib; };
        hasPrefix =
          # Prefix to check for
          prefix:
          # Input string
          content:
          let
            lenPrefix = builtins.stringLength prefix;
          in
          prefix == builtins.substring 0 lenPrefix content;
        includes = [
          "${blst}/bindings"
          "${leanPkgs.lean-bin-tools-unwrapped}/include"
        ];
        INCLUDE_PATH = concatStringsSep ":" includes;
        c-shim = buildCLib {
          updateCCOptions = d: d ++ (map (i: "-I${i}") includes);
          name = "lean-blst-bindings";
          sourceFiles = [ "bindings/*.c" ];
          staticLibDeps = [ libblst ];
          src = builtins.filterSource
            (path: type: hasPrefix (toString ./. + "/bindings") path) ./.;
          extraDrvArgs = {
            linkName = "lean-blst-bindings";
          };
        };
        c-shim-debug = c-shim.override {
          debug = true;
          updateCCOptions = d: d ++ (map (i: "-I${i}") includes) ++ [ "-O0" ];
        };
        name = "ZKSnark";  # must match the name of the top-level .lean file
        BLST = leanPkgs.buildLeanPackage {
          name = "BLST";
          src = ./src;
          nativeSharedLibs = [ c-shim ];
        };
        project = leanPkgs.buildLeanPackage {
          inherit name;
          deps = [
            BLST
            # lean-ipld.project.${system}
          ];
          # Where the lean files are located
          src = ./src;
        };
        cli = leanPkgs.buildLeanPackage {
          name = "ZKSnark.Cli";
          deps = [ project ];
          executableName = "zksnark";
          src = ./src;
        };
        test = leanPkgs.buildLeanPackage {
          name = "Tests";
          deps = [ project ];
          # Where the lean files are located
          src = ./test;
        };
        joinDepsDerivations = getSubDrv:
          pkgs.lib.concatStringsSep ":" (map (d: "${getSubDrv d}") project.allExternalDeps);
        withGdb = bin: pkgs.writeShellScriptBin "${bin.name}-with-gdb" "${pkgs.gdb}/bin/gdb ${bin}/bin/${bin.name}";
      in
      {
        inherit project test BLST;
        packages = {
          inherit c-shim;
          BLST = BLST.sharedLib;
          ${name} = project.sharedLib;
          "${name}-cli" = cli.executable;
          test = test.executable;
          debug-test = (test.overrideArgs {
            debug = true;
            deps =
            [ (project.override {
                deps = [
                  (BLST.overrideArgs {
                    debug = true;
                    nativeSharedLibs = [ c-shim-debug ];
                  })
                ];
              })
            ];
          }).executable // { allowSubstitutes = false; };
          gdb-test = withGdb self.packages.${system}.debug-test;
        };

        defaultPackage = self.packages.${system}."${name}-cli";
        devShell = pkgs.mkShell {
          inputsFrom = [ project.executable ];
          buildInputs = with pkgs; [
            leanPkgs.lean-dev
          ];
          LEAN_PATH = "./src:./test";
          LEAN_SRC_PATH = "./src:./test";
          C_INCLUDE_PATH = INCLUDE_PATH;
          CPLUS_INCLUDE_PATH = INCLUDE_PATH;
        };
      });
}
