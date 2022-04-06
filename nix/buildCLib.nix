# A very simple setup to compile C and C++ code
{ nixpkgs, system, lib }:
with builtins;
let
  pkgs = nixpkgs.legacyPackages.${system};
  inherit (pkgs) stdenv;
  joinArgs = lib.concatStringsSep " ";
  pathOfLib = dep: dep.libPath or "${dep}/${dep.libName or dep.name}";
  protoBuildCLib = lib.makeOverridable
    ({ name
     , src
     , static ? false
     , libExtension ? if static then "a" else "so"
     , libName ? "lib${name}.${libExtension}"
     , cc ? stdenv.cc
       # A function that 
     , updateCCOptions ? a: a
     , sourceFiles ? [ "*.c" ]
     , debug ? false
     , extraDrvArgs ? {}
     # Static libraries that wil be included in the resulting lib
     , staticLibDeps ? []
     # Shared libraries to link to
     , sharedLibDeps ? []
     }:
      let
        defaultOptions = [ "-Wall" "-pedantic" "-O3" (if debug then "-ggdb" else "") ];
        commonCCOptions = updateCCOptions defaultOptions;
        libs = map (drv: "${drv}/lib/${drv.libName}") staticLibDeps;
        linkerOpts = map (drv: "-L${drv}") sharedLibDeps;
        objectFiles = [ "*.o" ];
        buildSteps =
          if static then
            [
              "${cc}/bin/cc ${joinArgs commonCCOptions} -c ${joinArgs sourceFiles}"
              "ar rcs ${libName} ${joinArgs objectFiles}"

            ] else
            [
              "${cc}/bin/cc ${joinArgs commonCCOptions} -c ${joinArgs sourceFiles}"
              "${cc}/bin/cc ${joinArgs commonCCOptions} -shared -Wl,--whole-archive ${joinArgs libs} ${joinArgs objectFiles} -Wl,--no-whole-archive ${joinArgs linkerOpts} -o ${libName}"
            ];
      in
      stdenv.mkDerivation ({
        inherit src system;
        name = libName;
        buildInputs = with pkgs; [ cc clib ] ++ staticLibDeps;
        NIX_DEBUG = 1;
        buildPhase = lib.concatStringsSep "\n" buildSteps;
        installPhase = ''
          mkdir -p $out
          cp ${libName} $out
        '';
      } // extraDrvArgs));

  # type: {a = b;} -> (a -> b -> c) -> [c]
  forEachRow = attrset: f: lib.zipListsWith f (attrNames attrset) (attrValues attrset);
  forEachRowJoin = attrset: f: lib.foldl (acc: c: acc // c) { } (forEachRow attrset f);
  # Extend an overridable function with the given overrideArgs.
  extendOverridableFn = (f: overrideArgs: args:
    let
      self = f args;
      newProps = forEachRowJoin overrideArgs (name: attrs: { ${name} = self.override attrs; });
    in
    self // newProps
  );
  # Property extensions. Each generation inherits the properties of the last.
  propertyGenerations = [
    {
      debug = { debug = true; };
    }
    {
      staticLib = {
        static = true;
      };
      sharedLib = {
        static = false;
      };
    }
  ];

  # Add additional properties in sequence
  buildCLib = lib.foldl extendOverridableFn protoBuildCLib propertyGenerations;
in
buildCLib
