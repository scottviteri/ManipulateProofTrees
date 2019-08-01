with import <nixpkgs> {};
stdenv.mkDerivation rec {
  name = "env";
  env = buildEnv { name = name; paths = buildInputs; };
  buildInputs = [
    python37
    python37Packages.matplotlib
    python37Packages.networkx
    python37Packages.scipy
    coq_8_8
  ];
}
