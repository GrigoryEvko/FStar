{ fetchFromGitHub, z3 }:

z3.overrideAttrs (old: rec {
  version = "4.15.4";
  src = fetchFromGitHub {
    owner = "z3prover";
    repo = "z3";
    rev = "z3-${version}";
    sha256 = "sha256-eyF3ELv81xEgh9Km0Ehwos87e4VJ82cfsp53RCAtuTo=";
  };
})
