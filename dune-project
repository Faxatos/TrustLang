(lang dune 3.14)

(name trustlang)

(generate_opam_files true)

(source
 (github Faxatos/TrustLang))

(authors "Faxatos")

(license LICENSE)

(documentation https://url/to/documentation)

(package
 (name trustlang)
 (synopsis "Assignments for the Language Based Technology for Security UniPi course")
 (description "A secure functional programming language in OCaml that manages trusted vs untrusted code execution")
 (depends ocaml dune)
 (tags
  (topics "to describe" your project)))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/dune-files.html#dune-project
