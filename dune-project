(lang dune 3.8)
(using coq 0.7)
(name coq-optsim)

(license "LGPLv3")
(authors "Nicolas Chappe")
(maintainers "Nicolas Chappe")

(generate_opam_files true)

(package
 (name coq-optsim)
 (version 0.1)
 (depends
  (coq (= 8.19.1))
  (coq-ext-lib (>= 0.11.3))
  (coq-coinduction (= 1.9))
  (coq-relation-algebra (>= 1.7))
  (coq-itree (>= 5.0)))
)
