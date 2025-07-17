(lang dune 3.8)
(using coq 0.7)
(name coq-sims)

(license "LGPLv3")
(authors "Nicolas Chappe")
(maintainers "Nicolas Chappe")

(generate_opam_files true)

(package
 (name coq-sims)
 (version 0.1)
 (depends
  (coq (>= 8.19.1))
  (coq-coinduction (>= 1.9))
  (coq-relation-algebra (>= 1.7))
  (coq-ctree (>= 0.1)))
)
