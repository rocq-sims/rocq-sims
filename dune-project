(lang dune 3.8)
(using coq 0.7)
(name coq-sims)

(license "LGPL-3.0-or-later")
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
  (coq-ctree (>= 2.0)))
 (tags (
   "category:CS/Semantics and Compilation/Semantics"
   "category:CS/Semantics and Compilation/Compilation"
   "keyword:simulation"
   "keyword:coinduction up-to"
   "logpath:Sims"
)))

(package
 (name coq-sims-examples)
 (version 0.1)
 (depends
  (coq-sims (= 0.1)))
 (tags (
   "category:CS/Semantics and Compilation/Semantics"
   "category:CS/Semantics and Compilation/Compilation"
   "keyword:simulation"
   "keyword:coinduction up-to"
   "logpath:SimsExamples"
)))
