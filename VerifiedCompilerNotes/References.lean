import VersoManual

open Verso.Genre.Manual

namespace VerifiedCompilerNotes

def reynoldsDefinitionalInterpreters : InProceedings where
  title := inlines!"Definitional Interpreters for Higher-Order Programming Languages"
  authors := #[inlines!"John C. Reynolds"]
  year := 1972
  booktitle := inlines!"Proceedings of the ACM Annual Conference"
  url := some "https://surface.syr.edu/lcsmith_other/13/"

def kahnNaturalSemantics : InProceedings where
  title := inlines!"Natural Semantics"
  authors := #[inlines!"Gilles Kahn"]
  year := 1987
  booktitle := inlines!"Annual Symposium on Theoretical Aspects of Computer Science"
  url := some "https://link.springer.com/chapter/10.1007/BFb0039592"

def plotkinSOS : Article where
  title := inlines!"A Structural Approach to Operational Semantics"
  authors := #[inlines!"Gordon D. Plotkin"]
  journal := inlines!"Journal of Logic and Algebraic Programming"
  year := 2004
  month := none
  volume := inlines!"60-61"
  number := inlines!""
  pages := some (17, 139)
  url := some "https://homepages.inf.ed.ac.uk/gdp/publications/sos_jlap.pdf"

def landinMechanicalEvaluation : Article where
  title := inlines!"The Mechanical Evaluation of Expressions"
  authors := #[inlines!"P. J. Landin"]
  journal := inlines!"The Computer Journal"
  year := 1964
  month := none
  volume := inlines!"6"
  number := inlines!"4"
  pages := some (308, 320)
  url := some "https://www.cs.cmu.edu/~crary/819-f09/Landin64.pdf"

def plotkinOriginsSOS : Article where
  title := inlines!"The Origins of Structural Operational Semantics"
  authors := #[inlines!"Gordon D. Plotkin"]
  journal := inlines!"Journal of Logic and Algebraic Programming"
  year := 2004
  month := none
  volume := inlines!"60-61"
  number := inlines!""
  pages := some (3, 15)
  url := some "https://homepages.inf.ed.ac.uk/gdp/publications/Origins_SOS.pdf"

def mccarthyMathematicalScience : InProceedings where
  title := inlines!"Towards a Mathematical Science of Computation"
  authors := #[inlines!"John McCarthy"]
  year := 1962
  booktitle := inlines!"Information Processing"
  url := some "https://www-formal.stanford.edu/jmc/towards.pdf"

def smullyanFirstOrderLogic : Article where
  title := inlines!"First-Order Logic"
  authors := #[inlines!"Raymond M. Smullyan"]
  journal := inlines!"Ergebnisse der Mathematik und ihrer Grenzgebiete"
  year := 1968
  month := none
  volume := inlines!"43"
  number := inlines!""
  pages := none
  url := some "https://link.springer.com/book/10.1007/978-3-642-86718-7"

def barendregtThesis : Thesis where
  title := inlines!"Some Extensional Term Models for Combinatory Logics and Lambda-Calculi"
  author := inlines!"H. P. Barendregt"
  year := 1971
  university := inlines!"Rijksuniversiteit te Utrecht"
  degree := inlines!"PhD thesis"
  url := some "https://www.illc.uva.nl/Research/Publications/Dissertations/HDS/HDS-37.text.html"

def felleisenHiebRevisedReport : Article where
  title := inlines!"The Revised Report on the Syntactic Theories of Sequential Control and State"
  authors := #[inlines!"Matthias Felleisen", inlines!"Robert Hieb"]
  journal := inlines!"Theoretical Computer Science"
  year := 1992
  month := none
  volume := inlines!"103"
  number := inlines!"2"
  pages := some (235, 271)
  url := some "https://plv.mpi-sws.org/plerg/papers/felleisen-hieb-92-2up.pdf"

def huttonSemantics123 : Article where
  title := inlines!"Programming Language Semantics: It’s Easy as 1,2,3"
  authors := #[inlines!"Graham Hutton", inlines!"Nicolas Wu"]
  journal := inlines!"Journal of Functional Programming"
  year := 2022
  month := none
  volume := inlines!"32"
  number := inlines!""
  pages := none
  url := some "https://www.cambridge.org/core/journals/journal-of-functional-programming/article/programming-language-semantics-its-easy-as-123/EC2C046CF94382B3B408036B84475DC7"

def taitIntensionalInterpretations : Article where
  title := inlines!"Intensional Interpretations of Functionals of Finite Type I"
  authors := #[inlines!"W. W. Tait"]
  journal := inlines!"The Journal of Symbolic Logic"
  year := 1967
  month := none
  volume := inlines!"32"
  number := inlines!"2"
  pages := some (198, 212)
  url := some "https://www.cambridge.org/core/journals/journal-of-symbolic-logic/article/intensional-interpretations-of-functionals-of-finite-type-i/9F30EA199783BD797DF6FA44525F114E"

def timanyLogicalTypeSoundness : Article where
  title := inlines!"A Logical Approach to Type Soundness"
  authors := #[
    inlines!"Amin Timany",
    inlines!"Robbert Krebbers",
    inlines!"Derek Dreyer",
    inlines!"Lars Birkedal"
  ]
  journal := inlines!"Journal of the ACM"
  year := 2024
  month := none
  volume := inlines!"71"
  number := inlines!"6"
  pages := none
  url := some "https://doi.org/10.1145/3676954"

end VerifiedCompilerNotes
