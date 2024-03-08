# MMVA_of_HashTrie
We present an efficiency-optimized functional HashTrie algorithm and mechanically validate it.

HashTrie.thy contains the functional modeling and mechanical verification of the algorithm;

HashTrie_TM.thy contains the temporal model and verification of the related time complexity;

Multi_Pattern_Matching.thy contains the implementation of the Multi Pattern Matching algorithm as an application example. It also includes algorithmic threading based on the correlation between pattern strings to eliminate backtracking issues during matching.

Test.thy contains experimental comparisons of the time consumption of several multiple pattern matching algorithms implemented in Multi_Pattern_Matching.thy.

Please keep in mind that all .thy files must be run in Isabelle2021-1/HOL.
