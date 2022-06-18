These are the Magma and log files for our (Nikola Adzaga, Shiva Chidambaram, Timo Keller, Oana Padurariu) preprint "Rational points on hyperelliptic Atkin-Lehner quotients of modular curves and their coverings" https://arxiv.org/submit/4204672

-- The files qc_X0Nstar.m carry out quadratic Chabauty for X_0(N)^* (using code by [BDMTV]: https://github.com/steffenmueller/QCMod with the only changes contained in qc_init_g2.m.diff).

-- The files elliptic Chabauty/ec_X0Nstar.m carry out elliptic curve Chabauty for X_0(N)^* (using code by [BGX21]: https://github.com/XavierXarles/HyperellipticParametrizationsQcurves).

-- The files Coleman/cc_X0Nstar.m carry out classical Coleman--Chabauty for X_0(N)^* (using code by [Balakrishnan--Tuitman]: https://github.com/jtuitman/Coleman). The file Coleman/diff_of_ratpts.m verifies a hypothesis for this code by checking that differences of rational points on the curve generate a finite index subgroup of the Mordell-Weil group of the Jacobian.

-- The file Coverings/X0N_coverings.m computes X_0(N) -> X_0(N)^* for N = 133, but can be easily adapted for all N such that X_0(N) is non-hyperelliptic.

-- The file genus-3-4-5/genus3-4-5.m contains an alternative proof for X_0(N)^* of genus > 2.

-- The file IsSemistable.m contains code to check whether a given integral model of a hyperelliptic curve is semistable (used for the local heights away from p in the cases where we apply quadratic Chabauty).

-- The file jinvs.m contains the code to compute the j-invariants.

-- The log files for $file.m are contained in $file.log.
