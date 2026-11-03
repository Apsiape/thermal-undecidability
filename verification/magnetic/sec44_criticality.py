"""Section 4.4 sanity: the anisotropic point p_H=2/3, p_V=1/2 (Ising K1=ln3/2, K2=ln2/2) is critical.
(1) exact identities: y_H y_V = 2 ; sinh(2K1) sinh(2K2) = 1 ; isoradial half-angle check arctan(1/2)+arctan(1/3)=pi/4.
(2) cylinder transfer matrix (circumference L, transfer along the horizontal direction):
    xi_L = 1/log(lambda0/lambda1). At criticality xi_L / L tends to a constant (power-law decay in the plane);
    at the comparison point (y_H = 2 e^{-Delta}, y_V = 1) xi_L saturates (exponential decay)."""
import numpy as np
from scipy.sparse.linalg import eigsh
import scipy.sparse as sp

pH, pV = 2 / 3, 1 / 2
yH, yV = pH / (1 - pH), pV / (1 - pV)
K1, K2 = -0.5 * np.log(1 - pH), -0.5 * np.log(1 - pV)
print("y_H y_V = %.15f" % (yH * yV))
print("K1 = ln3/2 ? %s ; K2 = ln2/2 ? %s" % (np.isclose(K1, np.log(3) / 2), np.isclose(K2, np.log(2) / 2)))
print("sinh(2K1) sinh(2K2) = %.15f" % (np.sinh(2 * K1) * np.sinh(2 * K2)))
print("tanh K1 = %.6f, tanh K2 = %.6f, arctan sum - pi/4 = %.2e" %
      (np.tanh(K1), np.tanh(K2), np.arctan(np.tanh(K1)) + np.arctan(np.tanh(K2)) - np.pi / 4))


def xi_cyl(Kt, Kc, L):
    """Transfer along direction with coupling Kt; circumference coupling Kc; L spins per column, periodic."""
    n = 2 ** L
    ar = np.arange(n)
    spins = 1 - 2 * ((ar[:, None] >> np.arange(L)[None, :]) & 1)
    E_col = (spins * np.roll(spins, -1, axis=1)).sum(1)  # intra-column bonds
    D = np.exp(0.5 * Kc * E_col)
    # V = prod_i exp(Kt s_i s'_i) = tensor product of 2x2 matrices -> apply as operator
    v1 = np.array([[np.exp(Kt), np.exp(-Kt)], [np.exp(-Kt), np.exp(Kt)]])

    def matvec(x):
        y = D * x
        y = y.reshape([2] * L)
        for ax in range(L):
            y = np.tensordot(v1, y, axes=([1], [ax]))
            y = np.moveaxis(y, 0, ax)
        y = y.reshape(n)
        return D * y
    from scipy.sparse.linalg import LinearOperator
    op = LinearOperator((n, n), matvec=matvec, dtype=float)
    vals = eigsh(op, k=2, which='LA', return_eigenvectors=False, tol=1e-12)
    vals = np.sort(vals)[::-1]
    return 1.0 / np.log(vals[0] / vals[1])


for label, (yh, yv) in [("critical (2,1)", (2.0, 1.0)), ("comparison (2e^-0.2, 1)", (2 * np.exp(-0.2), 1.0)),
                        ("comparison (2e^-0.05, 1)", (2 * np.exp(-0.05), 1.0))]:
    k1 = 0.5 * np.log(1 + yh); k2 = 0.5 * np.log(1 + yv)
    row = []
    for L in [4, 6, 8, 10, 12, 14]:
        xi = xi_cyl(k1, k2, L)
        row.append("L=%d: xi=%.3f xi/L=%.4f" % (L, xi, xi / L))
    print("%-28s " % label + " | ".join(row))
