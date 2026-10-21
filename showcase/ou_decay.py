"""FL-4 / KL-5: Langevin (OU) KL decay e^{-2at} and the Gaussian log-Sobolev inequality.

(Illustration, not a proof.) Target pi = N(0, v). The OU / Langevin semigroup with rate a is the
kernel `OULangevinDecay.ouKernelVar v a t`: x -> N(e^{-at} x, v (1 - e^{-2at})). Lean statements
tested here (1D):

* FL-4, `OULangevinDecay.toReal_klDiv_ouKernelVar_comp_le`: for every probability rho with finite
  KL and second moment,  KL(OU_t rho || pi) <= e^{-2at} KL(rho || pi);
  `toReal_klDiv_ouKernelVar_comp_gaussianReal`: EQUALITY for rho = N(m, v), with value
  e^{-2at} m^2 / (2v).
* KL-5(b), `GaussianLSIZero.klDiv_le_fisher0`: KL(rho || pi) <= (v/2) I(rho || pi),
  I = int |d/dx log(rho/pi)|^2 d rho (equality again for N(m, v)).
* FL-4 (probability flow of OU), `ProbabilityFlowOU.hasDerivAt_gaussKL_ouDensity`:
  d/dt KL(rho_t || pi) = -(a v) I(rho_t || pi)  (checked by finite differences).

Every start is a Gaussian mixture, so rho_t is a Gaussian mixture in closed form; KL and Fisher
information are computed by quadrature with the exact mixture score.
"""

import numpy as np
from _style import AQUA, BLUE, INK2, MUTED, ORANGE, YELLOW, plt, save, setup

V, A = 1.0, 1.0
XS = np.linspace(-14, 14, 56001)
DX = XS[1] - XS[0]
STARTS = {
    "mean shift N(2, 1)": ([1.0], [2.0], [1.0]),
    "narrow N(0, 0.05)": ([1.0], [0.0], [0.05]),
    "wide N(0, 6)": ([1.0], [0.0], [6.0]),
    "bimodal ½N(±2.5, 0.1)": ([0.5, 0.5], [-2.5, 2.5], [0.1, 0.1]),
}
COLORS = dict(zip(STARTS, (BLUE, ORANGE, AQUA, YELLOW)))


def mixture_at(t, w, m, s):
    """OU_t applied to sum_i w_i N(m_i, s_i)."""
    e = np.exp(-A * t)
    return w, e * np.asarray(m), e**2 * np.asarray(s) + V * (1 - e**2)


def kl_fisher(w, m, s):
    comps = [
        wi * np.exp(-((XS - mi) ** 2) / (2 * si)) / np.sqrt(2 * np.pi * si)
        for wi, mi, si in zip(w, m, s)
    ]
    p = np.sum(comps, axis=0)
    dp = np.sum([-(XS - mi) / si * c for c, mi, si in zip(comps, m, s)], axis=0)
    log_pi = -(XS**2) / (2 * V) - 0.5 * np.log(2 * np.pi * V)
    ok = p > 1e-300
    kl = np.sum(p[ok] * (np.log(p[ok]) - log_pi[ok])) * DX
    rel_score = dp[ok] / p[ok] + XS[ok] / V
    fisher = np.sum(p[ok] * rel_score**2) * DX
    return kl, fisher


def main() -> None:
    setup()
    ts = np.linspace(0, 3, 121)
    res = {}
    for name, (w, m, s) in STARTS.items():
        kl, fi = np.array([kl_fisher(*mixture_at(t, w, m, s)) for t in ts]).T
        res[name] = (kl, fi)
        decay = np.exp(-2 * A * ts) * kl[0]
        assert np.all(kl <= decay * (1 + 1e-9) + 1e-14), f"FL-4 decay violated ({name})"
        assert np.all(kl <= V / 2 * fi * (1 + 1e-9) + 1e-14), f"KL-5 LSI violated ({name})"
        # de Bruijn-type identity for the OU flow: d/dt KL = -(a v) I.
        h = 1e-4
        for t in (0.25, 1.0, 2.0):
            k_plus = kl_fisher(*mixture_at(t + h, w, m, s))[0]
            k_minus = kl_fisher(*mixture_at(t - h, w, m, s))[0]
            deriv = (k_plus - k_minus) / (2 * h)
            fisher_t = kl_fisher(*mixture_at(t, w, m, s))[1]
            assert abs(deriv + A * V * fisher_t) < 1e-6 * max(1.0, fisher_t), "dKL/dt = -a v I"
        j = np.searchsorted(ts, 1.0)
        print(
            f"{name:24s}: KL0 = {kl[0]:.4f}; at t = 1: KL = {kl[j]:.4g},"
            f" e^-2at KL0 = {decay[j]:.4g} (ratio {kl[j] / decay[j]:.4f});"
            f" max_t KL/((v/2) I) = {np.max(2 * kl / (V * fi)):.4f}"
        )
    kl, fi = res["mean shift N(2, 1)"]
    exact = np.exp(-2 * A * ts) * 2.0**2 / (2 * V)
    assert np.allclose(kl, exact, rtol=1e-9), "N(m, v) must attain e^{-2at} KL0 exactly"
    assert np.allclose(kl, V / 2 * fi, rtol=1e-9), "N(m, v) must attain the LSI"
    print(f"mean shift: max |KL - e^-2at m^2/(2v)| / KL = {np.max(np.abs(kl / exact - 1)):.1e}")
    print("d/dt KL = -(a v) I checked by central differences at t = 0.25, 1, 2 for every start")

    fig, axes = plt.subplots(1, 3, figsize=(16, 4.6))
    ax = axes[0]
    w, m, s = STARTS["bimodal ½N(±2.5, 0.1)"]
    xs = XS[np.abs(XS) < 5]
    for t, alpha in zip((0.0, 0.2, 0.5, 1.0), (0.25, 0.5, 0.75, 1.0)):
        ww, mm, ss = mixture_at(t, w, m, s)
        dens = sum(
            wi * np.exp(-((xs - mi) ** 2) / (2 * si)) / np.sqrt(2 * np.pi * si)
            for wi, mi, si in zip(ww, mm, ss)
        )
        ax.plot(xs, dens, color=YELLOW, alpha=alpha, lw=2, label=f"OU_t ρ, t = {t:g}")
    ax.plot(
        xs,
        np.exp(-(xs**2) / (2 * V)) / np.sqrt(2 * np.pi * V),
        "--",
        color=INK2,
        lw=2.2,
        label="target N(0, 1)",
    )
    ax.set_ylim(0, 0.75)
    ax.set_xlabel("x")
    ax.set_ylabel("density")
    ax.set_title("bimodal start flowing to N(0, 1)")
    ax.legend(loc="upper right", fontsize=8.5)

    ax = axes[1]
    ax.semilogy(ts, np.exp(-2 * A * ts), "--", color=INK2, lw=2.6, label=r"Lean bound $e^{-2at}$")
    for name, (kl, _) in res.items():
        style = dict(marker="o", ms=4, ls="none", markevery=6) if name.startswith("mean") else {}
        ax.semilogy(ts, kl / kl[0], color=COLORS[name], label=name, **style)
    ax.set_xlabel("time t")
    ax.set_ylabel(r"KL(OU$_t\rho$ ‖ π) / KL(ρ ‖ π)")
    ax.set_title(f"KL decay along OU (a = {A:g}, v = {V:g})")
    ax.legend(loc="lower left", fontsize=8.5)

    ax = axes[2]
    for name, (kl, fi) in res.items():
        style = dict(marker="o", ms=4, ls="none", markevery=6) if name.startswith("mean") else {}
        ax.plot(ts, kl / (V / 2 * fi), color=COLORS[name], label=name, **style)
    ax.axhline(1.0, color=INK2, lw=2.2, ls="--")
    ax.text(3, 1.03, "LSI equality", color=INK2, ha="right", fontsize=9)
    ax.set_ylim(0, 1.12)
    ax.set_xlabel("time t")
    ax.set_ylabel(r"KL / ((v/2) I)")
    ax.set_title(r"Gaussian LSI: KL $\leq$ (v/2) I along the flow")
    ax.text(
        0.05,
        0.05,
        "(dKL/dt = −a v I is checked numerically)",
        color=MUTED,
        fontsize=8.5,
        transform=ax.transAxes,
    )
    fig.suptitle(
        r"FL-4 / KL-5: Langevin (OU) flow contracts KL by $e^{-2at}$; "
        "mean-shifted Gaussians attain it, other starts decay faster",
        fontsize=13,
    )
    fig.tight_layout()
    save(fig, "ou_decay.png")


if __name__ == "__main__":
    main()
