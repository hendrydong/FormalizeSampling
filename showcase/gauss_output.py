"""DF-8: Gaussian output and path KL, retaining initialization (illustration, not a proof).

Exact-score DDPM with reverse variance beta_k / alpha_k^2 (`ddpmVar`) on Gaussian data
N(0, v I_d), uniform grid t_k = t_1 + (k - 1) h, t_1 = DELTA, t_N = HORIZON. Everything is
closed form (`_gauss_ddpm.py`). Compared with the Lean statements of
`Samplers/DiffusionGaussianOutputRate.lean`:
  * `algVar_ddpm_sub_gaussVar_le`: 0 <= w_1 - s_1 <= (1 - v) e^{-2(2T - t_1)} + e^{2h} - 1,
  * `klDiv_output_isoGauss_ddpm_le`: KL(p_1 || q_1) <= d B^2 / (4 s_1^2), B the bound above,
  * `klDiv_truePath_isoGauss_ddpm_ge`: KL(path) >= d (T - t_1) h / (1 + h)   (v <= 1),
  * `errWeight_mul_sub_eq` (exact identity), checked through its telescoped closed form.
At v=1, the output bounds give quadratic decay at fixed horizon. For v<1 the
initialization error remains; slopes fitted over this finite grid are not asymptotic proofs.
"""

import numpy as np
from _gauss_ddpm import exact_kl, output_law, path_terms
from _style import BLUE, INK2, ORANGE, plt, save, setup

DELTA, HORIZON = 0.01, 5.0
VS = [0.1, 0.5, 1.0]
DS = [1, 10]
NS = [10, 20, 40, 80, 160, 320, 640, 1280]


def grid(n):
    return np.concatenate([[0.0], np.linspace(DELTA, HORIZON, n)])


def closed_form_err(v, t):
    """w_1 - s_1 from the telescoped identity phi_1 e_1 = phi_N e_N + sum phi_{k-1} L_k."""
    n = len(t) - 1
    s = np.exp(-2 * t) * v + 1 - np.exp(-2 * t)
    phi = np.exp(-2 * t) / s**2
    tot = phi[n] * (1 - s[n])
    for k in range(2, n + 1):
        h = t[k] - t[k - 1]
        beta, alpha2 = -np.expm1(-2 * h), np.exp(-2 * h)
        tot += phi[k - 1] * beta**2 / (alpha2 * s[k])
    return tot / phi[1]


def lean_bounds(v, d, n):
    t = grid(n)
    h = t[2] - t[1]
    s1 = np.exp(-2 * DELTA) * v + 1 - np.exp(-2 * DELTA)
    b = (1 - v) * np.exp(-2 * (2 * HORIZON - DELTA)) + np.expm1(2 * h)
    return h, b, d * b**2 / (4 * s1**2), d * (HORIZON - DELTA) * h / (1 + h)


def main():
    setup()
    rows = {}
    for v in VS:
        for d in DS:
            out = []
            for n in NS:
                t = grid(n)
                h, b, out_ub, path_lb = lean_bounds(v, d, n)
                _, wq, _, sp = output_law(np.zeros(d), np.full(d, v), t)
                err = float(wq[0] - sp[0])
                assert 0 <= err <= b * (1 + 1e-12), (v, n, err, b)
                assert abs(err - closed_form_err(v, t)) <= 1e-9 * max(1.0, abs(err))
                kl = exact_kl(np.zeros(d), np.full(d, v), t)
                terms, init = path_terms(np.zeros(d), np.full(d, v), t)
                path = float(terms.sum() + init)
                assert kl <= out_ub, (v, d, n, kl, out_ub)
                assert path >= path_lb, (v, d, n, path, path_lb)
                assert kl <= path
                out.append((n, h, kl, out_ub, path, path_lb))
            rows[(v, d)] = np.array(out)

    print("v    d   N     h        KL out     Lean UB    UB/KL   path KL    Lean LB   path/LB")
    for (v, d), arr in rows.items():
        for n, h, kl, ub, path, lb in arr:
            print(
                f"{v:<4} {d:<3} {int(n):<5} {h:.2e} {kl:.3e}  {ub:.3e}  {ub / kl:6.2f}  "
                f"{path:.3e}  {lb:.3e}  {path / lb:5.2f}"
            )
        sl_out = np.polyfit(np.log(arr[-4:, 0]), np.log(arr[-4:, 2]), 1)[0]
        sl_path = np.polyfit(np.log(arr[-4:, 0]), np.log(arr[-4:, 4]), 1)[0]
        print(f"  slopes (last 4 N): output {sl_out:.2f}, path {sl_path:.2f}")

    fig, axes = plt.subplots(1, 3, figsize=(14, 4.4), sharey=True)
    for ax, v in zip(axes, VS):
        for d, ls in zip(DS, ["-", "--"]):
            arr = rows[(v, d)]
            lab = d == DS[0]
            ax.loglog(
                arr[:, 0], arr[:, 2], ls, color=BLUE, label="output KL (exact)" if lab else None
            )
            ax.loglog(
                arr[:, 0],
                arr[:, 3],
                ls,
                color=BLUE,
                alpha=0.45,
                label="Lean output bound" if lab else None,
            )
            ax.loglog(
                arr[:, 0], arr[:, 4], ls, color=ORANGE, label="path KL (exact)" if lab else None
            )
            ax.loglog(
                arr[:, 0],
                arr[:, 5],
                ls,
                color=ORANGE,
                alpha=0.45,
                label="Lean path lower bound" if lab else None,
            )
        ax.set_title(f"v = {v}")
        ax.set_xlabel("number of steps N")
        ax.text(
            0.03, 0.04, "solid d = 1, dashed d = 10", transform=ax.transAxes, color=INK2, fontsize=9
        )
    axes[0].set_ylabel("KL")
    axes[0].legend(loc="upper right")
    fig.suptitle(
        "Gaussian data, exact score, uniform grid: output vs path KL (output Θ(h²) proved for v = 1)",
        y=1.02,
    )
    fig.tight_layout()
    save(fig, "gauss_output.png")


if __name__ == "__main__":
    main()
