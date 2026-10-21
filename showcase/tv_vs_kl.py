"""EX-3: accumulate errors in KL, not in TV (illustration, not a proof).

Two Euler-Maruyama chains x <- x + h b + sqrt(2h) xi from the same point: exact drift b = 0 and
estimated drift b = Delta (a constant error). After n steps they are N(0, 2nh) and
N(n h Delta, 2nh), so
    true TV                 = 2 Phi(sqrt(n h) |Delta| / (2 sqrt 2)) - 1,
    KL                      = n h Delta^2 / 4           (equal to the GI-1 budget: attained),
    Pinsker from KL         = sqrt(KL / 2) = sqrt(n h Delta^2 / 8),
    TV telescoping (GI-1)   = n * sqrt(h) |Delta| / (2 sqrt pi)   (per-step bound, summed),
and telescoping / Pinsker = sqrt(2n/pi) (`GaussianIncrementTight.sqrt_mul_tvSup_le_telescoped`).
"""

from math import erf, sqrt

import numpy as np
from _style import BLUE, INK2, MUTED, ORANGE, VIOLET, plt, save, setup

H = 0.01
DELTA = 0.5


def phi(x):
    return 0.5 * (1 + np.vectorize(erf)(x / sqrt(2)))


def main() -> None:
    setup()
    n = np.unique(np.round(np.logspace(0, 4, 200)).astype(int)).astype(float)
    true_tv = 2 * phi(np.sqrt(n * H) * DELTA / (2 * sqrt(2))) - 1
    step_tv = 2 * phi(sqrt(H) * DELTA / (2 * sqrt(2))) - 1
    sum_exact = n * step_tv
    telescoped = n * sqrt(H) * DELTA / (2 * sqrt(np.pi))
    kl = n * H * DELTA**2 / 4
    pinsker = np.sqrt(kl / 2)
    assert np.all(true_tv <= pinsker + 1e-15) and np.all(true_tv <= sum_exact + 1e-15)
    assert np.allclose(telescoped / pinsker, np.sqrt(2 * n / np.pi))

    fig, axes = plt.subplots(1, 2, figsize=(12, 4.5))
    ax = axes[0]
    ax.loglog(n, telescoped, color=ORANGE, label="TV telescoping: n × (per-step TV bound)")
    ax.loglog(n, pinsker, color=BLUE, label="KL accumulation + Pinsker: √(KL/2)")
    ax.loglog(n, true_tv, color=INK2, lw=2.6, label="true TV")
    ax.axhline(1.0, color=MUTED, lw=1, ls="--")
    ax.text(1.3, 1.25, "TV ≤ 1 always: above this line a bound is vacuous", color=INK2, fontsize=9)
    ax.set_xlabel("number of steps n")
    ax.set_ylabel("bound on / value of TV")
    ax.set_title(f"constant drift error Δ = {DELTA}, step h = {H}")
    ax.legend(loc="lower right")

    ax = axes[1]
    ax.loglog(n, telescoped / true_tv, color=ORANGE, label="telescoped / true TV")
    ax.loglog(n, pinsker / true_tv, color=BLUE, label="Pinsker / true TV")
    ax.loglog(n, np.sqrt(2 * n / np.pi), "--", color=VIOLET, lw=1.6, label="√(2n/π)")
    ax.set_xlabel("number of steps n")
    ax.set_ylabel("overestimation factor")
    ax.set_title("telescoping in TV overshoots by √(2n/π)")
    ax.legend(loc="upper left")
    fig.suptitle(
        "EX-3: summing per-step TV errors loses √n; summing KL is exact",
        fontsize=13,
        fontweight="bold",
        y=1.02,
    )
    fig.tight_layout()
    save(fig, "tv_vs_kl.png")

    print("    n | true TV | Pinsker √(KL/2) | telescoped | tele/true | √(2n/π)")
    for k in [1, 10, 100, 1000, 10000]:
        i = int(np.argmin(np.abs(n - k)))
        print(
            f"{int(n[i]):5d} | {true_tv[i]:.4f}  | {pinsker[i]:.4f}          | "
            f"{telescoped[i]:10.4f} | {telescoped[i] / true_tv[i]:9.2f} | "
            f"{sqrt(2 * n[i] / np.pi):.2f}"
        )
    print(f"n × exact per-step TV at n = 10^4: {sum_exact[-1]:.4f} (same order as telescoped)")
    print(f"KL after n steps = n h Δ²/4 = {H * DELTA**2 / 4:.3g} n (exactly the GI-1 budget)")


if __name__ == "__main__":
    main()
