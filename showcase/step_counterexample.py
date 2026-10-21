"""CE-08: one ideal-velocity step can increase the KL (illustration, not a proof).

Target pi = N(0, 1), current law rho = N(0, s). The ideal velocity is
v = -(log(rho / pi))' = (1/s - 1) x, and one deterministic step x -> x + eta v(x) = c x with
c = 1 + eta (1/s - 1) maps N(0, s) to N(0, c^2 s). Both KLs are closed form:
KL(N(0, a) || N(0, 1)) = (a - 1 - log a) / 2. Lean: for every eta > 0 there is s > 0 with
KL after > KL before (`IdealVelocityStep.exists_klDiv_map_step_idealVel_gt`).
"""

import numpy as np
from _style import BLUE, INK2, MUTED, ORANGE, RED, VIOLET, plt, save, setup

ETAS = [(0.05, BLUE), (0.2, ORANGE), (0.5, VIOLET), (1.0, RED)]


def kl_to_std(a):
    return 0.5 * (a - 1 - np.log(a))


def kl_after(s, eta):
    c = 1 + eta * (1 / s - 1)
    return kl_to_std(c**2 * s)


def main() -> None:
    setup()
    s = np.logspace(-6, 1.5, 3000)
    before = kl_to_std(s)
    fig, axes = plt.subplots(1, 2, figsize=(12, 4.5))

    ax = axes[0]
    ax.loglog(s, before, color=INK2, lw=2.5, label="before the step: KL(N(0,s) ‖ N(0,1))")
    for eta, color in ETAS:
        ax.loglog(s, kl_after(s, eta), color=color, lw=1.8, label=f"after one step, η = {eta}")
    ax.set_xlabel("variance s of the current law ρ = N(0, s)")
    ax.set_ylabel("KL to the target N(0, 1)  (nats)")
    ax.set_title("KL before and after one ideal-velocity step")
    ax.set_ylim(1e-5, 1e6)
    ax.legend(loc="upper right", fontsize=8.8)

    ax = axes[1]
    print("eta   | KL increases for s below | eta|1/s-1| there | example (s, KL before -> after)")
    for eta, color in ETAS:
        ratio = kl_after(s, eta) / before
        ax.semilogx(s, ratio, color=color, label=f"η = {eta}")
        up = (ratio > 1) & (s < 1)
        s_star = s[up].max()
        s_ex = s_star / 10
        print(
            f"{eta:5.2f} | {s_star:.4g}                   | {eta * abs(1 / s_star - 1):.3f}"
            f"            | s={s_ex:.3g}: {kl_to_std(s_ex):.3f} -> {kl_after(s_ex, eta):.3f}"
        )
        ax.plot([s_star], [1.0], "o", ms=7, color=color, mec="white", mew=1.5, zorder=5)
        large = (ratio > 1) & (s > 1)
        if large.any():
            print(f"       also increases for s >= {s[large].min():.4g}")
    ax.axhline(1.0, color=MUTED, lw=1.2, ls="--")
    ax.fill_between(s, 1, 1e3, color="#e34948", alpha=0.06, lw=0)
    ax.text(3e-6, 1.6, "KL goes UP", color=RED, fontsize=10, fontweight="bold")
    ax.text(3e-6, 0.55, "KL goes down", color=INK2, fontsize=10)
    ax.set_yscale("log")
    ax.set_ylim(0.05, 1e3)
    ax.set_xlabel("variance s of the current law ρ = N(0, s)")
    ax.set_ylabel("KL after / KL before")
    ax.set_title("every fixed step size fails for narrow enough ρ")
    ax.legend(loc="upper right")
    fig.suptitle(
        "CE-08: no step size works uniformly for the ideal velocity (target N(0,1))",
        fontsize=13,
        fontweight="bold",
        y=1.02,
    )
    fig.tight_layout()
    save(fig, "step_counterexample.png")


if __name__ == "__main__":
    main()
