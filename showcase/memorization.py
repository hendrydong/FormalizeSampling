"""DF-2: exact empirical scores concentrate near training data as terminal noise vanishes.

(Illustration, not a proof.) Twenty training points on a ring in the plane. The data law is
their empirical distribution mu = (1/n) sum_i delta_{x_i}, whose forward marginals are Gaussian
mixtures p_t = (1/n) sum_i N(e^{-t} x_i, (1 - e^{-2t}) I) with an exact closed-form score.

(a) DDPM with that exact score (geometric grid from t_1 = delta to t_N = T, variance
    beta/alpha^2, start N(0, I)) outputs q_1, which the formal bound
    `DiffusionDiscretization.klDiv_output_le_geomGrid` (made non-vacuous for singular data by
    `DiffusionDiscretization.exists_klDiv_output_le` and the witnesses
    `Audit.Diffusion.dirac_tvSup_output_le`, `twoPoint_tvSup_output_le`) says is close to p_1 = the training set blurred by
    sqrt(1 - e^{-2 delta}). As delta -> 0, with grid and horizon chosen to control
    approximation error, the output concentrates near the training points
    (`DiffusionMemorization.output_concentrates_on_training_set`, registry DF-2).
(b) The same sampler with a score learned by a small numpy MLP (denoising score matching)
    produces new points between the training points.
"""

import os

os.environ.setdefault("OPENBLAS_NUM_THREADS", "1")  # small matrices: threads only add overhead
os.environ.setdefault("OMP_NUM_THREADS", "1")

import numpy as np  # noqa: E402
from _style import BLUE, INK, INK2, MUTED, ORANGE, geom_grid, plt, save, setup  # noqa: E402

SEED = 0
N_TRAIN = 20
RADIUS = 2.0
N_SAMPLES = 2000
N_STEPS = 200
HORIZON = 6.0
DELTA_SHOW = 1e-3
RHO = 0.1  # "memorised" = within RHO of a training point (ring spacing ~ 0.63)


def training_points(rng):
    ang = 2 * np.pi * (np.arange(N_TRAIN) + 0.25 * rng.uniform(-1, 1, N_TRAIN)) / N_TRAIN
    return RADIUS * np.stack([np.cos(ang), np.sin(ang)], axis=1)


def exact_score(x_train):
    def score(y, t):
        a = np.exp(-t)
        var = -np.expm1(-2 * t)
        diff = a * x_train[None, :, :] - y[:, None, :]  # (n, m, 2)
        logits = -np.sum(diff**2, axis=2) / (2 * var)
        logits -= logits.max(axis=1, keepdims=True)
        w = np.exp(logits)
        w /= w.sum(axis=1, keepdims=True)
        return np.einsum("nm,nmd->nd", w, diff) / var

    return score


def ddpm_sample(score, delta, rng, n=N_SAMPLES):
    """Lean conventions: q_N = N(0, I); for k = N..2, x <- (x + beta s_k(x))/alpha + sigma xi."""
    t = geom_grid(delta, HORIZON, N_STEPS)
    x = rng.normal(size=(n, 2))
    for k in range(N_STEPS, 1, -1):
        dt = t[k] - t[k - 1]
        alpha = np.exp(-dt)
        beta = -np.expm1(-2 * dt)
        x = (x + beta * score(x, t[k])) / alpha + np.sqrt(beta) / alpha * rng.normal(size=x.shape)
    return x


def nearest_dist(x, x_train):
    return np.sqrt(((x[:, None, :] - x_train[None, :, :]) ** 2).sum(axis=2)).min(axis=1)


def sample_p1(x_train, delta, rng, n=N_SAMPLES):
    """Exact samples from p_1: a training point, shrunk by e^{-delta}, plus Gaussian noise."""
    idx = rng.integers(len(x_train), size=n)
    return np.exp(-delta) * x_train[idx] + np.sqrt(-np.expm1(-2 * delta)) * rng.normal(size=(n, 2))


# --- a small MLP trained by denoising score matching (pure numpy, manual backprop, Adam) ---


def features(y, t):
    sig = np.sqrt(-np.expm1(-2 * t))
    ls = np.log(sig)[:, None]
    freqs = np.array([0.25, 0.5, 1.0])[None, :]
    return np.concatenate([y, np.sin(ls * freqs), np.cos(ls * freqs), ls / 5], axis=1)


class MLP:
    def __init__(self, rng, sizes):
        self.params = []
        for i, o in zip(sizes[:-1], sizes[1:]):
            self.params += [rng.normal(size=(i, o)) * np.sqrt(1.0 / i), np.zeros(o)]
        self.m = [np.zeros_like(p) for p in self.params]
        self.v = [np.zeros_like(p) for p in self.params]
        self.step = 0

    def forward(self, x):
        acts = [x]
        h = x
        n_layers = len(self.params) // 2
        for j in range(n_layers):
            h = h @ self.params[2 * j] + self.params[2 * j + 1]
            if j < n_layers - 1:
                h = np.tanh(h)
            acts.append(h)
        return h, acts

    def train_step(self, x, target, lr):
        out, acts = self.forward(x)
        err = out - target
        loss = float(np.mean(np.sum(err**2, axis=1)))
        g = 2 * err / len(x)
        grads = [None] * len(self.params)
        n_layers = len(self.params) // 2
        for j in range(n_layers - 1, -1, -1):
            grads[2 * j] = acts[j].T @ g
            grads[2 * j + 1] = g.sum(axis=0)
            if j > 0:
                g = (g @ self.params[2 * j].T) * (1 - acts[j] ** 2)
        self.step += 1
        b1, b2 = 0.9, 0.999
        for p, gr, m, v in zip(self.params, grads, self.m, self.v):
            m *= b1
            m += (1 - b1) * gr
            v *= b2
            v += (1 - b2) * gr**2
            mh = m / (1 - b1**self.step)
            vh = v / (1 - b2**self.step)
            p -= lr * mh / (np.sqrt(vh) + 1e-8)
        return loss


def train_mlp(x_train, rng, iters=4000, batch=512):
    net = MLP(rng, [9, 128, 128, 2])
    t_lo, t_hi = np.log(1e-4), np.log(HORIZON)
    losses = []
    for it in range(iters):
        x0 = x_train[rng.integers(len(x_train), size=batch)]
        t = np.exp(rng.uniform(t_lo, t_hi, size=batch))
        eps = rng.normal(size=(batch, 2))
        y = np.exp(-t)[:, None] * x0 + np.sqrt(-np.expm1(-2 * t))[:, None] * eps
        lr = 2e-3 * (0.5 * (1 + np.cos(np.pi * it / iters)))
        losses.append(net.train_step(features(y, t), eps, lr))
    print(
        f"MLP denoising loss: first 100 its {np.mean(losses[:100]):.3f}, "
        f"last 500 its {np.mean(losses[-500:]):.3f}"
    )

    def score(y, t_scalar):
        t = np.full(len(y), t_scalar)
        eps_hat, _ = net.forward(features(y, t))
        return -eps_hat / np.sqrt(-np.expm1(-2 * t))[:, None]

    return score


def scatter(ax, x, x_train, color, title):
    ax.scatter(x[:, 0], x[:, 1], s=4, color=color, alpha=0.3, lw=0, rasterized=True)
    ax.scatter(x_train[:, 0], x_train[:, 1], s=9, color=INK, lw=0, zorder=3)
    ax.set_aspect("equal")
    lim = RADIUS + 1.0
    ax.set_xlim(-lim, lim)
    ax.set_ylim(-lim, lim)
    ax.set_xticks([])
    ax.set_yticks([])
    ax.grid(False)
    for side in ("left", "bottom"):
        ax.spines[side].set_visible(False)
    ax.set_title(title)


def main() -> None:
    setup()
    rng = np.random.default_rng(SEED)
    x_train = training_points(rng)
    s_exact = exact_score(x_train)
    s_mlp = train_mlp(x_train, np.random.default_rng(SEED + 1))

    x_exact = ddpm_sample(s_exact, DELTA_SHOW, np.random.default_rng(SEED + 2))
    x_mlp = ddpm_sample(s_mlp, DELTA_SHOW, np.random.default_rng(SEED + 3))
    d_exact = nearest_dist(x_exact, x_train)
    d_mlp = nearest_dist(x_mlp, x_train)
    print(f"delta = {DELTA_SHOW}, N = {N_STEPS}, T = {HORIZON}, {N_SAMPLES} samples")
    for name, dd in [("exact score", d_exact), ("MLP score", d_mlp)]:
        print(
            f"  {name:11s}: median nearest-train distance {np.median(dd):.4f}, "
            f"fraction within rho={RHO}: {np.mean(dd < RHO):.3f}"
        )

    fig, axs = plt.subplots(1, 4, figsize=(17, 4.9), gridspec_kw={"wspace": 0.32})
    for a in axs:
        a.set_box_aspect(1)
    ax0, ax1 = axs[0], axs[1]
    scatter(ax0, x_exact, x_train, BLUE, "(a) exact score: copies the data")
    scatter(ax1, x_mlp, x_train, ORANGE, "(b) learned score: fills the ring")
    for ax in (ax0, ax1):
        ax.text(
            0.5,
            -0.04,
            f"{N_SAMPLES} samples; black dots = 20 training points",
            transform=ax.transAxes,
            fontsize=8.5,
            color=INK2,
            ha="center",
            va="top",
        )

    ax = axs[2]
    bins = np.logspace(-3.5, 0.2, 50)
    ax.hist(d_exact, bins=bins, color=BLUE, alpha=0.75, label="exact score")
    ax.hist(d_mlp, bins=bins, color=ORANGE, alpha=0.6, label="MLP score")
    ax.axvline(RHO, color=MUTED, ls="--", lw=1.2)
    ax.text(RHO * 1.1, ax.get_ylim()[1] * 0.92, f"ρ = {RHO}", color=INK2, fontsize=9)
    ax.set_xscale("log")
    ax.set_xlabel("distance to the nearest training point")
    ax.set_ylabel("number of samples")
    ax.set_title(f"(c) distance to the data, δ = {DELTA_SHOW}")
    ax.legend(loc="upper left")

    ax = axs[3]
    deltas = np.logspace(-4, 0, 9)
    frac_exact, frac_p1, frac_mlp = [], [], []
    for j, dl in enumerate(deltas):
        xs = ddpm_sample(s_exact, dl, np.random.default_rng(100 + j), n=1000)
        frac_exact.append(np.mean(nearest_dist(xs, x_train) < RHO))
        xp = sample_p1(x_train, dl, np.random.default_rng(200 + j), n=20000)
        frac_p1.append(np.mean(nearest_dist(xp, x_train) < RHO))
        xm = ddpm_sample(s_mlp, dl, np.random.default_rng(300 + j), n=1000)
        frac_mlp.append(np.mean(nearest_dist(xm, x_train) < RHO))
    ax.semilogx(deltas, frac_p1, color=MUTED, lw=4, alpha=0.5, label="p₁ itself (blurred data)")
    ax.semilogx(deltas, frac_exact, "o-", color=BLUE, ms=5, label="sampler, exact score")
    ax.semilogx(deltas, frac_mlp, "s-", color=ORANGE, ms=5, label="sampler, MLP score")
    ax.set_ylim(-0.02, 1.04)
    ax.set_xlabel("early-stopping time δ = t₁")
    ax.set_ylabel(f"fraction within ρ = {RHO} of a training point", fontsize=9.5)
    ax.set_title("(d) memorisation as δ → 0")
    ax.legend(loc="upper right", fontsize=8.8)
    print("delta    | p_1 frac | exact-score frac | MLP-score frac")
    for dl, a, b, c in zip(deltas, frac_p1, frac_exact, frac_mlp):
        print(f"{dl:8.1e} | {a:.3f}    | {b:.3f}            | {c:.3f}")

    fig.suptitle(
        "Diffusion sampling with a perfect score reproduces the training set",
        fontsize=13,
        fontweight="bold",
        y=0.9,
    )
    save(fig, "memorization.png")


if __name__ == "__main__":
    main()
