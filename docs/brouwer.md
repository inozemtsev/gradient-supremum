# The local Brouwer proof

The formal development proves the fixed-point theorem for the closed unit ball
of any finite-dimensional real normed space. It has two analytic steps after
the cubical Sperner lemma.

## 1. Approximate fixed points on a cube

Let $f:[0,1]^n\to[0,1]^n$ be continuous, and write $d(x)=f(x)-x$.
Label $x$ by the smallest coordinate $i<n$ for which either $f_i(x)<x_i$
or $x_i=1$. Give it label $n$ when there is no such coordinate.
On the lower face $x_i=0$ its label cannot be $i$; on the upper face $x_i=1$
its label is at most $i$.

Apply the cubical Sperner lemma to a grid of mesh $1/m$. A fully labeled
simplex contains a vertex $x$ of label $n$ and a vertex $y_i$ of each label $i$.
Its vertices satisfy

$$
d_i(x)\ge0,\qquad d_i(y_i)\le0,\qquad \|x-y_i\|_\infty\le 1/m.
$$

Given $\varepsilon>0$, uniform continuity of $d$ makes
$\|d(x)-d(y_i)\|_\infty<\varepsilon$ when $m$ is large enough.
Hence $0\le d_i(x)<\varepsilon$ for every coordinate. Thus the displacement
norm can be made arbitrarily small.

The continuous function $x\mapsto\|d(x)\|_\infty$ attains its minimum on the
compact cube. The preceding estimate forces that minimum to be zero, so
$f$ has a fixed point. This is `Brouwer.exists_fixedPoint_cube`.

## 2. Transfer to a ball

Choose a continuous linear coordinate isomorphism $e:E\to\mathbb R^n$ and
put $K=\max\{1,\|e\|\}$. Every point of the closed unit ball has coordinates
in $[-K,K]$. Define

$$
\operatorname{encode}(x)_i=\frac{e(x)_i/K+1}{2},\qquad
\operatorname{decode}(u)=e^{-1}\bigl(K(2u-1)\bigr).
$$

The radial projection

$$
P(z)=\frac{z}{\max\{1,\|z\|\}}
$$

is continuous, takes values in the unit ball, and fixes that ball pointwise.
Consequently $r=P\circ\operatorname{decode}$ satisfies
$r\circ\operatorname{encode}=\mathrm{id}$ on the ball.

For a continuous ball map $f$, apply the cube theorem to
$\operatorname{encode}\circ f\circ r$. If $u$ is a fixed point, applying $r$
to its fixed-point equation gives $f(r(u))=r(u)$.
This is `Brouwer.exists_fixedPoint_closedBall`.

The formal proof is in `GradientSupremum/Brouwer/Cube.lean` and `ClosedBall.lean`.
The local triangulation and parity modules are adapted from harfe's cubical
Sperner development; their source and license are recorded in `THIRD_PARTY.md`.
