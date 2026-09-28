# Supremum preservation under a gradient step

**Theorem.** Let $E$ be a finite-dimensional real inner-product space. If
$f:E\to\mathbb R$ is continuously differentiable and bounded above, then

$$
\sup_{x\in E} f(x+\nabla f(x))=\sup_{x\in E} f(x).
$$

This proves the bounded-only variant of
[MathOverflow 347178](https://mathoverflow.net/questions/347178).
The Lean theorem is [`GradientSupremum.supremum_gradient_step`](../GradientSupremum/Main.lean).
The [Euclidean specialization](../GradientSupremum/Mathoverflow347178.lean) retains
both boundedness hypotheses and all quantifiers of the original formal statement.

## 1. Reduction to a positive gap

Put $M=\sup f$, $g=M-f$, and $S(x)=x-\nabla g(x)=x+\nabla f(x)$.
Then $g\ge0$ and $\inf g=0$. Suppose the asserted equality fails. There is a
constant $D>0$ such that

$$
g(S(x))\ge D\qquad\text{for every }x\in E.
\tag{1}
$$

Choose $p\in E$ and $a\in\mathbb R$ with $g(p)<a<D$, and choose
$R>\sqrt{2g(p)}$. We will construct a continuous deformation on
$\overline B(p,R)$ and use Brouwer's fixed-point theorem to contradict (1).

## 2. Separation of compact low centers

The set $K=\overline B(p,R)\cap\{g\le a\}$ is nonempty and compact.
The nonempty closed set $A=\{g\ge D\}$ contains $S(E)$ and is disjoint from $K$.
Thus there is $c>0$ such that

$$
\|y-S(x)\|\ge c\qquad(y\in K,\ x\in E).
\tag{2}
$$

Define

$$
Q_y(x)=g(x)-\tfrac12\|x-y\|^2,\qquad
V(y,x)=\frac{y-S(x)}{\max\{c,\|y-S(x)\|\}}.
$$

The vector field $V$ is jointly continuous and has norm at most one.
Since $\nabla Q_y(x)=y-S(x)$, equation (2) gives

$$
\langle\nabla Q_y(x),V(y,x)\rangle=\|y-S(x)\|\ge c\qquad(y\in K).
\tag{3}
$$

These facts are proved in [`Ascent.lean`](../GradientSupremum/Ascent.lean).

## 3. A uniform short ascent step

Set $T=2a/c$. Continuity of $\nabla g$ makes $S$ uniformly continuous on
$\overline B(p,R+T+1)$. Choose $0<\varepsilon\le1$ such that points of this ball
at distance at most $\varepsilon$ have images under $S$ at distance at most $c/2$.

For $x\in\overline B(p,R+T)$, $\|v\|\le1$,
$\langle y-S(x),v\rangle\ge c$, and $0\le h\le\varepsilon$, we claim

$$
Q_y(x+hv)\ge Q_y(x)+hc/2.
\tag{4}
$$

Indeed, the segment $x+tv$, $0\le t\le h$, stays in the larger ball, and

$$
\frac{d}{dt}Q_y(x+tv)
=\langle y-S(x+tv),v\rangle
\ge\langle y-S(x),v\rangle-\|S(x+tv)-S(x)\|\,\|v\|
\ge c/2.
$$

The mean value theorem gives (4). Only uniform continuity on this compact ball
is used. See `uniform_ascent_step` in [`Ascent.lean`](../GradientSupremum/Ascent.lean).

## 4. A finite-step deformation

Choose an integer $N>0$ with $N\varepsilon>T$, and put

$$
h(y)=\frac{2\max\{0,a-g(y)\}}{Nc}.
$$

Then $h$ is continuous, $0\le Nh(y)\le T$, and $h(y)\le\varepsilon$.
For $s\in[0,1]$ define

$$
x_0(s,y)=y,\qquad
x_{k+1}(s,y)=x_k(s,y)+s h(y)V(y,x_k(s,y)),\qquad H_s(y)=x_N(s,y).
$$

This finite recursion makes $H$ jointly continuous, with $H_0(y)=y$.
Centers with $g(y)\ge a$ are fixed because $h(y)=0$.
For $y\in\overline B(p,R)$ and $k\le N$,
$\|x_k(s,y)-y\|\le ksh(y)\le T$.
Thus every step starts in the ball where (4) applies. When $g(y)<a$, the
**original center** $y$ belongs to $K$ throughout the walk. Applying (3) and (4)
at each step gives

$$
Q_y(H_s(y))\ge g(y)+Nsh(y)c/2=g(y)+s(a-g(y)).
$$

Including the fixed high centers, we obtain, for all $y\in\overline B(p,R)$
and $s\in[0,1]$,

$$
g(H_s(y))\ge g(y)+\tfrac12\|H_s(y)-y\|^2,\qquad g(H_1(y))\ge a.
\tag{5}
$$

The recursion and displacement bound are in [`Iteration.lean`](../GradientSupremum/Iteration.lean).
The construction and estimate (5) are in [`Deformation.lean`](../GradientSupremum/Deformation.lean).

## 5. The topological step

We use the following consequence of Brouwer's fixed-point theorem: if a continuous
homotopy on a closed ball starts at the identity and avoids the center on the
boundary at every time, its final map attains the center somewhere in the ball.

To prove it, translate and scale to the closed unit ball centered at zero.
Suppose the final map $H_1$ has no zero. For $\|u\|\le1$, put

$$
d(u)=\max\{1,2\|u\|\},\quad v(u)=2u/d(u),\quad t(u)=2-d(u),\quad
z(u)=H_{t(u)}(v(u)).
$$

The vector $z(u)$ is nonzero: when $d(u)=1$, this follows from the assumed
absence of a zero of $H_1$; when $d(u)>1$, we have $\|v(u)\|=1$ and use the
boundary hypothesis. Therefore $r(u)=z(u)/\|z(u)\|$ is a continuous map to the sphere.
On the sphere, $d=2$, $v=u$, and $t=0$, so $r(u)=u$.
Brouwer's theorem gives a fixed point of the self-map $u\mapsto-r(u)$ of the ball.
At that point $\|u\|=1$, hence $u=-r(u)=-u$, a contradiction.

This argument is formalized in [`Homotopy.lean`](../GradientSupremum/Homotopy.lean).
The Brouwer theorem itself is proved by harfe's cubical Sperner development;
[THIRD_PARTY.md](../THIRD_PARTY.md) gives its source, license, and port details.

## 6. Contradiction and conclusion

If $H_s(y)=p$ for $y\in\overline B(p,R)$, then (5) and $g\ge0$ imply

$$
\tfrac12\|y-p\|^2\le g(p)-g(y)\le g(p).
$$

Since $R>\sqrt{2g(p)}$, this is impossible on the boundary of the ball.
The topological result gives $y\in\overline B(p,R)$ with $H_1(y)=p$.
But (5) then gives $g(p)\ge a$, contrary to the choice of $p$ and $a$.

Thus (1) is impossible and $\inf_x g(S(x))=0$. Substituting $g=M-f$ proves

$$
\sup_x f(x+\nabla f(x))=\sup_x f(x).\qquad\square
$$

[`Main.lean`](../GradientSupremum/Main.lean) packages this argument as a transfer
of upper bounds, then derives equality of the real suprema.
