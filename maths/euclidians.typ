#import "/cards.typ": *

#show: setup

//![FLASHBANG HEADER]

#import "/utils.typ": *
#import "@preview/tiptoe:0.3.1"
#import "@preview/lilaq:0.4.0" as lq
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge
#import "@preview/physica:0.9.7": *

#card("fbildege", "Formes bilinéaires non dégénérées", ("Maths.Algèbre.Euclidiens",))

Formes bilinéaires non dégénérées.

#answer

Soit $E$ un $RR$-ev. Pour $phi : E^2 -> RR$ une forme bilinéaire on considère
$
  psi : func(E, cal(L)(E, RR), x, phi_x : y |-> phi(x, y))
$
On dit que $phi$ est non dégénérée si $psi$ est unjective.

On a alors

- Si $phi$ bilinéaire symmétrique positive, $phi$ est un produit scalaire sur $E$ ssi $phi$ est non dégénérée.

*Démonstration*

- ($=>$) Si $phi$ est un produit scalaire, $x in ker psi$ #h(1fr)
  $
    psi(x) (x) = phi(x, x) = 0 => x = 0
  $

- ($arrow.l.double$) Supposons $phi$ non dégénérée, soit $x in E$ tel que $phi(x, x) = 0$. Soit $y in E$
  $
    0 <= psi(x)(y)^2 &= phi(x, y)^2 \ &<= underbrace(phi(x, x), 0) phi(y, y) \ &= 0
  $
  Donc $x in ker psi = {0}$ d'où $x = 0$.

#card("idpseucl", "Identités du produit scalaire", ("Maths.Algèbre.Euclidiens",))

Identités du produit scalaire (polarisation, parallèlogramme).

#answer

Soit $(E, scl(dot, dot))$ un $RR$-ev préhilbertien.

- (Polarisation) Pour $x, y in E$
  $
    scl(x, y) &= 1 / 2 (norm(x + y)^2 - norm(x)^2 - norm(y)^2) \
    &= 1/4 ( norm(x + y)^2 - norm(x - y)^2)
  $

- (Parallèlogramme) Pour $x, y in E$
  $
    norm(x + y)^2 + norm(x - y)^2 = 2 norm(x)^2 + 2 norm(y)^2
  $

#card("partieortho", "Orthogonal d'une partie", ("Maths.Algèbre.Euclidiens",))

Orthogonal d'une partie.

#answer

Soit $(E, scl(dot, dot))$ un $RR$-ev préhilbertien et $A subset.eq E$ une partie.

On définit 
$
A^perp &= Set(x in E, forall a in A\, scl(x, a) = 0) \
&= inter.big_(a in A) ker (x |-> scl(x, a))
$
Qui est donc un sev de $E$.

On a alors
- Pour $F$ sev de $E$, $F^perp inter F = {0}$.

- En dimension finie $F^perp plus.o F = E$

- Pour $F, G$ sevs de $E$, $(F + G)^perp = F^perp inter G^perp$.

*Démonstration*

- Par définie positivité.

- Projection.

- L'écrire.

#card("projecsev", "Projection orthogonale sur un sev de dimension finie", ("Maths.Algèbre.Euclidiens",))

Projection orthogonale sur un sev de dimension finie.

#answer

Soit $(E, scl(dot, dot))$ un $RR$-ev préhilbertien et $F$ sev de $E$.

Pour tout $x in E$, il existe un unique $z in F$ tel que $norm(x - z) = d(x, F)$, de plus si $(e_1, dots, e_d)$ est une bon de $F$
$
  z = sum_(j = 1)^d scl(x, e_j) e_j quad quad x - z in F^perp
$
Ainsi
$
  d(x, F)^2 &= norm(x - z)^2 \ &= norm(x)^2 - norm(z)^2 \
  &= norm(x)^2 - sum_(j = 1)^d scl(x, e_j)^2
$

// NOTE: M320 matrice d'une application bilinéaire

#card("exinegdetfam", "Exercice : Inégalité sur le determinant d'une famille de vecteurs", ("Maths.Algèbre.Euclidiens",))

Soit $(E, scl(dot, dot))$ euclidien de dimension $n$, $(x_1, dots, x_n) in E^n$ une famille de vecteurs et $e$ une BON. Montrer que $abs(det_e (x_1, dots, x_n))$ est indépendant de la BON $e$ choisie et que
$
  abs(det_e (x_1, dots, x_n)) <= product_(k = 1)^n norm(x_k)
$

#answer

+ Soit $e, e'$ deux BON de $E$ : #h(1fr)
  $
    abs(det_e (x_1, dots, x_n))  \ = abs(underbrace(det_e (e'), plus.minus 1) det_e' (x_1, dots, x_n)) \
  $

+ Si $(x_1, dots, x_n)$ n'est pas une base
  $
    0 &= abs(det_e (x_1, dots, x_n)) \
    &<= product_(k = 1)^n norm(x_k)
  $

+ Sinon, on pose $w = (w_1, dots, w_n)$ la BON obtenue par Gramm-Schmidt sur $x = (x_1, dots, x_n)$
  $
    forall i in [|1, n|], x_i &= sum_(k = 1)^n scl(x_i, w_k) w_k \ 
    &= sum_(k = i)^n scl(x_i, w_k) w_k \
  $
  $
    abs(det_e (x)) &= abs(det_w (x)) \ &= product_(k = 1)^n scl(x_k, w_k) \
    &<= product_(k = 1)^n norm(x_k)
  $
  Car $cal(M)_w (x) in T_n^+ (RR)$.

#card("thmrepr", "Théorème de représentation", ("Maths.Algèbre.Euclidiens",))

Théorème de représentation.

#answer

Pour $(E, scl(dot, dot))$ euclidien, soit $u in cal(L)(E, RR)$ une forme linéaire, on dispose d'un unique $w in E$ tel que
$
  forall x in E, u(x) = scl(x, w)
$

*Démonstration*

Comme $scl(dot, dot)$ est un produit scalaire
$
  psi : func(E, cal(L)(E, RR), x, y |-> scl(x, y))
$
Est injective et donc bijective par argument dimensionnel.

#card("adjendo", "Adjoint d'un endomorphisme", ("Maths.Algèbre.Euclidiens",))

Adjoint d'un endomorphisme.

#answer

Soit $(E, scl(dot, dot))$ et $u in cal(L)(E)$, pour tout $x in E$ il existe un unique $z_x in E$ tel que
$
  forall y in E, scl(u(y), x) = scl(y, z_x)
$
On pose alors
$
  u^* : func(E, E, x, z_x) in cal(L)(E)
$
Qui est l'unique adjoit de $u$. On le caractérise alors par
$
  forall x, y in E, scl(x, u(y)) = scl(u^* (x), y)
$

On a alors
- Pour tout $u in cal(L)(E), u^*^* = u$ #h(1fr)

- Pour toute BON $e$ de $E$
  $
    cal(M)_e (u^*) = cal(M)_e (u)^TT
  $

- Pour $u in cal(L)(E)$
  $
    ker (u^*) &= im (u)^perp \
    im (u^*) &= ker (u)^perp \
    "rg" u^* &= u
  $

- Pour $u in cal(L)(E)$
  $
    ker (u^* compose u) = ker u \
    "rg" (u^* compose u) = "rg" u
  $

- Pour tout $F$ sev de $E$ stable par $u$, $F^perp$ est stable par $u^*$

*Démonstration*

- Soit $x in E$, on pose #h(1fr)
  $
    phi_x : func(E, RR, y, scl(x, u (y)))
  $
  Par théorème de représentation on dispose d'un unique $z_x$ tel que
  $
    forall y in E, phi_x (y) = scl(z_x, y)
  $
  Soit $x, y, z in E$ et $alpha, beta in RR$
  $
    scl(alpha x + beta y, u(z)) \ = alpha scl(x, u(z)) + beta scl(y, u(z)) \
    = alpha scl(u^*(x), z) + beta scl(u^*(y), z) \
    = scl(alpha u^*(x) + beta u^*(y), z) \
    = scl(u^*(alpha x + beta y), z)
  $
  D'où par unicité 
  $
  u^*(alpha x + beta y) = alpha u^* (x) + beta u^* (y)
  $

- Les écrires

- On a $ker u subset.eq ker (u^* compose u)$. Soit $x in ker (u^* compose u)$.
  $
    scl(u^* (u(x)), x) &= 0 \
    &= scl(u(x), u(x)) \
    &= norm(u(x))^2
  $

#card("isomvec", "Isométries vectorielles", ("Maths.Algèbre.Euclidiens",))

Isométries vectorielles.

#answer

Soit $u in cal(L)(E)$, on dit que $u$ est une isométrie vectorielle (ou automorphisme orthogonal) si pour tout $x in E$
$
  norm(u(x)) = norm(x)
$

Ce qui est équivalent à
$
  forall x, y in E, scl(u(x), u(y)) = scl(x, y)
$

D'autre caractérisation équivalente des isométrie vectorielles :

- Il existe $e$ BON tel que $u(e)$ BON.
- Pour tout $e$ BON, $u(e)$ BON.
- $u^* compose u = u compose u^* = id$

On note $O(E)$ leur ensemble, qui forme un sous groupe compact de $"GL"(E)$.

On a alors

- Pour tout $u in O(E)$, $det(u) = plus.minus 1$.


*Démonstration*

- ($arrow.l.double$) Soit $x in E$ #h(1fr)
  $
    norm(u(x))^2 &= scl(u(x), u(x)) \ &= scl(x, x) = norm(x)^2
  $

- ($=>$) Soit $x, y in E$
  $
    scl(u(x), u(y)) \ = (norm(u(x + y))^2 - norm(u(x - y))^2) / 4 \
    (norm(x + y)^2 - norm(x - y)^2) / 4 \
    = scl(x, y)
  $

- Les écrires.

- $u in O(E)$
  $
    &<=> forall x, y in E, scl(u(x), u(y)) = scl(x, y) \
    &<=> forall x, y in E, scl(u^* compose u (x), y) = scl(x, y) \
    &<=> forall x, y in E, scl(u^* compose u (x) - x, y) = 0 \
    &<=> forall x in E, norm(u^* compose u(x) - x)^2 = 0
  $

- Écrire la démonstration pour $O(E)$ sous groupe de $"GL"(E)$.

- Pour tout $u in O(E)$, $norm(u)_"op" = 1$ donc $O(E)$ est borné et on montre facilement (par critère séquentiel) que $O(E)$ est fermé, donc compact.

#card("symprojortho", "Symétries et projecteurs ortogonaux", ("Maths.Algèbre.Euclidiens",))

Symétries et projecteurs ortogonaux.

#answer

Soit $(E, scl(dot, dot))$ euclidiens.

*Symmétries orthogonales*

Soit $s in cal(L)(E)$ tel que $s^2 = id$, on dit que $s$ est une symmétrie orthogonale si
$
  ker (s - id) perp ker (s + id) \ => E = ker (s - id) dperp ker(s + id)
$

Ou de manière équivalente, si $s$ est une isométrie vectorielle.

On appelle réflexion une symmétrie orthogonale par rapport à un hyperplan.

*Projecteurs orthogonaux*

Soit $p in cal(L)(E)$ tel que $p^2 = p$, on dit que $p$ est un projecteur orthogonale si
$
  ker (p - id) perp ker p \ => E = ker (p - id) dperp ker p
$

Ou de manière équivalente si $p$ est autoadjoint.

*Démonstration*

- ($=>$) Soit $s$ une symmétrie orthogonales, $x in E$, $F = ker (s - id)$
  $
    x = y + z quad quad y in F, z in F^perp \
  $
  $
    norm(s(x))^2 &= norm(s(y + z))^2 \ &= norm(y - z)^2 \
    &= norm(y)^2 + norm(-z)^2 \
    &= norm(x)^2
  $

- ($arrow.l.double$) Soit $s$ une symmétrie qui conserve la norme, et donc le produit scalaire. Soit $x in F = ker (s - id)$ et $y in G = ker (s + id)$.
  $
    scl(x, y) = scl(s(x), s(y)) = scl(x, -y) \
    scl(x, y) = 0
  $

#card("endosym", "Endomorphismes symmétriques ou autoadjoints", ("Maths.Algèbre.Euclidiens",))

Endomorphismes symmétriques ou autoadjoints.

#answer

Soit $(E, scl(dot, dot))$ euclidiens, on dit que $u in cal(L)(E)$ est autoadjoint (ou symmétrique) si $u^* = u$.

Pour toute BON $e$ (d'où symmétrique)
$
  cal(M)_e (u) = A = A^TT in S_n (RR)
$

On note $S(E)$ leur ensemble
$
  S = ker ((u |-> u^*) - id)
$
Qui est donc un sev de $cal(L)(E)$ et $dim S(E) = (n (n+1)) / 2$.
