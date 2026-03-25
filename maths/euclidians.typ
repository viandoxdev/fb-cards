#import "/cards.typ": *

#show: setup

//![FLASHBANG HEADER]

#import "/utils.typ": *
#import "@preview/tiptoe:0.3.1"
#import "@preview/lilaq:0.4.0" as lq
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge
#import "@preview/physica:0.9.7": *

#card("fbildege", "Formes bilinéaires non dégénérées", ("Maths.Algèbre.Algèbre linéaire.Euclidiens",))

Formes bilinéaires non dégénérées.

#answer

Soit $E$ un $RR$-ev. Pour $phi : E^2 -> RR$ une forme bilinéaire on considère
$
  psi : func(E, cal(L)(E, RR), x, phi_x : y |-> phi(x, y))
$
On dit que $phi$ est non dégénérée si $psi$ est injective.

On a alors

- Si $phi$ bilinéaire symétrique positive, $phi$ est un produit scalaire sur $E$ ssi $phi$ est non dégénérée.

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

#card("idpseucl", "Identités du produit scalaire", ("Maths.Algèbre.Algèbre linéaire.Euclidiens",))

Identités du produit scalaire (polarisation, parallélogramme).

#answer

Soit $(E, scl(dot, dot))$ un $RR$-ev préhilbertien.

- (Polarisation) Pour $x, y in E$
  $
    scl(x, y) &= 1 / 2 (norm(x + y)^2 - norm(x)^2 - norm(y)^2) \
    &= 1/4 ( norm(x + y)^2 - norm(x - y)^2)
  $

- (Parallélogramme) Pour $x, y in E$
  $
    norm(x + y)^2 + norm(x - y)^2 = 2 norm(x)^2 + 2 norm(y)^2
  $

#card("partieortho", "Orthogonal d'une partie", ("Maths.Algèbre.Algèbre linéaire.Euclidiens",))

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

#card("projecsev", "Projection orthogonale sur un sev de dimension finie", ("Maths.Algèbre.Algèbre linéaire.Euclidiens",))

Projection orthogonale sur un sev de dimension finie.

#answer

Soit $(E, scl(dot, dot))$ un $RR$-ev préhilbertien et $F$ sev de $E$.

Pour tout $x in E$, il existe un unique $z in F$ tel que $norm(x - z) = d(x, F)$, de plus si $(e_1, dots, e_d)$ est une BON de $F$
$
  z = sum_(j = 1)^d scl(x, e_j) e_j quad quad x - z in F^perp
$
Ainsi
$
  d(x, F)^2 &= norm(x - z)^2 \ &= norm(x)^2 - norm(z)^2 \
  &= norm(x)^2 - sum_(j = 1)^d scl(x, e_j)^2
$

// NOTE: M320 matrice d'une application bilinéaire

#card("exinegdetfam", "Exercice : Inégalité sur le déterminant d'une famille de vecteurs", ("Maths.Algèbre.Algèbre linéaire.Euclidiens",))

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

+ Sinon, on pose $w = (w_1, dots, w_n)$ la BON obtenue par Gram-Schmidt sur $x = (x_1, dots, x_n)$
  $
    forall i in [|1, n|], x_i &= sum_(k = 1)^n scl(x_i, w_k) w_k \ 
    &= sum_(k = i)^n scl(x_i, w_k) w_k \
  $
  $
    abs(det_e (x)) &= abs(det_w (x)) \ &= product_(k = 1)^n scl(x_k, w_k) \
    &<= product_(k = 1)^n norm(x_k)
  $
  Car $cal(M)_w (x) in T_n^+ (RR)$.

#card("thmrepr", "Théorème de représentation", ("Maths.Algèbre.Algèbre linéaire.Euclidiens",))

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

#card("adjendo", "Adjoint d'un endomorphisme", ("Maths.Algèbre.Algèbre linéaire.Euclidiens",))

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
Qui est l'unique adjoint de $u$. On le caractérise alors par
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

- Les écrire

- On a $ker u subset.eq ker (u^* compose u)$. Soit $x in ker (u^* compose u)$.
  $
    scl(u^* (u(x)), x) &= 0 \
    &= scl(u(x), u(x)) \
    &= norm(u(x))^2
  $

#card("isomvec", "Isométries vectorielles", ("Maths.Algèbre.Algèbre linéaire.Euclidiens",))

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

D'autres caractérisations équivalentes des isométries vectorielles :

- Il existe $e$ BON tel que $u(e)$ BON.
- Pour tout $e$ BON, $u(e)$ BON.
- $u^* compose u = u compose u^* = id$

On note $O(E)$ leur ensemble, qui forme un sous groupe compact de $"GL"(E)$.

On a alors

- Pour tout $u in O(E)$, $det(u) = plus.minus 1$.

- Pour tout $u in O(E)$ et $F$ sev stable par $u$, $F^perp$ est stable par $u$.

- Pour tout $u in O(E)$ et $F$ sev stable par $u$, $tilde(u)$ induit par $u$ sur $F$ est dans $O(F)$.

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

- Les écrire.

- $u in O(E)$
  $
    &<=> forall x, y in E, scl(u(x), u(y)) = scl(x, y) \
    &<=> forall x, y in E, scl(u^* compose u (x), y) = scl(x, y) \
    &<=> forall x, y in E, scl(u^* compose u (x) - x, y) = 0 \
    &<=> forall x in E, norm(u^* compose u(x) - x)^2 = 0
  $

- Écrire la démonstration pour $O(E)$ sous groupe de $"GL"(E)$.

- Pour tout $u in O(E)$, $norm(u)_"op" = 1$ donc $O(E)$ est borné et on montre facilement (par critère séquentiel) que $O(E)$ est fermé, donc compact.

- On a $u in O(E)$ et $u(F) subset.eq F$, or comme $u in "GL"(E)$, $u(F) = F$ par argument dimensionnel.

  Ainsi $u^(-1) (F) = u^* (F) = F$, et $F$ est stable par $u^*$, donc $F^perp$ est stable par $u^*^* = u$.

- Pour tout $x, y in F$
  $
    scl(tilde(u)(x), tilde(u)(y)) &= scl(u(x), u(y)) \ &= scl(x, y)
  $

#card("symprojortho", "Symétries et projecteurs orthogonaux", ("Maths.Algèbre.Algèbre linéaire.Euclidiens",))

Symétries et projecteurs orthogonaux.

#answer

Soit $(E, scl(dot, dot))$ euclidiens.

*Symétries orthogonales*

Soit $s in cal(L)(E)$ tel que $s^2 = id$, on dit que $s$ est une symétrie orthogonale si
$
  ker (s - id) perp ker (s + id) \ => E = ker (s - id) dperp ker(s + id)
$

Ou de manière équivalente, si $s$ est une isométrie vectorielle.

On appelle réflexion une symétrie orthogonale par rapport à un hyperplan.

*Projecteurs orthogonaux*

Soit $p in cal(L)(E)$ tel que $p^2 = p$, on dit que $p$ est un projecteur orthogonal si
$
  ker (p - id) perp ker p \ => E = ker (p - id) dperp ker p
$

Ou de manière équivalente si $p$ est autoadjoint.

*Démonstration*

- ($=>$) Soit $s$ une symétrie orthogonale, $x in E$, $F = ker (s - id)$
  $
    x = y + z quad quad y in F, z in F^perp \
  $
  $
    norm(s(x))^2 &= norm(s(y + z))^2 \ &= norm(y - z)^2 \
    &= norm(y)^2 + norm(-z)^2 \
    &= norm(x)^2
  $

- ($arrow.l.double$) Soit $s$ une symétrie qui conserve la norme, et donc le produit scalaire. Soit $x in F = ker (s - id)$ et $y in G = ker (s + id)$.
  $
    scl(x, y) = scl(s(x), s(y)) = scl(x, -y) \
    scl(x, y) = 0
  $

#card("endosym", "Endomorphismes symétriques ou autoadjoints", ("Maths.Algèbre.Algèbre linéaire.Euclidiens",))

Endomorphismes symétriques ou autoadjoints.

#answer

Soit $(E, scl(dot, dot))$ euclidiens, on dit que $u in cal(L)(E)$ est autoadjoint (ou symétrique) si $u^* = u$.

Pour toute BON $e$ (d'où symétrique)
$
  cal(M)_e (u) = A = A^TT in S_n (RR)
$

On note $S(E)$ leur ensemble
$
  S = ker ((u |-> u^*) - id)
$
Qui est donc un sev de $cal(L)(E)$ et $dim S(E) = (n (n+1)) / 2$.

#card("thspectral", "Théorème spectral", ("Maths.Algèbre.Algèbre linéaire.Euclidiens",))

Théorème spectral.

#answer

Soit $A in M_n (RR)$, il y a équivalence entre

+ $A in S_n (RR)$.

+ $A$ est diagonalisable dans une BON.

+ $E$ s'écrit comme une somme directe orthogonale des sous espaces propres de $A$.

*Démonstration*

On suppose $A in S_n (RR)$

- Montrons d'abord que $"Sp"_CC (A) subset.eq RR$.

  Soit $lambda in "Sp"_CC (A), Z in CC^n \\ {0}$ vecteur propre associé. #h(1fr)
  $
    A Z &= lambda Z \
    overline(Z)^TT A Z &= lambda overline(Z)^TT Z = lambda sum_(k = 1)^n abs(z_k) in lambda RR^*_+ \
    overline(overline(Z)^T A Z) &= Z^TT overline(A) overline(Z) = Z^TT A overline(Z) in cal(M)_(11) (CC) \
    &= (Z^T A overline(Z))^TT = overline(Z)^TT A^TT Z \
    &= overline(Z)^TT A Z in RR
  $
  D'où $lambda in RR$ et $chi_A$ est scindé sur $RR$.

- Par récurrence sur $n$.

  Le cas $n = 1$ est évident.

  On suppose le résultat pour tout $k <= n in NN$, et $A in S_(n+1) (RR)$.

  Comme $chi_A$ est scindé sur $RR$, on dispose de $lambda_1 in RR in "Sp" (A)$.

  Ainsi $E_lambda_1 (A) = F$ est stable par $A$, donc $F^perp$ aussi.

  En considérant la bonne BON on a alors
  $
    P A P^T = mat(lambda_1 I_m, 0; 0, tilde(A)) = (P A P^T)^TT \
    tilde(A) = tilde(A)^TT in S_n (RR)
  $
  Et on conclut par hypothèse de récurrence.

#card("calcvpps", "Expression des valeurs propres avec le produit scalaire", ("Maths.Algèbre.Algèbre linéaire.Euclidiens",))

Expression des valeurs propres avec le produit scalaire.

#answer

Pour $u in S(E)$, $(E, scl(dot, dot))$ euclidien, on note $lambda_1 <= dots.c <= lambda_n$ le spectre ordonné (avec multiplicité) de $u$.

Par le théorème spectral on dispose d'une BON de vecteurs propres $(e_1, dots, e_n)$.

- Pour tout $x in E$ #h(1fr)
  $
    x = sum_(k = 1)^n x_k e_k \
    scl(u(x), x) = sum_(k = 1)^n lambda_k x_k^2 \
    norm(u(x))^2 = sum_(k = 1)^n lambda_k^2 x_k^2 \
  $

- Pour les valeurs propres extrêmes
  $
    lambda_1 = min_(x in SS(0, 1)) scl(u(x), x) \
    lambda_n = max_(x in SS(0, 1)) scl(u(x), x) \
  $

- Pour $k in [|1, n|]$
  $
    lambda_k &= min_(F "sev" \ dim F = k) ( max_(x in F inter SS(0, 1)) scl(u(x), x)) \
    &= max_(G "sev" \ dim G = n - k + 1) (min_(x in G inter SS(0,1)) scl(u(x), x))
  $

- Et de plus
  $
    norm(u)_"op" = rho = max_(lambda in "Sp"(u)) abs(lambda)
  $

*Démonstration*

- Pour tout $x in E$ #h(1fr)
  $
    x = sum_(k = 1)^n x_k e_k \
    scl(u(x), x) = sum_(k = 1)^n lambda_k x_k^2
  $
  Ainsi
  $
    lambda_1 norm(x)^2 <= scl(u(x), x) <= lambda_n norm(x)^2
  $

- On en déduit
  $
    lambda_1 = min_(x in SS(0, 1)) scl(u(x), x) \
    lambda_n = max_(x in SS(0, 1)) scl(u(x), x) \
  $

- En notant $F_k = "Vect"(e_1, dots, e_k) = G_k^perp$. Pour tout $x in F_k inter SS(0, 1)$
  $
    scl(u(x), x) = sum_(i = 1)^k lambda_i x_i^2 \
    lambda_1 <= scl(u(x), x) <= lambda_k
  $
  Et pour tout $x in G_k inter SS(0,1)$
  $
    scl(u(x), x) = sum_(i = k+1)^n lambda_i x_i^2 \
    lambda_(k+1) <= scl(u(x), x) <= lambda_n
  $

- Ainsi pour tout $k in [|1, n|]$, et $F$ sev de dimension $k$, par argument dimensionnel, on dispose de $x in F inter G_(k - 1) inter SS(0, 1)$
  $
    lambda_k <= scl(u(x), x) \
    lambda_k <= max_(x in F inter SS(0, 1)) scl(u(x), x)
  $
  D'où (atteint en $F_k$)
  $
    lambda_k = min_(F "sev" \ dim F = k) ( max_(x in F inter SS(0, 1)) scl(u(x), x))
  $

- Et de même :
  $
    lambda_k = max_(G "sev" \ dim G = n - k + 1) (min_(x in G inter SS(0,1)) scl(u(x), x))
  $

- On a aussi
  $
    norm(u(x))^2 = sum_(k = 1)^n lambda_k^2 x_k^2
  $
  Donc si $rho = max_(lambda in "Sp" (u)) abs(lambda) = max(abs(lambda_1), abs(lambda_n))$
  $
    norm(u(x))^2 <= rho^2 norm(x)^2
  $
  Avec égalité pour $x = e_1$ ou $x = e_2$ d'où
  $
    norm(u)_"op" = rho = max_(lambda in "Sp"(u)) abs(lambda)
  $

#card("endoautopos", "Endomorphismes autoadjoints positifs", ("Maths.Algèbre.Algèbre linéaire.Euclidiens",))

Endomorphismes autoadjoints positifs.

#answer

Soit $u in S(E)$, $(E, scl(dot, dot))$ euclidien, on dit que $u$ est autoadjoint positif si
$
  forall x in E, space scl(u(x), x) >= 0
$
Et on dit que $u$ est autoadjoint défini positif si
$
  forall x in E\\{0}, space scl(u(x), x) > 0
$
On note $S^+ (E)$ et $S^(++) (E)$ leurs ensembles respectifs.

Topologiquement :

- $S^+ (E)$ et $S^(++) (E)$ sont convexes.
- $S^+ (E)$ est fermé.
- $S^(++) (E)$ est dense dans $S^+ (E)$.

Et pour $u in S(E)$, on a équivalence entre

- + $u in S^+(E)$
  + $"Sp"(u) subset.eq RR_+$

- + $u in S^(++)(E)$
  + $"Sp"(u) subset.eq RR^*_+$

On en déduit
- $S^(++) (E) = S^+(E) inter "GL"(E)$.

Et de plus

- Pour tout $u in S^+ (E)$
  $
    forall x in E, scl(u(x), x) = 0 <=> u(x) = 0
  $

- Pour tout $A in S_n^+ (RR)$, pour tout $i in [|1,n|]$
  $
    a_(i i) = E_i^TT A E_i >= 0
  $

- Pour $A in S_n^+ (RR)$
  $
    0 <= det (A) <= product_(k = 1)^n a_(k k)
  $

Matriciellement, pour $A in S_n (RR)$, on regarde le signe de $X^TT A X$.

*Démonstration*

- $S(E)$ est convexe car un sev, puis l'écrire. #h(1fr)

- On remarque que
  $
    S^+ (E) = inter.big_(x in E) (u |-> scl(u(x), x))^(-1) (RR^+)
  $

- Soit $u in S^+(E)$ , pour $k >= N in NN^*$ on pose
  $
    u_k = u + 1/k id in S^(++)(E)
  $
  Pour tout $x in E \\ {0}$
  $
    scl(u_k(x), x) = underbrace(scl(u(x), x), >= 0) + underbrace(1/k norm(x)^2, > 0)
  $
  Et $u_k tends(k -> oo)u $.

- (i $=>$ ii) Soit $lambda in "Sp"(u)$ et $x$ vecteur propre associé.
  $
    lambda norm(x)^2 = scl(u(x), x) >= 0
  $
  (ii $=>$ i) Soit $x in E$
  $
    x = sum_(k = 1)^n x_k e_k \
    scl(u(x), x) = sum_(k = 1)^n underbrace(lambda_k x_k^2, >= 0) >= 0
  $

- La même avec des inégalités strictes.

- Le sens indirect est évident. Par théorème spectral
  $
    x = sum_(k = 1)^n x_k e_k \
    scl(u(x), x) = sum_(k = 1)^n underbrace(lambda_k x_k^2, >= 0) = 0 \
    forall k in [|1, n|], space lambda_k x_k = 0 \
    u(x) = sum_(k = 1)^n lambda_k x_k e_k = 0
  $

- Comme $"Sp"(A) subset.eq RR_+$, $det(A) >= 0$.

  On peut écrire $A = M^TT M$ avec
  $
    M = (C_1 space dots.c space C_n) \
    A = M^TT M = G(C_1, dots, C_n) \
  $
  $
    det(A) &= det(M)^2 <= product_(k = 1)^n underbrace(norm(C_k)^2, scl(C_k, C_k)) \
    &= product_(k = 1)^n a_(k k)
  $
  (On utilise un exercice ?)

// TODO: Vérifier

#card("decompensympos", "Décomposition des Endomorphismes symétriques positifs", ("Maths.Algèbre.Algèbre linéaire.Euclidiens",))

Décomposition des Endomorphismes symétriques positifs.

#answer

Pour $S in M_n (RR)$

- $S in S_n^+(RR)$ ssi il existe $A in M_n (RR)$ tel que
  $
    S = A^TT A
  $

- $S in S_n^(++)(RR)$ ssi il existe $A in "GL"_n (RR)$ tel que
  $
    S = A^TT A
  $

*Démonstration*

- ($arrow.l.double$) Soit $A in M_n (RR)$ #h(1fr)
  $
    (A^TT A)^TT = A^TT A in S_n (RR) \
  $
  Et pour tout $X in RR^n$
  $
    X^TT A^TT A X &= (A X)^TT (A X) \ &= norm(A X)^2 >= 0
  $
  Et si $A in "GL"_n (RR)$, pour tout $X in RR^n \\ {0}$
  $
    X in.not ker A => norm(A X)^2 > 0
  $

- ($=>$) Soit $S in S_n^+ (RR)$
  $
    S = P^TT underbrace(dmat(lambda_1, dots.down, lambda_n), D) P
  $
  Avec $lambda_1, dots, lambda_n >= 0$. On peut alors poser
  $
    Delta = dmat(sqrt(lambda_1), dots.down, sqrt(lambda_n)) quad quad Delta^TT Delta = D
  $
  Ainsi
  $
    S &= P^TT D P = P^TT Delta^TT Delta P \
    &= (Delta P)^TT underbrace((Delta P), A) = A^TT A
  $
  Et si de plus $S in S^(++)_n (RR)$, $Delta in "GL"_n (RR)$ et $A in "GL"_n (RR)$.

#card("matgramm", "Matrices de Gram", ("Maths.Algèbre.Algèbre linéaire.Euclidiens",))

Matrices de Gram.

#answer

Soit $(E, scl(dot, dot))$ un euclidien de dimension $n$ et $x_1, dots, x_p in E$.

On appel matrice de Gram des $x_1, dots, x_p$
$
  G(x_1, dots, x_p) = (scl(x_i, x_j))_(1 <= i, j <= p)
$

On a les propriétés suivantes

- $G(x_1, dots, x_p) in S_p^+ (RR)$.

- $"rg" G(x_1, dots, x_p) = "rg" (x_1, dots, x_p)$

- Avec $e = (e_1, dots, e_n)$ BON et $A = cal(M)_e (x_1, dots, x_n) in cal(M)_(n p) (RR)$
  $
    G(x_1, dots, x_p) = A^TT A
  $

*Démonstration*

- Tout se montre à partir du 3#super[e] point.

  $A = cal(M)_e (x_1, dots, x_p) = (C_1 space dots.c space C_p)$ avec $C_k = cal(M)_e (x_k)$.

  Donc pour tout $i, j in [|1, p|]$
  $
    scl(x_i, x_j) = C_i^TT C_j = (A^TT A)_(i j)
  $
  D'où $G in S_n^+ (RR)$ et comme $ker A^TT A = ker A$ on a le rang.

// NOTE: Exercices M329-330

#card("reducisomvec", "Réduction des isométries vectorielles", ("Maths.Algèbre.Algèbre linéaire.Euclidiens",))

Réduction des isométries vectorielles.

#answer

*Dimension 2*

Pour tout $u in O(E)$ où $(E, scl(dot, dot))$ euclidien de dimension $2$ et $e = (e_1, e_2)$ BON
$
  cal(M)_e (u) = A = mat(cos theta, - epsilon sin theta; sin theta, epsilon cos theta) \
  theta in RR quad quad epsilon = det u in {-1, 1}
$

- Si $A in "SO"_2 (RR)$, $u$ est une rotation d'angle $theta$, et $A$ ne dépend pas de la BON directe choisie.
 
- Si $A in O^-_2 (RR)$, $u$ est une réflexion d'angle $theta / 2$ et $A$ ne dépend pas de la BON directe choisie.

Ainsi pour $u in O(E)$ et $e$ BON tel que $cal(M)_e (u) = R_theta$ 
$
  R_theta = mat(cos theta, -sin theta; sin theta, cos theta)
$

- Pour tout BON f de même orientation que $e$
  $
    cal(M)_f (u) = R_theta
  $
- Pour tout BON f d'orientation opposée
  $
    cal(M)_f (u) = R_(-theta)
  $

*Dimension quelconque*

Soit $u in O(E)$, avec $dim E = n$, il existe $e$ BON, $p, q, r in NN$ tels que $p + q + 2 r = n$ et $theta_1, dots, theta_r in RR$ tels que

$
  cal(M)_e (u) = dmat(I_p, -I_q, R_theta_1, dots.down, R_theta_r)
$

Si $u in "SO"(E)$, $q = 0$.

On en déduit que $"SO"(E)$ est connexe par arcs.

*Démonstration*

Calculs.

- Pour $f$ directe, $P = cal(M)_e (f) in "SO"_2 (RR)$ #h(1fr)
  $
    cal(M)_f (u) &= P R_theta P^(-1) = R_alpha R_theta R_(-alpha) \
    &= R_theta
  $

- Pour $f$ indirecte, $P = cal(M)_e (f) in O^-_2 (RR)$
  $
    P = P^(-1)
    R_theta P in O^-_2 (RR) \
    (R_theta P)^2 = I_2 \
    P R_theta P = P R_theta P^(-1) = R_(-theta) = cal(M)_f (u)
  $

- Par récurrence sur $n = dim E$ :
  - Si $1 in "Sp" u$ OK.
  - Si $-1 in "Sp" u$ OK.
  - Sinon on montre que $"Sp" u = emptyset$ par conservation de la norme, en prenant un vecteur propre quelconque.

    Or comme $E$ est un $RR$-ev, $u$ admet un plan stable, et on peut induire dessus, et il ne s'agit pas d'une réflexion car pas de valeurs propres.

#card("identso", "Identification d'une matrice de rotation en dimension 3", ("Maths.Algèbre.Algèbre linéaire.Euclidiens",))

Identification d'une matrice de rotation en dimension 3.

#answer

Soit $A = cal(M)_e (u) = (C_1 space C_2 space C_3) != I_3$.

+ Si $(C_1, C_2, C_3)$ forme une BON, $A in O_3 (RR)$.

+ Ainsi $C_3 = plus.minus C_1 and C_2$, et on peut déterminer le signe avec une seule coordonné de $C_1 and C_2$. #h(1fr)

  $
    det(C_1, C_2, C_3) = scl(C_1 and C_2, C_3)
  $

+ Pour trouver l'axe de rotation on résout $A X = X$, on trouve $ ker u - id = "Vect"(e_1)$ avec $norm(e_1) = 1$.

+ Pour l'angle : $tr(u) = tr(A) = 1 + 2 cos theta$
  $
    cos theta = (tr(A) - 1) / 2
  $
  Une fois l'axe orienté, on choisit $x in e_1^perp$, avec $e_2 = x / norm(x)$ et $e_3 = e_1 and e_2$. Ainsi
  $
    u(e_2) = cos theta e_2 + sin theta e_3 \
    e(x) = cos theta x + sin theta e_1 and x
  $
  Donc le signe de $sin theta$ est donné par $scl(u(x), e_1 and x)$.

#card("exrefengon", "Exercice : les réflexions engendrent le groupe orthogonal", ("Maths.Exercice.Euclidiens",))

Montrer que les réflexions engendrent $O_n (RR)$.

#answer

Matriciellement :

Soit $u in O(E)$, on dispose de $e$ BON tel que
$
  cal(M)_e (u) = dmat(I_p, -I_q, R_theta_1, dots.down, R_theta_r)
$
On pose les réflexions suivantes
$
  S_k = mat(I_k;,-1;,,I_(n - k - 1)) \
  T_k (theta) = mat(I_k;,cos theta, sin theta;,sin theta, -cos theta;,,,I_(n - k - 2))
$
Ainsi
$
  A_k (theta) &= dmat(I_k, R_theta, I_(n - k - 2)) \
  &= T_k (theta) S_(k + 1)
$
D'où
$
  cal(M)_e (u) =& S_(p + 1) dot dots.c dot S_(p + q) \
  dot & A_(p + q + 1) (theta_1) dot dots.c dot A_(p + q + 2 r - 1) (theta_r) \
  =& product_(k = p + 1)^(p + q) S_k dot product_(k = 1)^r (T_(p + q + 2r - 1) (theta_k) S_(p + q + 2 r))
$

#card("raccarendos", "Racine carrée d'une matrice symétrique positive", ("Maths.Algèbre.Algèbre linéaire.Euclidiens",))

Racine carrée d'une matrice symétrique positive.

#answer

Soit $S in S_n^+ (RR)$, il existe une unique $R in S_n^+ (RR)$ tel que
$
  S = R^2
$

*Démonstration*

- Existence : par le théorème spectral on dispose de $P in O_n (RR)$ tel que #h(1fr)
  $
    S = P^TT underbrace(dmat(lambda_1, dots.down, lambda_n), D) P \
  $
  Avec $lambda_1, dots, lambda_n >= 0$ car $S in S_n^+ (RR)$.
  $
    Delta = dmat(sqrt(lambda_1), dots.down, sqrt(lambda_n)) \
    R = P Delta P^TT in S_n^+ (RR) \
    R^2 = P Delta underbrace(P^TT P, I_n) Delta P^TT = P Delta^2 P^TT = S
  $

- Unicité : soit $r in S^+ (E)$ tel que $r^2 = s in S^+ (E)$.

  Ainsi $r$ et $s$ commutent, notons
  $
    E = bdperp_(lambda in "Sp"(s)) E_lambda (s)
  $
  Or pour tout $lambda in "Sp"(s)$, $r$ stabilise $E_lambda (s)$ (car ils commutent).

  Posons $tilde(r)$ l'induit, qui est diagonalisable car $r$ l'est.
  $
    cal(M)_tilde(e) (tilde(r)) = dmat(mu_1, dots, mu_d) \ tilde(r)^2 = tilde(s) = lambda id
  $
  Or $"Sp"(tilde(r)) subset.eq "Sp"(r) subset.eq R_+$, d'où $mu_k = sqrt(lambda)$.

  Alors $tilde(r) = sqrt(lambda) id$, donc $r$ est unique sur chaque $E_lambda(s)$, et est donc unique.

// NOTE: Analogies M334

#card("decomppolaire", "Décomposition polaire d'Endomorphismes", ("Maths.Algèbre.Algèbre linéaire.Euclidiens",))

Décomposition polaire d'Endomorphismes.

#answer

Soit $A in M_n (RR)$, il existe $(R, U) in S_n^+ (RR) times O_n (RR)$ tel que
$
  A = U R quad quad R = sqrt(A^TT A)
$
Et si $A in "GL"_n (RR)$, $R in S_n^(++) (RR)$ et cette décomposition est unique.

*Démonstration*

- Unicité : Soit $A in "GL"_n (RR)$, si $A = U R$ avec $U in O_n (RR)$ et $R in S_n^(++) (RR)$, alors #h(1fr)
  $
    A^TT A = underbrace(R^TT, R) underbrace(U^TT U, I_n) R = R^2
  $
  Donc $R = sqrt(A^TT A)$ qui est unique car dans $S_n^(++) (RR)$.

  Ainsi
  $
      U = A R^(-1)
  $
  Qui est aussi unique.

- Existence : Soit $A in "GL"_n (RR)$. Comme $A^TT A in S_n^(++) (RR)$, on dispose de $R in S_n^(++) (RR)$ tel que
  $
    A^TT A = R^2
  $
  Posons alors
  $
    U = A R^(-1) \
    U^TT U = (R^(-1))^TT underbrace(A^TT A, R^2 = R^TT R) R^(-1) = I_n
  $

- Cas non inversible :
  $
    phi : func(O_n (RR) times S_n^(++) (RR), "GL"_n (RR), (U, R), U R)
  $
  Est une bijection continue (car restriction de $(M, N) |-> M N$ linéaire en dimension finie).

  Et de plus $phi^(-1)$ est continue : par critère séquentiel
  $
    (A_k)_k in "GL"_n (RR)^NN tends(k -> oo) B in "GL"_n (RR) \
    (U_k, R_k) = phi^(-1) (A_k) \
    (W, S) = phi^(-1) (B)
  $
  Comme $(U_k)_k in O_n (RR)^NN$ qui est compact, $(U_k)_k$ dispose d'une valeur d'adhérance $V = lim_(k -> oo) U_psi(k) in O_n (RR)$.
  $
    (R_k)_k in S_n^(++) (RR)^NN subset.eq underbrace(S_n^+ (RR), "fermé")^NN \
    R_psi(k) = U^TT_psi(k) A_psi(k) tends(k -> oo) V^TT B in S_n^+ (RR)
  $
  Ainsi
  $
    B = underbrace(V, in O_n (RR)) dot underbrace(V^TT B, in S_n^(++) (RR))
  $
  Donc par unicité de la décomposition polaire $V = W$, qui est donc l'unique valeur d'adhérance de la suite :
  $
    lim_(k -> oo) U_k = W
  $
  Par le même raisonnement, $R_k tends(k -> oo) W^TT B = S$, d'où la continuité.

  On peut donc finalement prendre une suite
  $
    (A_k)_k in "GL"_n (RR)^NN tends(k -> oo) B in M_n (RR) \
    (U_k, R_k) = phi^(-1) A_k
  $
  Et on refait la même chose :
  $
    B = underbrace(V, in O_n (RR)) dot underbrace(V^TT B, in S_n^(++) (RR))
  $
  Avec unicité de $R$ car $B^TT B = R^2$.

#card("normadj", "Norme et adjoint d'un endomorphisme", ("Maths.Algèbre.Algèbre linéaire.Euclidiens",))

Norme et adjoint d'un endomorphisme.

#answer

Soit $(E, scl(dot, dot))$ un euclidien.

- Pour tout $x in E$ #h(1fr)
  $
    norm(x) = max_(a in SS(0, 1)) scl(a, x)
  $
- Pour tout $u in cal(L)(E)$
  $
    norm(u)_"op" = norm(u^*)_"op"
  $
- Pour tout $u in cal(L)(E)$
  $
    norm(u)_"op"^2 = max_(lambda in "Sp" (u^* compose u)) lambda
  $

*Démonstration*

- Par Cauchy-Schwartz, pour tout $a in SS(0, 1)$
  $
    scl(a, x) <= norm(a) dot norm(x) = norm(x)
  $
  Et pour $a = x / norm(x)$
  $
    scl(a, x) = norm(x)^2 / norm(x) = norm(x)
  $

- Soit $u in cal(L)(E)$
  $
    norm(u)_"op" &= max_(x in SS(0,1)) norm(u(x)) \
    &= max_(x in SS(0,1)) max_(a in SS(0,1)) scl(a, u(x)) \
    &= max_(a in SS(0,1)) max_(x in SS(0,1)) scl(u^*(a), x) \
    &= max_(a in SS(0,1)) norm(u^* (a)) = norm(u^*)_"op"
  $

- Soit $u in cal(L)(E)$
  $
    norm(u)^2_"op" &= max_(x in SS(0,1)) norm(u(x))^2 \
    &= max_(x in SS(0,1)) scl(u(x), u(x)) \
    &= max_(x in SS(0,1)) scl(u^* compose u(x), x) \
    &= max_(lambda in "Sp"(u^* compose u)) lambda
  $

#card("exennomopleto", "Exercice : endomorphisme de norme triple inférieur à un", ("Maths.Exercice.Euclidiens",))

Soit $u in cal(L)(E)$ avec $(E, scl(dot, dot))$ euclidien tel que $norm(u)_"op" <= 1$.

+ Montrer que #h(1fr)
  $
    E = ker (u - id) dperp im (u - id)
  $
+ En déduire que
  $
    w_k = 1/k sum_(j = 0)^(k - 1) u^j
  $
  Converge vers le projecteur orthogonal sur $ker (u - id)$.

#answer

+ On remarque que
  $
    im (u - id)^perp &= ker (u - id)^* \
    &= ker (u^* - id)
  $
  Il suffit donc de montrer que
  $
    ker (u - id) = ker (u^* - id)
  $

  Soit $x in ker(u^* - id)$
  $
    &norm(u(x) - x)^2 \ 
    =& norm(u(x))^2 - 2scl(x, u(x)) + norm(x)^2 \
    =& norm(u(x))^2 - 2scl(underbrace(u^*(x), x), x) + norm(x)^2 \
    =& norm(u(x))^2 - norm(x)^2 <= 0 \
    =& 0
  $
  D'où $ker (u^* - id) subset.eq ker (u - id)$, et comme 
  $
  norm(u^*)_"op" = norm(u)_"op" <= 1
  $
  On à l'autre sens.

+ Pour tout $x in ker (u - id)$ et $k in NN$
  $
    w_k (x) = 1/k sum_(j = 0)^(k - 1) u^j (x) = 1/k sum_(j = 0)^(k - 1) x = x
  $
  Et pour tout $x in ker(u - id)^perp = im(u - id)$, on dispose de $y in E$
  $
    x = u(y) - y
  $
  $
    w_k (x) &= (w_k compose (u - id)) (y) \
    &= (u^k (y) - y) / k tends(k -> oo) 0
  $
  On a la CVS, et on peut en déduire la CVU en appliquant la CVS sur une BON.

#card("prodmatsym", "Produit de matrices symétriques", ("Maths.Algèbre.Algèbre linéaire.Euclidiens",))

Produit de matrices symétriques.

#answer

Soit $A in S_n^(++)(RR)$ et $B in S_n (RR)$, alors $A B$ est diagonalisable, et si $B in S_n^+ (RR)$, $"Sp"(A B) subset.eq RR_+$.

*Démonstration*

On note $R in S_n^(++)(RR)$ la racine carrée de $A$.
$
  A B = R underbrace((R B R^TT), S in S_n (RR)) R^(-1)
$
Donc $S$ est diagonalisable et $A B$ aussi

Si $B in S_n^+ (RR)$, $S in S_n^+ (RR)$ :
$
  X^TT S X = (R X)^TT B (R X) >= 0
$

#card("exendopreortho", "Exercice : endomorphisme qui préserve l'orthogonalité", ("Maths.Exercice.Euclidiens",))

Soit $u in cal(L)(E)$ où $(E, scl(dot, dot))$ euclidien  tel que
$
  forall x, y in E, scl(x, y) = 0 \ => scl(u(x), u(y)) = 0
$
Montrer que $u = alpha v$ avec $v in O(E)$ et $alpha in RR$.

#answer

Soit $e = (e_1, dots, e_n)$ une BON, ainsi $(u(e_1), dots, u(e_n))$ est une famille orthogonale.

Pour tout $i != j in [|1, n|]$
$
  scl(e_i + e_j, e_i - e_j) &= norm(e_i)^2 - norm(e_j)^2 \
  &= 0 \
$
Donc
$
  scl(u(e_i) + u(e_j), u(e_i) - u(e_j)) = 0 \
  norm(u(e_i))^2 = norm(u(e_j))^2
$

On pose $alpha = norm(e_1)$

- Si $alpha = 0$, $u = 0 = 0 id$ et $id in O(E)$.

- Sinon on pose $v = 1 / alpha u$ et $(v(e_1), dots, v(e_n))$ est une BON, donc $v in O(E)$.

#card("expresprodfam", "Exercice : isométries vectorielles et conservation du produit scalaire entre familles de vecteurs", ("Maths.Exercice.Euclidiens",))

Soit $(E, scl(dot, dot))$ un euclidien de dimension $n$, $(a_i)_i, (b_i)_i in E^n$ deux familles de vecteurs.

+ Montrer l'équivalence suivante
  + $forall i, j in [|1, n|], space scl(a_i, a_j) = scl(b_i, b_j)$.
  + Il existe une isométrie vectorielle $phi$ tel que $forall i in [|1, n|], space phi(a_i) = b_i$.

+ Pour $E = RR^n$ et $k in NN^*$, $u_1, dots, u_k, v_1, dots, v_k in RR^n$ des vecteurs, on suppose que pour tout $i, j in [|1, k|]$
  $
    scl(u_i, u_j) = scl(v_i, v_j)
  $
  Montrer qu'il existe $W in O_n (RR)$ tel que pour tout $i in [|1, k|]$, $v_k = W u_k$.

+ Soit $A, B in M_n (RR)$, montrer que $A^TT A = B^TT B$ ssi il existe $P in O_n (RR)$ tel que $A = P B$.

#answer

+ Un des sens est évident car les isométries vectorielles conservent le produit scalaire.

  - On suppose d'abord que $(a_1, dots, a_n)$ est une base. On pose alor $phi$ l'unique application linéaire qui peut marcher.

    Soit $x in E$ #h(1fr)
    $
      x = sum_(k = 1)^n x_k a_k
    $
    $
      norm(phi(x))^2 &= sum_(1 <= i, j <= n) x_i x_j scl(b_i, b_j) \
      &= sum_(1 <= i, j <= n) x_i x_j scl(a_i, a_j) \
      &= norm(x)^2
    $
    D'où $phi in O(E)$.

  - Sinon, quitte à renuméroter, on suppose $(a_1, dots, a_k)$ libre.

    Soit $j in [|k+1, n|]$.
    $
      a_j = sum_(i = 1)^k lambda_i a_i \
    $
    Ainsi (en développant)
    $
      norm(b_j - sum_(i = 1)^k lambda_i b_i)^2 = underbrace(norm(a_j - sum_(i = 1)^k lambda_i a_i)^2, 0)
    $
    En notant $F = "Vect"(a_1, dots, a_k)$ et $G = "Vect"(b_1, dots, b_n)$, par le cas 1, on dispose de 
    $
    phi_0 : func(F, G, a_i, b_i) "pour" i in [|1,k|]
    $
    Qu'on étend en $phi in O(E)$ (en posant des BON).

+ Il s'agit de la même chose, le fait qu'il peut y avoir plus de $n$ vecteurs n'est pas dérangeant car on extrait une famille libre dans tous les cas.

+ Soit $A, B in M_n (RR)$
  $
    A &= (a_1 space dots.c space a_n) \
    B &= (b_1 space dots.c space b_n) \
    A^TT A &= (scl(a_i, a_j))_(i j) \
    &= B^TT B = (scl(b_i, b_j))_(i j)
  $
  Par le 1 on dispose donc de $P in O_n (RR)$ tel que
  $
    forall k in [|1, n|], b_k = P a_k
  $
  D'où
  $
    A = P^(-1) B
  $

#card("actionparcongr", "Action par congruence", ("Maths.Algèbre.Algèbre linéaire.Euclidiens",))

Action par congruence.

#answer

Pour tout $P in "GL"_n (RR)$ on pose
$
  rho_P : func(S_n (RR), S_n (RR), M, P M P^TT)
$

- Pour tout $P, Q in "GL"_n (RR)$ #h(1fr)
  $
    rho_P compose rho_Q = rho_(P Q)
  $

- Si $M in S_n^+ (RR)$ alors $rho_P (M) in S_n^+ (RR)$.

*Interpretation*

Si $phi$ une forme bilinéaire symétrique sur $E$, $e$ et $f$ des bases.
$
  A = cal(M)_e (phi) = (phi(e_i, e_j))_(i j) \
  B = cal(M)_f (phi) = (phi(f_i, f_j))_(i j) \
  B = P A P^TT
$
Avec $P = cal(M)_e (f) in "GL"_n (RR)$.

Pour tout $x, y in E$ si 
$
  X = cal(M)_e (x) quad quad Y = cal(M)_e (y) \
  X' = cal(M)_f (x) quad quad Y' = cal(M)_f (y) \
$
Alors
$
  phi(x, y) &= X^TT A Y \
  &= X'^TT B Y'
$

*Démonstration*

- L'écrire.

- Soit $M in S_n^+ (RR)$ et $X in RR^n$ #h(1fr)
  $
    X^TT P M P^TT X = (P^T X)^TT M (P^TT X) >= 0
  $

- Les écrire.

#card("coredmatsym", "Coréduction des matrices symétriques", ("Maths.Algèbre.Algèbre linéaire.Euclidiens",))

Coréduction des matrices symétriques.

#answer

Soit $A in S_n^(++) (RR)$ et $B in S_n (RR)$. Il existe $P in "GL"_n (RR)$ et $D in D_n (RR)$ tels que
$
  A = P^TT P quad quad B = P^TT D P
$

*Démonstration*

Comme $A in S_n^(++) (RR)$ on dispose de $Q in "GL"_n (RR)$ tel que 
$
A = Q^TT Q
$
On pose alors
$
B_0 = (Q^TT)^(-1) B Q^(-1) in S_n (RR)
$
Donc par théorème spectral, on dispose de $P in O_n (RR)$ et $D in D_n (RR)$ tels que 
$
  B_0 = P^TT D P
$
Ainsi
$
  B = Q^TT P^TT D P Q = (P Q)^TT D (P Q) \
  (P Q)^TT P Q = Q^TT underbrace(P^TT P, I_n) Q = A
$

// NOTE: Nouvelle interpretation du théorème spectral M338

// NOTE: Applications que j'ai pas compris M339

#card("decomsing", "Décomposition en valeurs singulières", ("Maths.Algèbre.Algèbre linéaire.Euclidiens",))

Décomposition en valeurs singulières.

#answer

Soit $A in M_(n p) (RR)$, il existe $P in O_n (RR)$, $Q in O_p (RR)$ et
$
  mu_1 >= dots >= mu_r > 0
$
tels que
$
  A = P underbrace(dmat(mu_1, dots.down, mu_r, 0), in M_(n p) (RR)) Q
$
Avec $r = "rg" A$.

*Démonstration (cas carré)*

On note $A = cal(M)_"can" (u)$ où $u in cal(L)(RR^n)$.

Soit $lambda in "Sp" (u^* compose u) \\ {0}$, $x in E_lambda = E_lambda (u^* compose u)$ vecteur propre non nul.
$
  u^* compose u (x) = lambda x != 0
$
Or $u(x) != 0$ donc
$
  u compose u^* (u(x)) = lambda u(x)
$
Et $u(x) in F_lambda = E_lambda (u compose u^*)$.

Par symétrie
$
  "Sp" (u compose u^*) \\ {0} = "Sp" (u^* compose u) \
  forall lambda in "Sp" (u compose u^*), space dim E_lambda = dim F_lambda
$
Soit un tel $lambda$ et $(e_1, dots, e_d)$ une bon de $E_lambda$. Pour tout $i, j in [|1, d|]$
$
  scl(u(e_i), u(e_j)) &= scl(u^* compose u (e_i), e_j) \
  &= lambda scl(e_i, e_j) = lambda delta_(i j)
$
Ainsi $(u(e_1), dots, u(e_d))$ est OG et $norm(u(e_i)) = sqrt(lambda)$.

On pose alors $f_i = u(e_i) / sqrt(lambda)$ BON de $F_lambda$.

Donc
$
  RR^n = (bdperp_(k in [|1,p|]) E_lambda_k) dperp ker (u^* compose u)
$
Avec
$
  lambda_1 > lambda_2 > dots.c > lambda_p > 0
$
On en extrait une BON $cal(B)$ par concatenation des $cal(B)_1, dots, cal(B)_p, cal(B)_(p+1)$.

À chaque $cal(B)_k$ on associe $cal(C)_k$ BON de $F_lambda_k$ associé.

Ainsi
$
  cal(M)_(cal(B), cal(C)) (u) = dmat(sqrt(lambda_1) I_d_1, dots.down, sqrt(lambda_p) I_d_p, 0)
$

Et les valeurs singulières de $A$ sont les racines carrées des valeurs propres non nulles de $A^TT A$ avec multiplicité.

*Démonstration (cas non carré)*

La même en introduisant $u^*$ l'endomorphisme associé à $A^TT$ (car pas adjoint tel qu'on la définit sur les endomorphismes).

#card("matcov", "Matrice de covariance", ("Maths.Algèbre.Algèbre linéaire.Euclidiens", "Maths.Probabilités"))

Matrice de covariance.

#answer

Soient $X_1, dots, X_n in LL^2$ sur $(Omega, cal(T), PP)$ ep. On appelle matrice de covariance des $X_1, dots, X_n$
$
  C &= Cov(X_1, dots, X_n) \ &= (Cov(X_i, X_j))_(i, j) in S_n^+ (RR)
$

Toute matrice de $S_n^+ (RR)$ est une matrice de covariance.

*Démonstration*

- Cas $I_n$ :

  Soient $X_1, dots, X_n$ vaiid de Rademarcher, par indépendance pour tout $i, j in [|1, n|]$ #h(1fr)
  $
    Cov(X_i, X_j) = delta_(i j)
  $
  Ainsi
  $
    I_n = Cov(X_1, dots, X_n)
  $

- Cas général :

  Soit $S in S_n^+ (RR)$, on dispose de $A in M_n (RR)$ tel que
  $
    S &= A^TT A = A^TT Cov(X_1, dots, X_n) A \
    S_(i j) &= sum_(1 <= k, l <= n) a_(k i) Cov(X_k, X_l) a_(l j) \
    &= Cov(sum_(k = 1)^n a_(k i) X_k, sum_(l = 1)^n a_(l j) X_l) \
    &= Cov(Y_i, Y_j)
  $
  Où
  $
    Y_i = sum_(k = 1)^n a_(k i) X_k
  $

*Application*

Soit $A, B in M_n (RR)$, on note le produit de Hadamard de $A$ et $B$
$
  A dot.o B = (a_(i j) b_(i j))_(i j)
$
Monrons que si $A, B in S_n^+ (RR)$ alors $A dot.o B$ aussi.

On refait la démo : soit $X_1, dots, X_(2n)$ vaiid de Rademarcher.
$
  A = S^TT S = Cov(Y_1, dots, Y_n) \
  B = R^TT R = Cov(Z_1, dots, Z_n) \
  Y_i = sum_(j = 1)^n s_(j i) X_i quad quad Z_i = sum_(j = 1)^n s_(j i) X_(i + n) \
$
Or $EE(Y_i) = EE(Z_i) = 0$ d'où
$
  A = (EE(Y_i Y_j))_(i j) quad quad B = (EE(Z_i Z_j))_(i j) \
$
$
  A dot.o B &= (EE(Y_i Y_j) EE(Z_i Z_j))_(i j) \
  &= (EE(underbrace(Y_i Z_i, W_i) underbrace(Y_j Z_j, W_j)))_(i j) \
  &= Cov(W_1, dots, W_n) in S_n^+ (RR)
$

#card("matantisym", "Endomorphismes et matrices antisymétriques", ("Maths.Algèbre.Algèbre linéaire.Euclidiens",))

Endomorphismes et matrices antisymétriques.

#answer

Soit $u in cal(L)(E)$ où $(E, scl(dot, dot))$ euclidien. On a équivalence entre

+ $forall x in E, scl(u(x), x) = 0$.

+ $forall x, y in E, scl(u(x), y) = - scl(x, u(y))$.

+ $u^* = -u$

On dit dans ce cas que $u$ est antisymétrique. On note $A(E)$ leur ensemble.

$
  cal(L)(E) = S(E) plus.o A(E)
$

Ainsi

$
  S(E) inter A(E) = {0}
$

Et de plus

- Si $dim E in 2 NN + 1$, $det u = 0$.

- Pour tout $u in A(E)$, $"rg" u in 2 NN$.

- Pour tout $A in A_n (RR)$, $"Sp" (A) subset.eq i RR$.

- Pour tout $A in A_n (RR)$, $A$ est diagonalisable dans $M_n (CC)$.

*Démonstration*

- (2 $<=>$ 3) Par définition.

- (2 $=>$ 1) Avec $y = x$ : #h(1fr)
  $
    scl(u(x), x) = -scl(x, u(x)) = 0
  $

- (1 $=>$ 2) Soit $x, y in E$
  $
    0 = &scl(u(x + y), x + y) \
    = &underbrace(scl(u(x), x), 0) + underbrace(scl(u(y), y), 0) \ + &scl(u(x), y) + scl(x, u(y))
  $
  D'où
  $
    scl(u(x), y) = -scl(x, u(y))
  $

- Découle de
  $
    M_n (RR) = S_n (RR) dperp A_n (RR)
  $

- Soit $u in A(E)$
  $
    u^* = -u \
    det(u) = det(u^*) = det(-u) \
    det(u) = (-1)^(dim E) det (u)
  $
  Donc si $dim E in 2 NN + 1$
  $
    det(u) = 0
  $

- Pour tout $u in A(E)$
  $
    E &= ker (u) dperp im (u^*) \
    &= ker (u) dperp im (u)
  $
  Ainsi $im (u)$ est stable par $u$ et est un supplémentaire de $ker (u)$ donc $tilde(u)$ induit est un automorphisme et $tilde(u) in A(im u)$, nécessairement $dim (im u) in 2 NN$.

- Soit $A in A_n (RR)$, $lambda in "Sp" (A)$ et $X in C^n$ vecteur propre associé non nul.
  $
    A Z &= lambda Z \
    overline(Z)^TT A Z &= lambda overline(Z)^TT Z = lambda sum_(k = 1)^n abs(z_k) in lambda RR^*_+ \
    overline(overline(Z)^T A Z) &= Z^TT overline(A) overline(Z) = Z^TT A overline(Z) in cal(M)_(11) (CC) \
    &= (Z^T A overline(Z))^TT = overline(Z)^TT A^TT Z \
    &= -overline(Z)^TT A Z in i RR
  $
  D'où $lambda in i RR$.

- Soit $A in A_n (RR)$, comme $A^2 in S_n (RR)$, $A^2$ est diagonalisable dans $M_n (RR)$.

  Or $ker A^2 = ker (- A^2) = ker (A^TT A) = ker A$, donc par un exercice de réduction, $A$ est diagonalisable dans $M_n (CC)$.

#card("reducantisym", "Réduction des endomorphismes antisymétriques", ("Maths.Algèbre.Algèbre linéaire.Euclidiens",))

Réduction des endomorphismes antisymétriques.

#answer

Soit $u in A(E)$ où $(E, scl(dot, dot))$ est un euclidien. On dispose de $e$ BON, $p + q = n$ et $a_1, dots, a_p in RR$ tels que
$
  cal(M)_e (u) = dmat(0 I_q,a_1 A, dots.down, a_p A) \
  A = mat(0, -1; 1, 0)
$

*Démonstration*

Par récurrence sur $n = dim E$. Initialisation ($n in {1, 2}$) facile.

Soit $E$ de dimension $n + 1$.

- Si $u in.not "GL"(E)$, $F = ker u$ est stable par $u$ et $F^perp$ aussi, on peut induire sur les deux et utiliser l'hypothèse de récurrence.

- Sinon $u in "GL"(E)$, ($dim E in 2 NN$) et $"Sp"_RR (u) = emptyset$. Mais comme $E$ est un $RR$-ev, $u$ admet un plan stable, donc on peut induire et utiliser l'hypothèse de récurrence.

// NOTE: Exercice M343

// TODO: Correction d'exercice M??? (C'est bien une feuille)
