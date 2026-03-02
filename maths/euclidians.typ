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

- On a $u in O(E)$ et $u(F) subset.eq F$, or comme $u in "GL"(E)$, $u(F) = F$ par argument dimensionnel.

  Ainsi $u^(-1) (F) = u^* (F) = F$, et $F$ est stable par $u^*$, donc $F^perp$ est stable par $u^*^* = u$.

- Pour tout $x, y in F$
  $
    scl(tilde(u)(x), tilde(u)(y)) &= scl(u(x), u(y)) \ &= scl(x, y)
  $

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

#card("thspectral", "Théorème spectrale", ("Maths.Algèbre.Euclidiens",))

Théorème spectrale.

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

- Par recurrence sur $n$.

  Le cas $n = 1$ est évident.

  On suppose le résultat pour tout $k <= n in NN$, et $A in S_(n+1) (RR)$.

  Comme $chi_A$ est scindé sur $RR$, on dispose de $lambda_1 in RR in "Sp" (A)$.

  Ainsi $E_lambda_1 (A) = F$ est stable par $A$, donc $F^perp$ aussi.

  En considérent la bonne BON on a alors
  $
    P A P^T = mat(lambda_1 I_m, 0; 0, tilde(A)) = (P A P^T)^TT \
    tilde(A) = tilde(A)^TT in S_n (RR)
  $
  Et on conclus par hypothèse de récurrence.

#card("calcvpps", "Expression des valeurs propres avec le produit scalaire", ("Maths.Algèbre.Euclidiens",))

Expression des valeurs propres avec le produit scalaire.

#answer

Pour $u in S(E)$, $(E, scl(dot, dot))$ euclidien, on note $lambda_1 <= dots.c <= lambda_n$ le spectre ordonnée (avec multiplicité) de $u$.

Par le théorème spectral on dispose d'une BON de vecteurs propres $(e_1, dots, e_n)$.

- Pour tout $x in E$ #h(1fr)
  $
    x = sum_(k = 1)^n x_k e_k \
    scl(u(x), x) = sum_(k = 1)^n lambda_k x_k^2 \
    norm(u(x))^2 = sum_(k = 1)^n lambda_k^2 x_k^2 \
  $

- Pour les valeurs propres extremmes
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

#card("endoautopos", "Endomorphismes autoadjoints positifs", ("Maths.Algèbre.Euclidiens",))

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

#card("decompensympos", "Décomposition des Endomorphismes symmétriques positifs", ("Maths.Algèbre.Euclidiens",))

Décomposition des Endomorphismes symmétriques positifs.

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

#card("matgramm", "Matrices de Gram", ("Maths.Algèbre.Euclidiens",))

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

#card("reducisomvec", "Réduction des isométries vectorielles", ("Maths.Algèbre.Euclidiens",))

Réduction des isométries vectorielles.

#answer

*Dimension 2*

Pour tout $u in O(E)$ où $(E, scl(dot, dot))$ euclidien de dimension $2$ et $e = (e_1, e_2)$ BON
$
  cal(M)_e (u) = A = mat(cos theta, - epsilon sin theta; sin theta, epsilon cos theta) \
  theta in RR quad quad epsilon = det u in {-1, 1}
$

- Si $A in "SO"_2 (RR)$, $u$ est une rotation d'angle $theta$, et $A$ ne dépend pas de la BON directe choisie.
 
- Si $A in O^-_2 (RR)$, $u$ est une réfléxion d'angle $theta / 2$ et $A$ ne dépend pas de la BON directe choisie.

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

#card("identso", "Identification d'une matrice de rotation en dimension 3", ("Maths.Algèbre.Euclidiens",))

Identification d'une matrice de rotation en dimension 3.

#answer

Soit $A = cal(M)_e (u) = (C_1 space C_2 space C_3) != I_3$.

+ Si $(C_1, C_2, C_3)$ forme une BON, $A in O_3 (RR)$.

+ Ainsi $C_3 = plus.minus C_1 and C_2$, et on peut déterminer le signe avec une seule coordonée de $C_1 and C_2$. #h(1fr)

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

#card("exrefengon", "Exercice : les réflexions engendrent le groupe orthogonale", ("Maths.Exercice.Euclidiens",))

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

#card("raccarendos", "Racine carrée d'une matrice symmétrique positive", ("Maths.Algèbre.Euclidiens",))

Racine carrée d'une matrice symmétrique positive.

#answer

Soit $S in S_n^+ (RR)$, il existe une unique $R in S_n^+ (RR)$ tel que
$
  S = R^2
$

*Démonstration*

- Existence : par le théorème spectrale on dispose de $P in O_n (RR)$ tel que #h(1fr)
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

#card("decomppolaire", "Décomposition polaire d'Endomorphismes", ("Maths.Algèbre.Euclidiens",))

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
