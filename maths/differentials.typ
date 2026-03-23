#import "../cards.typ": *

#show: setup

//![FLASHBANG HEADER]

#import "/utils.typ": *
#import "@preview/tiptoe:0.3.1"
#import "@preview/cetz:0.4.2"
#import "@preview/lilaq:0.4.0" as lq
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge
#import "@preview/physica:0.9.7": *

#card("derselvec", "Derivée selon un vecteur", ("Maths.Analyse.Calcul différentiel",))

Derivée selon un vecteur.

#answer

Soit $f in cal(F)(Omega, F)$ où $Omega subset.eq E$ ouvert dans un $RR$-ev de dimension finie.

Soit $a in Omega$ et $u in E$, on dispose de $delta > 0$ tel que pour tout $t in Ioo(-delta, delta)$, $a + t v in Omega$.

On dit que $f$ admet une dérivée selon un vecteur $v$ en $a$ si
$
  phi_(v,a) : func(Ioo(-delta, delta), F, t, f(a + t v))
$
Est dérivable en $0$. Dans ce cas on note
$
  D_v f (a) &= phi'_(v, a) (0)  \
  &= lim_(t -> 0) (f(a + t v) - f(a)) /t
$

#card("derpart", "Dérivées partielles", ("Maths.Analyse.Calcul différentiel",))

Dérivées partielles.

#answer

On se fixe $e = (e_1, dots, e_n)$ une base de $E$ ($RR$-ev de dimension finie). On prend la base canonique si $E = RR^n$.

Si elle existe, on appelle la $j^e$ dérivée partielle de $f$ en $a in E$ la dérivée selon $e_j$ de $f : Omega -> F$ où $Omega subset.eq E$ ouvert.

$
  pdv(f, x_j) (a) &= partial_j f (a) = D_(e_j) f (a) \
  &= lim_(t -> 0) (f(a + t e_j) - f(a))/ t
$

Dans le cas où $E = RR^n$
$
  f(x) = f(x_1, dots, x_n) \
  phi_(a, e_j) : t |-> f(a + t e_j) \
  g_j : x_j |-> f(a_1, dots, x_j, dots, a_n)
$
La $j^e$ dérivée partielle existe si $phi_(a, e_j)$ est dérivable en $0$, ou si $g_j$ est dérivable en $a_j$, et dans ce cas
$
  diff_j (f) = pdv(f, x_j) (a) = phi'_(a, e_j) (a) = g'_j (a_j)
$

*Cela ne suffit pas à généraliser la dérivabilité*

On considère
$
  f : func(RR^2, RR, (x, y) != (0, 0), (x y) / (x^2 + y^2), (0, 0), 0)
$
Sur $RR^2 \\ {(0, 0)}$, $f$ admet évidemment des dérivées partielles.

En $(0, 0)$
$
x |-> f(x, 0) = 0 \
y |-> f(0, y) = 0 \
$
D'où $pdv(f, x) (0, 0)$ existe et est nulle. De même en $y$.

Mais $f$ n'est même pas $C^0$ en $(0, 0)$
$
  f(t, t) = t^2 / (2 t^2) = 1/2 tendsnot(t -> 0) 0
$

#card("différentiabilité", "Différentiabilité", ("Maths.Analyse.Calcul différentiel",))

Différentiabilité.

#answer

Soit $f : Omega -> F$ où $Omega subset.eq E$ ouvert.
Soit $a in Omega$ et $r > 0$ tel que $B(a, r) subset.eq Omega$.

On dit que $f$ est différentiable en $a$ si il existe $phi in cal(L)(E, F)$ et $epsilon : B(0, r) -> F$ tel que
$
  forall h in B_E (0, r), \
  f(a + h) = f(a) + phi(h) + norm(h) epsilon(h) \
  epsilon(h) tends(h -> 0) 0
$

Dans le cas où $E = RR$ et $Omega = I$, $f$ est différentiable en $a$ ssi $f$ est dérivable en $a$ et $phi : h |-> f'(a) h$.

*Propriétés*

- Si $f$ est différentiable en $a$, alors $f$ est continue en $a$

- Si $f$ est différentiable en $a$, alors $f$ admet une dérivée selon tout vecteur en $a$.

  Et pour tout $v in E$, $D_v f (a) = phi(v)$.

- L'application $phi$ est unique, est appelée différentiel de $f$ en $a$ et est notée $dif f (a)$.
  
  On note de plus alternativement $dif f (a) (h) = dif f (a). h$.

- Si $f$ est constante sur $Omega$, alors $f$ est différentiable sur $Omega$ et pour tout $a in Omega$, $dif f (a) = 0$.

- Si $f = phi|_Omega$ pour $phi in cal(L)(E, F)$, alors $f$ est différentiable sur $Omega$ et pour tout $a in Omega$, $dif f (a) = phi$.

*Démonstration*

- On suppose que $f$ est différentiable en $a$
  $
    lim_(h -> 0) f(a + h) =& f(a) + underbrace(lim(h -> 0) phi(h), 0) \ +& underbrace(lim_(h - > 0) norm(h) epsilon(h), 0) \
    =& f(a)
  $

- Calcul de limite.

#card("derlelongdunchemin", "Dérivée le long d'un chemin", ("Maths.Analyse.Calcul différentiel",))

Dérivée le long d'un chemin.

#answer

Soit $f : Omega -> F$ où $Omega subset.eq E$ ouvert. Soit $gamma : I -> E$ où $I$ est un intervalle et $gamma(I) subset.eq Omega$.

On suppose que $gamma$ est dérivable en $t_0 in I$ et $f$ est différentiable en $a = gamma(t_0)$.

Alors $f compose gamma$ est dérivable en $t_0$ et
$
  (f compose gamma)' (t_0) = dif f (gamma (t_0)) compose gamma' (t_0)
$

*Démonstration*

Par continuité de $gamma$ en $t_0$, on dispose de $V$ voisinage de $t_0$ tel que $gamma(V) subset.eq B(a, r)$.

Soit $h > 0$

$
  &f(gamma(t_0 + h)) - f(gamma(t_0)) \
  =& f(a + gamma(t_0 + h) - gamma(t_0)) - f(a) \
  =& dif f (a).(gamma(t_0 + h) - gamma(t_0)) \ 
  +& norm(gamma(t_0 + h) - gamma(t_0)) epsilon(gamma(t_0 + h) - gamma(t_0))
$
Ainsi pour tout $h > 0$
$
  &(f(gamma(t_0 + h)) - f(gamma(t_0))) / h \
  =& dif f (a).((gamma(t_0 + h) - gamma(t_0)) / h) \
  +& underbrace(norm((gamma(t_0 + h) - gamma(t_0)) / h), tends(h -> 0) norm(gamma'(t_0))) epsilon(underbrace(gamma(t_0 + h) - gamma(t_0), tends(h -> 0) 0))
$
Donc à la limite
$
  (f compose gamma)' (t_0) = dif f (a). gamma'(t_0)
$

#card("diffeetbases", "Différentiabilité et bases", ("Maths.Analyse.Calcul différentiel",))

Différentiabilité et bases.

#answer

Soit $f : Omega -> F$, où $Omega subset.eq E$ ouvert $(e_1, dots, e_n)$ base de $E$ et $(omega_1, dots, omega_p)$ base de $F$.

Quelques propriétés :

- Notation : si $f$ est différentiable en $a in Omega$

  On pose
  $
    forall k in [|1, n|], \ dif x_k : func(E, RR, h = sum_(j = 1)^n h_j e_j, h_k)
  $
  Et ainsi
  $
    dif f (a) = sum_(k = 1)^n pdv(f, x_k) dif x_k
  $

- Si on décompose $f$
  $
    f : x |-> sum_(k = 1)^p f_k (x) omega_k
  $

  Alors $f$ est différentiable en $a in Omega$ ssi pour tout $k in [|1, p|]$, $f_k$ est différentiable en $a$.

  Et dans ce cas
  $
    dif f (a) : h |-> sum_(k = 1)^p (dif f_k (a).h) omega_k
  $

#card("matrjaco", "Matrice Jacobienne", ("Maths.Analyse.Calcul différentiel",))

Matrice Jacobienne.

#answer

Soit $f : Omega -> RR^n$ où $Omega subset.eq RR^p$ ouvert.

Si $f$ est différentiable en $a in Omega$, on définit la matrice Jacobienne de $f$ en $a$ comme

$
  f : vec(x_1, dots.v, x_p) |-> vec(f_1(x_1, dots, x_p), dots.v, f_n (x_1, dots, x_p)) \ \

  J(f) (a) = mat(pdv(f_1, x_1), dots.c, pdv(f_1, x_n); dots.v, dots.down, dots.v; pdv(f_n, x_1), dots.c, pdv(f_n, x_n)) (a) in M_(n p) (RR)
$

#card("gradicd", "Gradient", ("Maths.Analyse.Calcul différentiel",))

Gradient.

#answer

Soit $f : Omega -> RR$ où $Omega subset.eq E$ ouvert dans un espace euclidien.

On suppose $f$ différentiable en $a in Omega$.

Par théorème de représentation, on dispose d'un unique vecteur $omega in E$ tel que pour tout $h in E$
$
  dif f (a).h = scl(omega, h)
$

On appelle $omega$ le gradient de $f$ en $a$ et on le note
$
  omega = grad f (a)
$

- Si $E = RR^p$ muni du produit scalaire canonique #h(1fr)
  $
    grad f(a) = vec(pdv(f, x_1) (a), dots.v, pdv(f, x_p) (a)) = J(f) (a)^TT
  $

- Si $dif f(a) != 0$
  $
    func(SS_E (0, 1), RR, u, dif f(a).u)
  $
  Est maximale en
  $
    (grad f (a)) / norm(grad f (a))
  $
  (Démonstration par Cauchy-Schwarz).

#card("opdif", "Opération sur les différentielles", ("Maths.Analyse.Calcul différentiel",))

Opération sur les différentielles.

#answer

- Si $f, g in cal(F)(Omega, F)$ et $f, g$ sont différentiables en $a in Omega$, alors pour tout $alpha, beta in RR$, $alpha f + beta g$ est différentiable en $a$ et #h(1fr)
  $
    dif (alpha f + beta g) (a) = alpha dif f (a) + beta dif g (b)
  $

- Soient $(f_1, dots, f_d) in product_(i = 1)^d cal(F)(Omega, F_i)$ et $M : F_1 times dots.c, F_d -> G$ est $d$-linéaire.

  Si $f_1, dots, f_d$ sont différentiables en $a in Omega$, alors
  $
    g : func(Omega, G, x, M(f_1 (x), dots, f_d (x)))
  $
  Est différentiable en $a$ et
  $
    dif g (a) : h |-> sum_(i = 1)^d script(M(f_1 (a), dots, dif f_i (a).h, dots, f_d (a)))
  $

- Soit $g : Omega -> F, f : W -> G$ où $Omega subset.eq E$ ouvert, $W subset.eq F$ ouvert, $g(Omega) subset.eq W$.

  Si $g$ est différentiable en $a in Omega$ et $f$ est différentiable en $b = g(a)$, alors $f compose g$ est différentiable en $a$ et 
  $
    dif (f compose g) (a) = dif f (g(a)) compose dif g (a)
  $

//NOTE: M384 Différentiabilité et normes

#card("formchaine", "Formule de la chaîne", ("Maths.Analyse.Calcul différentiel",))

Formule de la chaîne.

#answer

Soit $g : Omega -> F, f : W -> G$ où $Omega subset.eq E$ ouvert, $W subset.eq F$ ouvert, $g(Omega) subset.eq W$.

On fixe des bases de $E$, $F$ et $G$, et on se ramène au cas $E = RR^p, F = RR^n, G = RR^q$.

Si $g$ est différentiable en $a$ et $f$ est différentiable en $b = g(a)$, alors $f compose g$ est différentiable en $a$ et pour tout $j in [|1, p|]$ et $i in [|1, q|]$
$
  pdv(f compose g, x_j) = sum_(k = 1)^n pdv(f_i, u_k) (g(a)) pdv(g, x_j) (a)
$
