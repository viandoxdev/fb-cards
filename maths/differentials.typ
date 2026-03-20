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
  phi_(a, e_j) : t |-> f(a + t e_j)
$

