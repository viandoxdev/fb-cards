#import "/cards.typ": *

#show: setup

//![FLASHBANG HEADER]

#import "/utils.typ": *
#import "@preview/tiptoe:0.3.1"
#import "@preview/lilaq:0.4.0" as lq
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge
#import "@preview/physica:0.9.7": *

#card("derivevn", "Dérivabilité", ("Maths.Analyse.Espaces vectoriels normés",))

Définition de dérivabilité pour une fonction à valeur dans un evn.

#answer

Pour $f in cal(F)(I, E)$, où $I$ est un intervalle et $E$ un $RR$ ou $CC$-evn.

Soit $a in I$, on a équivalence entre

+ #h(1fr)
  $
    tau_a : func(I \\ {a}, E, x, (f(x) - f(a)) / (x - a)) 
  $
  Admet une limite finie $l in E$ en $a$.

+ On dispose de $l in E$ et $epsilon in cal(F)(I, E)$ tel que
  $
    f(x) = f(a) + (x - a)l + (x - a) epsilon(x) \
    "et " lim_(x -> a) epsilon(x) = 0
  $

Dans ce cas on dit que $f$ est dérivable en $a$ et on note
$
  l = f'(a) = lim_(x -> a) (f(x) - f(a)) / (x - a)
$

#card("linder", "Applications multi-linéaires et dérivation", ("Maths.Analyse.Espaces vectoriels normés",))

Formules de dérivation de $L(f)$, $B(f, g)$ et $M(f_1, dots, f_n)$.

#answer

Soient $E_1, dots, E_n, F$ des evn de dimension finie.

- Soit $L in cal(L)(E_1, F)$ et $f in cal(F)(I, E)$, si $f$ dérivable en $a in I$ :
  $
    (L compose f)'(a) = L(f') (a)
  $

- Soit $B : E_1 times E_2 -> F$ bilinéaire, $f, g in cal(F)(I, F)$, si $f$ et $g$ sont dérivables en $a in I$ :
  $
    (B(f, g))'(a) \ = B(f', g)(a) + B(f, g')(a)
  $

- Soit $M : product_(k = 1)^n E_k -> F$ $n$-linéaire, $f_1, dots, f_n in cal(F)(I, F)$. Si $f_1, dots, f_n$ sont dérivables en $a in I$ alors :
  $
    (M(f_1, dots, f_n))'(a) \
      = sum_(k = 1)^n M(f_1, dots, f_(k - 1), f'_k, f_(k+1), dots, f_n)(a)
  $

#card("derbout", "Théorème de Darboux", ("Maths.Analyse.Espaces vectoriels normés",))

Énoncé et démonstration du théorème de Darboux.

#answer

Soit $F in D^1(I, RR)$, pour tout $gamma in [F'(a), F'(b)]$ pour $a, b in I$ on dispose de $x in [a, b]$ tel que $F'(x) = gamma$.

*Démonstration*

Pour $gamma = 0$, supposons $F'(a) < 0, F'(b) > 0$
$
  min_[a,b] F in.not {F(a), F(b)}
$
Et $F C^0$ sur $[a, b]$

Donc on dispose de $x in [a, b]$ tel que $F(x) = min_[a, b] F$ et ainsi $F'(x) = 0$.

#card("inegevnfun", "Inégalités utiles", ("Maths.Analyse.Espaces vectoriels normés",))

Inégalités utiles qui tiennent pour les fonctions à valeur dans un evn de dimension finie.

#answer

+ Soit $f in C^1(I, E)$, pour tout $a, b in I$ : #h(1fr)
  $
    norm(f(a) - f(b)) <= abs(b - a) dot sup_[a, b] norm(f')
  $

+ Soit $f in C^(n+1)(I, E)$, pour tout $a, b in I$ :
  $
    norm(f(b) - sum_(k = 0)^n (b - a)^k / k! f^((k)) (a)) \
    <= abs(b - a) / (n+1)! sup_[a, b] norm(f^((n+1)))
  $


