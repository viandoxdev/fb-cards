#import "/cards.typ": *

#show: setup

//![FLASHBANG HEADER]

#import "/utils.typ": *
#import "@preview/tiptoe:0.3.1"
#import "@preview/cetz:0.4.2"
#import "@preview/lilaq:0.4.0" as lq
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge
#import "@preview/physica:0.9.7": *

#card("formmatendomedl", "Forme vectorielle des EDLs", ("Maths.Analyse.Équations différentielles linéaires",))

Forme matricielle des EDLs.

#answer

Soit $a in C^0 (I, cal(L)(E))$ et $b in C^0 (I, E)$ où $I$ est un intervalle de $RR$ et $E$ un $RR$ ou $CC$-ev de dimension finie.

Les équations différentielles linéaires qu'on étudie sont de la forme
$
  x' (t) = a(t) (x(t)) + b(t) quad quad (E)
$
Une solution de $(E)$ est $x in D^1 (I, E)$ tel que
$
  forall t in I, x'(t) = a(t)(x(t)) + b(t)
$

Toute solution est nécéssairement $C^1$ car $a$ et $b$ sont $C^0$.

*Lien avec les EDLs scalaire d'ordre n*

$
  y^((n)) (t) - sum_(k = 0)^(n - 1) a_k (t) y^((k)) (t) = b(t) quad space (cal(E))
$

Avec $a_0, dots, a_(n - 1), b in C^0 (I, KK)$

On associe à $y in D^n (I, KK)$
$
  Y : func(I, KK^n, t, vec(y(t), y'(t), dots.v, y^((n- 1)) (t)))
$
Et on pose
$
  A : t |-> inline(mat(0, 1;,dots.down, dots.down;,,dots.down,dots.down;,,,0,1;-a_0 (t),-a_1(t),dots.c, -a_(n - 2) (t), a_(n - 1) (t))) \
  B : t |-> vec(0, dots.v, 0, b(t))
$
Ainsi $y$ solution de $cal(E)$ est équivalent à $Y$ solution de
$
  Y'(t) = A(t) Y(t) + B(t) quad quad (E)
$

#card("eqlinhom", "Équations différentielles linéaires homogènes", ("Maths.Analyse.Équations différentielles linéaires",))

Équations différentielles linéaires homogènes.

#answer

Une EDL homogène est une EDL de la forme
$
  x'(t) = a(t) (x(t)) quad quad (E_0)
$
Où $a(t) in C^0 (I, cal(L)(E))$.

Avec $b(t) in C^0 (I, E)$
$
  x'(t) = a(t) (x(t)) + b(t) quad quad (E)
$

L'espace $S_0$ des solutions de $(E_0)$ est un sev de $C^0 (I, E)$.

L'espace $S$ des solutions de $(E)$ est soit vide (mais cela est impossible par le théorème de Cauchy-Lipschitz), soit un sea de $C^0 (I, E)$ obtenus par translation de $S_0$
$
  S = y_p + S_0 quad quad y_p in S
$

#card("probdecauchy", "Problème de Cauchy", ("Maths.Analyse.Équations différentielles linéaires",))

Problème de Cauchy.

#answer

On considère une EDL
$
  x'(t) = a(t)(x(t)) + b(t) quad quad (E)
$
Une condition initiale pour $(E)$ est la donnée de $t_0 in I$ et $x_0 in E$.

On appelle problème de Cauchy la recherche d'un $x in C^0 (I, E)$ tel que
$
  cases(space x'(t) = a(t)(x(t)) + b(t), space x(t_0) = x_0)
$

*Cas scalaire*

Pour une EDL scalaire d'ordre $n$.
$
  y^((n)) (t) - sum_(k = 0)^(n - 1) a_k (t) y^((k)) (t) = b(t) quad space (cal(E))
$

En posant l'application linéaire
$
  xi : func(D^n (I, KK), D^1 (I, KK), y, Y = vec(y, dots.v, y^(n-1)))
$
Avec $A in C^0 (I, M_n (KK))$ et $B in C^0 (I, KK^n)$ associé.

$
  y in S_cal(E) <=> Y in S_E
$
Donc $xi|_S_cal(E)$ est un isomorphisme (dans le cas homogène, sinon pas des espaces vectoriels).

Et une condition initiale pour $(cal(E))$ s'écrite
$
  cases(space y(t_0) &=& x_0, &space dots.v&, space y^(n-1) (t_0) &=& x_1 )
$

*Forme intégrale*

Soit $a in C^0 (I, cal(L)(E))$, $b in C^0 (I, E)$, $x_0 in E$ et $t_0 in I$.

Pour $y in D^1 (I, E)$, il y a équivalence entre

+ $y$ est solution du problème de Cauchy #h(1fr)
  $
  cases(space y'(t) = a(t)(y(t)) + b(t) quad (E), space y(t_0) = x_0)
  $

+ $forall t in I$
  $
    y(t) = x_0 + integral_(t_0)^t (a(s)(y(s)) + b(s)) dif s
  $

#card("thmcauchylipschitz", "Théorème de Cauchy-Lipschitz", ("Maths.Analyse.Équations différentielles linéaires",))

Théorème de Cauchy-Lipschitz.

#answer

Soit $I$ un intervalle, $E$ un $RR$ ou $CC$-ev de dimension finie, $a in C^0 (I, cal(L)(E))$ et $b in C^0 (I, E)$.

Pour tout $t_0 in I$ et $x_0 in E$, le problème de Cauchy
$
  cases(space x'(t) = a(t)(x(t)) + b(t) quad (E), space x(t_0) = x_0)
$
Admet une unique solution.

*Corolaires*

- L'espace (affine / vectorielle) des solutions est de même dimension que $E$.

- Dans le cas homogène, si $y_1, dots, y_d$ sont des solutions et $lambda_1, dots, lambda_d in KK$ et $t_0$ tels que
  $
    sum_(k = 1)^d lambda_k y_k (t_0) = 0
  $
  Alors pour tout $t in I$
  $
    sum_(k = 1)^d lambda y_k (t) = 0
  $

*Démonstration*

Idée : forme intégrale.

Soit
$
  f : func(C^0(I, KK^n), C^0 (I, KK^n), Y, f(Y)) \
  f(Y) = func(I, KK^n, t, X_0 + script(integral_(t_0)^t (A(s) Y(s) + B(s)) dif s))
$
Ainsi $Y in S <=> f(Y) = Y$

Deux méthodes :

+ (Idée) Marche aussi si non linéaire.

  Soit $delta > 0$ assez petit, $J = [t_0 - delta, t_0 + delta]$, sur $C^0 (J, KK^n)$, $f$ est contractante, et admet donc un unique point fixe, qui est une unique solution locale, puis on raccorde.

+ On pose
  $
    Y_0 : func(I, KK^n, t, X_0)
  $
  Et pour tout $p in NN$
  $
    Y_(p + 1) = f(Y_p)
  $
  On montre que $(Y_p)_(p in NN)$ converge uniformement sur tout $K = [a, b] subset.eq I$ contenant $t_0$.

  $
    f(x) - f(Y) : t |-> integral_(t_0)^t (A(X - Y))(s) dif s
  $

  Soit
  $
    c = sup_(s in K) norm(A(s))_"op"
  $
  D'où pour tout $t in K$ et $p in NN^*$
  $
    &norm(Y_(p+1) (t) - Y_p (t))  \
    =& norm((f(Y_p) - f(Y_(p-1)))(t)) \
    =& norm(integral_(t_0)^t A(s)(Y_p (s) - Y_(p-1) (s)) dif s) \
    <=& abs(integral_(t_0)^t norm(A(s))_"op" norm((Y_p - Y_(p-1))(s)) dif s) \
    <=& c abs(integral_(t_0)^t norm((Y_p - Y_(p-1))(s)) dif s) quad (*)
  $
  Or
  $
    Y_1 - Y_0 : t |-> integral_(t_0)^t (A(s)X_0 + B(s)) dif s \
    C_0 = sup_(s in K) norm(A(s) X_0 + B(s))
  $
  Ainsi pour tout $t in  K$
  $
    norm(Y_1(t) - X_0) <= C_0 abs(t - t_0) quad (**)
  $
  On montre par récurrence
  $
    norm(Y_p (t) - Y_(p - 1) (t)) <= C_0 c^(p-1) abs(t - t_0)^p / p!
  $

  L'initialisation est déjà faite. En supposant l'hypothèse de récurrence, pour tout $t in I$ on a
  $
    &norm(Y_(p+1) (t) - Y_p (t)) \
    <=& c abs(integral_(t_0)^t C_0 c^(p-1) abs(s - t_0)^p / p! dif s) \
    =& C_0 c^p abs(t - t_0)^(p + 1) / (p + 1)!
  $

  Donc avec $eta = max(t_0 - a, b - t_0)$
  $
    norm(Y_p - Y_(p-1))_(oo,K) <= C_0 c^(p-1) eta^p / p!
  $
  Qui est le terme général d'une série convergente : $sum Y_p - Y_(p - 1)$ converge normalement sur $K$, donc $(Y_p)$ converge uniformement sur $K$ vers $Y_oo$.

  On pose alors
  $
    tilde(f) : C^0(K, KK^n) -> C^0 (K, KK^n)
  $
  Qui correspond à $f$. Ainsi pour tout $X, Y in C^0(K, KK^n)$
  $
    norm(tilde(f)(X) - tilde(f)(Y))_oo <= c eta norm(X - Y)_oo
  $
  Et $tilde(f)$ est donc continue.

  Ainsi
  $
    tilde(f) (Y_oo|_K) = Y_oo|_K
  $
  Et ce pour tout $K$.

Il reste l'unicité :

On montre d'abord le lemme de Gronwall

+ Soit $f, g in C^0(I, RR)$ positives et $c >= 0$ tel que pour tout $t in I = Ico(0, +oo)$
  $
    f(t) <= c + integral_a^t f(s) g(s) dif s
  $
  Alors pour tout $t in I$
  $
    f(t) <= c exp(integral_a^t g(s) dif s)
  $

  Posons
  $
    h(t) = (c + integral_a^t f(s) g(s) dif s) / (c exp(integral_a^t g(s) dif s)) \
  $
  $
    h'(t) &= g(t) (f(t) - c - integral_a^t f(s) g(s) dif s) / (c exp(integral_a^t g(s) dif s)) \
    &<= 0
  $
  Ainsi pour tout $t in I$
  $
    h(t) <= h(t_0) = 1
  $

+ Ainsi si $Y$ et $tilde(Y)$ sont deux solutions, alors pour tout $t in I$
  $
    &Y(t) - tilde(Y)(t) \
    =& (f(Y) - f(tilde(Y)))(t) \
    =& integral_(t_0)^t A(s) (Y(s) - tilde(Y)(s)) dif s
  $
  Or pour tout $t >= t_0$
  $
    phi(t) &= norm(Y(t) - tilde(Y)(t)) \
    &<= 0 + integral_(t_0)^t norm(A(s))_"op" phi(s) dif s
  $
  D'où par le lemme de Gronwall
  $
    phi(t) <= 0 dot exp(integral_(t_0)^t norm(A(s))_"op" dif s)
  $
  Donc $Y(t) = tilde(Y)(t)$ sur $I inter Ico(t_0, +oo)$, et on peut faire de même sur $I inter Ioc(+oo, t_0)$.

#card("edlsyslincoefconst", "Système d'équation differentielles linéaires à coefficients constants", ("Maths.Analyse.Équations différentielles linéaires",))

Système d'équation differentielles linéaires à coefficients constants.

#answer

Pour
$
  (E) quad cases(space display(mat(delim: #none, 
    y'_1 (t), =, sum_(k = 1)^n a_(1 k) y_k (t);
    dots.v,,dots.v;
    y'_n (t), =, sum_(k = 1)^n a_(n k) y_k (t);
  ))) \
  <=> (E_0) quad Y'(t) = A Y(t) \
  A = (a_(i j))_(i j) quad quad Y(t) = vec(y_1 (t), dots.v, y_n (t))
$

Ainsi
$
  S_0 = { func(delim: #none, RR, KK^n, t, e^(t A) X_0), X_0 in KK^n }
$

#card("excarmdgedl", "Exercice : caractérisation des morphismes des réels additifs vers le groupe linéaire", ("Maths.Analyse.Équations différentielles linéaires",))

Caractériser les morphismes de $(RR, +)$ vers $("GL"(E), compose)$

+ Dans le cas $C^1$.

+ Dans le cas $C^0$.

#answer

+ Soit #h(1fr)
  $
    f in C^1(RR, "GL"(E))  \
    forall t, s in RR, f(s + t) = f(s) compose f(t)
  $
  Comme $f$ est $C^1$
  $
    dv(,t) f(t + s) = f'(t + s) \
    dv(,t) (f(t) compose f(s)) = f'(t) compose f(s) \
  $
  Donc pour $t = 0$ et pour tout $s in RR$
  $
    f'(s) = f'(0) compose f(s)
  $
  De plus $f(0) = id$ car morphisme de groupe.
  
  Ainsi par Cauchy-Lipschitz
  $
    f(t) = e^(t f'(0))
  $

+ Avec la notation matricielle :
  $
    M in C^0(RR, "GL"_n (KK)) \
    forall t, s in RR, space M(t + s) = M(t) M(s)
  $
  Montrons que $M$ est $C^1$. Pour $s, t in RR$
  $
    integral_0^t M(tau + s) dif tau = integral_0^t M(tau) M(s) dif tau
  $
  Par linéarité
  $
    integral_0^t M(tau + s) dif tau &= underbrace((integral_0^t M(tau) dif tau), tilde(M) (t)) M(s) \
    &= integral_s^(t + s) M(tau) dif tau \ 
    &= tilde(M)(t + s) - tilde(M)(s)
  $
  Or pour une norme subordonée
  $
    B(I_n, 1) subset.eq "GL"_n (KK)
  $
  (Car $I_n + N$ inversible si $N$ nilpotent)

  Donc pour tout $t > 0$
  $
    &norm(1/t tilde(M)(t) - I_n) \
    =& norm(1/t integral_0^t (M(tau) - I_n) dif tau) \
    <=& 1/t integral_0^t norm(M(tau) - I_n) dif tau
  $
  Or $M(0) = I_n$ et $M$ est continue, donc on dispose de $delta > 0$ tel que
  $
    M(Ioo(-delta, delta)) subset.eq B(I_n, 1/2)
  $

  Donc pour tout $t in Ico(0, delta)$
  $
    norm(1/t tilde(M)(t) - I_n) <= 1/2 < 1
  $

  Ainsi $tilde(M)(Ico(0, delta)) subset.eq "GL"_n (KK)$

  Donc pour tout $t in Ico(0, delta)$
  $
    M(s) = tilde(M)(t)^(-1) (tilde(M)(t + s) - tilde(M)(s))
  $
  Qui est donc $C^1$. Puis on conclut par propriétés de morphismes.

#card("resedlmatcasdz", "Résolution des équations differentielles linéaires homogènes matricielles à coefficient constant", ("Maths.Analyse.Équations différentielles linéaires",))

Résolution des équations differentielles linéaires homogènes matricielles à coefficient constant.

#answer

On étudie
$
  (E) quad Y' (t) = A Y(t) quad quad A in M_n (KK)
$

On a
$
  S = { e^(A t) X_0, X_0 in KK^n }
$

*Cas diagonalisable*

On prend la même équation, et on suppose $A$ diagonalisable.

Notons $C_1, dots, C_n in KK^n$ base de vecteurs propres de $A$ associés aux valeurs propres $lambda_1, dots, lambda_n in KK$.

$
  X_j : func(RR, KK^n, t, e^(t lambda_j) C_j) in S
$

Or $(X_1 (0), dots, X_n (0)) = (C_1, dots, C_n)$ libre donc par Cauchy-Lipschitz
$
  (X_1, dots, X_n)
$
Est libre et est donc une base de $S$.

*Cas diagonalisable dans les complexes*

On prend la même équation pour $KK = RR$, et on supposes $A$ diagonalisable dans $CC$.

Notons
$
  {underbrace(alpha_1\, dots\, alpha_p, in RR), lambda_1, overline(lambda_1), dots, lambda_r, overline(lambda_r) } = "Sp" (A)
$

Ainsi pour $k in [|1, p|]$ on pose
$
  X_k : t |-> e^(alpha_k t) C_k
$
Où $C_k$ est un vecteur propre non nul réel associé à $alpha_k$.

Pour $k in [|1, r|]$, on prend $W_k$ vecteur propre non nul associé à $lambda_k$ et on pose
$
  W_k = U_k + i V_k quad quad lambda_k = x_k + i y_k \
  Y_k : t |-> e^(x t) (cos (y_k t) V_k + sin(y_k t) U_k) \
  Z_k : t |-> e^(x t) (cos (y_k t) U_k - sin(y_k t) V_k) \
$

Et
$
  (X_1, dots, X_p, Y_1, dots, Y_r, Z_1, dots, Z_r) 
$
Est une base de $S$.

*Forme scalaire à coefficients constants*



*Démonstration*

+ Par Cauchy-Lipschitz, $(E)$ admet un espace de solutions $S$ de dimension $n$, et on vérifie que l'ensemble proposé marche.

+ Rien à faire.

+ On veut montrer la liberté de 
  $
    (C_1, dots, C_r, U_1, dots, U_r, V_1, dots, V_r)
  $
  Notons que
  $
    (C_1, dots, C_p, W_1, overline(W_1), dots, W_p, overline(W_p) )
  $
  Forme une base de vecteurs propres de $A$.

  Posons
  $
    sum_(k = 1)^r a_k C_k + sum_(k = 1)^r b_k U_k + c_k V_k = 0
  $
  $
    0 =& sum_(k = 1)^r b_k (W_k + overline(W_k)) / 2 + c_k (W_k - overline(W_k)) / 2 \
    +& sum_(k = 1)^r a_k C_k \
    0 =& sum_(k = 1) (b_k + c_k) / 2 W_k + (b_k - c_k) / 2 overline(W_k) \
    +& sum_(k = 1)^r a_k C_k
  $
  Donc
  $
    forall k in [|1, p|], space a_k = 0 \
    forall k in [|1, r|], space b_k + c_k = 0 = b_k - c_k \
  $
  Ainsi
  $
    forall k in [|1, r|], space b_k = c_k = 0 \
  $
  Et la famille est bien libre.

#card("resedlhsclcoefcst", "Résolution des équations differentielles linéaires homogènes scalaires à coefficients constants", ("Maths.Analyse.Équations différentielles linéaires",))

Résolution des équations differentielles linéaires homogènes scalaires à coefficients constants.

#answer

On étudie
$
  (cal(E)) quad y^(n) + sum_(k = 0)^(n - 1) a_k y^(k) = 0
$

Notons $cal(S)$ l'espace des solutions, qui est un $KK$-ev de dimension $n$ par Cauchy-Lipschitz.

On pose
$
  A &= inline(mat(0, 1;,dots.down, dots.down;,,dots.down,dots.down;,,,0,1;-a_0 (t),-a_1(t),dots.c, -a_(n - 2) (t), a_(n - 1) (t))) \ 
  &= C_p^TT quad P = chi_A = X^n + sum_(k = 0)^(n - 1) a_k X^k
$
Ainsi
$
  y in cal(S) <=> Y = vec(y, dots.v, y^(n - 1)) in S
$
Où $S$ est l'espace des solutions de
$
  (E) quad Y'(t) = A Y(t)
$

*Cas scindé racines simples*

On suppose $P = chi_A$ SARS, donc $A$ est diagonalisable.
$
  P = product_(k = 0)^n (X - lambda_k)
$
Ainsi en posant $C_1, dots, C_n$ une base de vecteurs propres de $A$ on a 
$
  S = "Vect" (t |-> e^(lambda_k t) C_k)_(k in [|1, n|])
$
D'où
$
  cal(S) = "Vect" (t |-> e^(lambda_k t))_(k in [|1, n|])
$

*Cas scindé racines simples dans les complexes*

Pour $KK = RR$, et $P$ SARS sur $CC$. Donc $A$ est diagonalisable sur $CC$, et on déduit du cas matricielle qu'en notant
$
  {script(underbrace(lambda_1\, dots\, lambda_p, in RR)\, alpha_1 + i beta_1\, alpha_1 - i beta_1\, dots\, alpha_r + i beta_r\, alpha_r + i beta_r) } = "Sp"_CC (A)
$
On a
$
  cal(S) =& "Vect" (e^(t alpha_k))_(k in [|1, p|]) \ +& "Vect" (e^(alpha_k t) cos(beta_k t))_(k in [|1, r|]) \ +& "Vect" (e^(alpha_k t) sin(beta_k t))_(k in [|1, r|])
$

*Cas général*

$P$ est scindé dans $CC$
$
  P = product_(k = 1)^q (X - lambda_k)^(m_k)
$

On montre par récurrence simple que tout $y in cal(S)$ est $C^oo$. On pose
$
  D : func(C^oo (RR, KK), C^oo (RR, KK), y, y')
$
Ainsi
$
  y in cal(S) &<=> P(D)(y) = 0 \ &<=> y in ker P(D)
$
Par le TDN
$
  cal(S) = plus.o.big_(k = 1)^q underbrace(ker (D - lambda_k id)^(m_k), "ev dim" m_k "par C-L")
$

Fixons un $lambda in CC$ et un $m in NN^*$,

Soit $k in NN$
$
  y_k : t |-> t^k e^(lambda t) \
  (D - lambda id) (y_k) &= y'_k - lambda y_k \
  &= k t^(k - 1) e^(lambda t) \
  &= k y_(k - 1)
$
Ainsi
$
  y_0, dots, y_(m - 1) in ker (D - lambda id)^m
$
Par liberté
$
  & ker (D - lambda id)^m \ =& "Vect" (y_0, dots, y_(m - 1)) \
  =& { t |-> Q(t) e^(lambda t), Q in KK_(m - 1) [X] }
$
D'où
$
  underbrace({t |-> sum_(k = 1)^q Q_k (t) e^(lambda_k t), (Q_k)_k in product_(j = 1)^q KK_(m_k - 1) [X]}, cal(S)) \
  = "Vect" (t^j e^(lambda_k t))_(k in [|1, q|], j in [|1, m_k - 1|])
$
