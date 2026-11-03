// Physical386/printed364: partial D5 character table, 2 rows by 2 values.
#let d5-exceptional-table = $
  mat(
    delim: #none, augment: #(hline: 1, vline: 1),
    "", 5_1, 5_2;
    psi_1, alpha, beta;
    psi_2, beta, alpha;
  )
$

// Physical387/printed365: A5 table (14.22), all printed unknowns/signs.
#let a5-character-table = $
  mat(
    delim: #none, augment: #(hline: 1, vline: 1),
    "", 1, 2, 3, 5_1, 5_2;
    zeta_0, 1, 1, 1, 1, 1;
    zeta_1, 3, x, y, plus.minus alpha, plus.minus beta;
    zeta_2, 3, x, y, plus.minus beta, plus.minus alpha;
    zeta_3, 4, 0, 1, -1, -1;
    zeta_4, 5, 1, -1, 0, 0;
  )
$

// Physical394/printed372: GL2(3), eight rows and eight classes.
#let gl23-character-table = $
  mat(
    delim: #none, augment: #(hline: 1, vline: 1),
    "", 1_H, t, u, u', v, v', w_1, w_2;
    phi^1, 1, 1, 1, 1, 1, 1, 1, 1;
    phi^2, 1, 1, 1, 1, 1, -1, -1, -1;
    phi^3, 2, 2, 2, -1, -1, 0, 0, 0;
    phi^4, 3, 3, -1, 0, 0, 1, -1, -1;
    phi^5, 3, 3, -1, 0, 0, -1, 1, 1;
    phi^6, 2, -2, 0, -1, 1, 0, sqrt(2)i, -sqrt(2)i;
    phi^7, 2, -2, 0, -1, 1, 0, -sqrt(2)i, sqrt(2)i;
    phi^8, 4, -4, 0, 1, -1, 0, 0, 0;
  )
$

// Physical394/printed372: (14.25). Blank entries are author zeros.
#let gl23-virtual-character-matrix = $
  mat(
    delim: #none, augment: #(hline: 1, vline: 1),
    "", phi^1, phi^2, phi^3, phi^4, phi^5, phi^6, phi^7, phi^8;
    lambda_1, 1, "", 1, -1, "", "", "", "";
    lambda_2, "", 1, 1, "", -1, "", "", "";
    lambda_3, "", "", 1, "", "", -1, "", "";
    lambda_4, "", "", 1, "", "", "", -1, "";
    lambda_5, 1, 1, 1, "", "", "", "", -1;
  )
$

// Physical396/printed374: (14.27), virtual degrees and special classes.
#let involution-special-character-table = $
  mat(
    delim: #none, augment: #(hline: 1, vline: 1),
    "", 1, t, u, v, w_1, w_2;
    zeta^1, x_1, 1, 1, 1, 1, 1;
    zeta^2, x_2, 1, 1, 1, -1, -1;
    zeta^3, x_3, 2, 2, -1, 0, 0;
    zeta^4, x_4, 3, -1, 0, -1, -1;
    zeta^5, x_5, 3, -1, 0, 1, 1;
    zeta^6, x_6, -2, 0, 1, sqrt(2)i, -sqrt(2)i;
    zeta^7, x_7, -2, 0, 1, -sqrt(2)i, sqrt(2)i;
    zeta^8, x_8, -4, 0, -1, 0, 0;
  )
$

// Physical398/printed376: four class-number expressions, two cases.
#let involution-class-number-table = table(
  columns: 3,
  align: (left, center, center),
  table.header([], [Case I], [Case II]),
  $c_(t t t)=frac(|G|, 48^2)
  lr({1+1/x-8/y+27/(y+1)+27/(x+y)-64/(x+y+1)})=$,
  $12$,
  $0$,

  $c_(t t u)=frac(|G|, 48^2)lr({1+1/x+8/y-9/(y+1)-9/(x+y)})=$, $4$, $0$,
  $c_(t t v)=frac(|G|, 48^2)lr({1+1/x+4/y-16/(x+y+1)})=$, $6$, $0$,
  $c_(t t w_1)=frac(|G|, 48^2)lr({1-1/x-9/(y+1)+9/(x+y)})=$, $0$, $0.$,
)
