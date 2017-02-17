package body T3Q3
is

  procedure A (I, J: in Natural; K: out Natural)
  with Depends => (K => (I, J)),
  pre =>  I <= Natural'Last - J,
  post => K = I + J;

  procedure A (I, J: in Natural; K: out Natural)
  is
  begin
    K := I + J;
  end A;


  procedure M (I, J: in Natural; K: out Natural)
  with Depends => (K => (I, J)),
  pre  => I * J <= Natural'Last,
  post => K = I * J;
  procedure M (I, J: in Natural; K: out Natural)
  is
  begin
    K := I * J;
  end M;


  procedure D (I, J: in Natural; K, L: out Natural)
  with Depends => ((K, L) => (I, J)),
  pre  => J /= 0,
  post => K = I / J and L = I - K * J;
  procedure D (I, J: in Natural; K, L: out Natural)
  is
  begin
    K := I/J;
    L := I - K * J;
  end D;


  procedure DoNothing (X, Y: in out Natural)
  is
    P, Q, R: Natural;
  begin
    D(X, Y, Q, R);
    M(Q, Y, P);
    A(P, R, X);
    D(P, Q, Y, R);

  end DoNothing;

end T3Q3;

