package body T3Q3
is

  procedure A (I, J: in Natural; K: out Natural)
  --# derives K from I, J;
  --# pre  I + J <= Natural'Last;
  --# post K = I + J;
  is
  begin
    K := I + J;
  end A;


  procedure M (I, J: in Natural; K: out Natural)
  --# derives K from I, J;
  --# pre  I * J <= Natural'Last;
  --# post K = I * J;
  is
  begin
    K := I * J;
  end M;


  procedure D (I, J: in Natural; K, L: out Natural)
  --# derives K, L from I, J;
  --# pre  J /= 0;
  --# post K = I / J and L = I - K * J;
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
    --# assert X = X~ and Y = Y~ and Q = X / Y and P = (X / Y) * Y;
    --# accept Flow, 10, R, "Value of R not required";
    D(P, Q, Y, R);
    --# end accept;
    --# check Y~ * (X~ / Y~) / (X~ / Y~) = Y~;

  --# accept Flow, 601, X, Y, "Overall result is that X is unchanged";
  --# accept Flow, 601, Y, X, "Overall result is that Y is unchanged";
  end DoNothing;

end T3Q3;
