package T3Q1
is

  subtype ElementType is Natural range 0..1000;
  subtype IndexType is Positive range 1..100;
  type ArrayType is array (IndexType) of ElementType;

  procedure Rotate3(A: in out ArrayType; X, Y, Z: in IndexType);
  --# derives A from A, X, Y, Z;
  --# pre X /= Y and
  --#     Y /= Z and
  --#     X /= Z;
  --# post A(X) = A~(Y) and A(Y) = A~(Z) and A(Z) = A~(X) and
  --#     (for all N in IndexType => ((N/=X and N/=Y and N/=Z) -> A(N) = A~(N)));

end T3Q1;
