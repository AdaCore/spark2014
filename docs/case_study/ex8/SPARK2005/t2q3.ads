package T2Q3
is

  subtype ElementType is Natural range 0..1000;
  subtype IndexType is Positive range 1..100;
  type ArrayType is array (IndexType) of ElementType;

  procedure Find (A: in ArrayType; Value: in ElementType;
                  Found: out Boolean; Index: out IndexType);
  --# derives Found, Index from A, Value;

end T2Q3;
