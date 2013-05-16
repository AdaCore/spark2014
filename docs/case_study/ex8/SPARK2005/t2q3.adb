package body T2Q3
is

  procedure Find (A: in ArrayType; Value: in ElementType;
                  Found: out Boolean; Index: out IndexType)
  is
  begin
    Index := IndexType'First;
    loop
      Found := A(Index) = Value;
      exit when Found or Index = IndexType'Last;
      Index := Index + 1;
    end loop;
  end Find;

end T2Q3;
