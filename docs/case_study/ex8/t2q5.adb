package body T2Q5
is

  function The_Max(A: ArrayType;
                   L, U: IndexType) return ElementType is
     Result : ElementType;
  begin
     for Result in ElementType loop
        exit when ((for all N in IndexType range L..U => (A(N) <= Result)) and
                     (for some N in IndexType range L..U => (A(N) = Result)));
     end loop;
     return Result;
   end The_Max;

  procedure MaxElement_P1B1 (A: in ArrayType; Max: out ElementType)
  is
  begin
    Max := A(IndexType'First);
    for I in IndexType loop
      if A(I) > Max then
        Max := A(I);
      end if;
      pragma Loop_Invariant ((for all N in IndexType range IndexType'First..I => (A(N) <= Max)) and
                       (for some N in IndexType range IndexType'First..I => (A(N) = Max)));
      --# assert (for all N in IndexType range IndexType'First..I => (A(N) <= Max))
      --#   and  (for some N in IndexType range IndexType'First..I => (A(N) = Max));
    end loop;
  end MaxElement_P1B1;

  procedure MaxElement_P2B1 (A: in ArrayType; Max: out ElementType)
  is
  begin
    Max := A(IndexType'First);
    for I in IndexType loop
      if A(I) > Max then
        Max := A(I);
      end if;
      pragma Loop_Invariant (Max = The_Max(A, IndexType'First, I));
      --# assert Max = the_max(A, IndexType'First, I);
    end loop;
  end MaxElement_P2B1;

  procedure MaxElement_P3B1 (A: in ArrayType; Max: out ElementType)
  is
  begin
    Max := A(IndexType'First);
    for I in IndexType loop
      if A(I) > Max then
        Max := A(I);
      end if;
    end loop;
  end MaxElement_P3B1;

  procedure MaxElement_P1B2 (A: in ArrayType; Max: out ElementType)
  is
  begin
    Max := A(IndexType'First);
    for I in IndexType range IndexType'First+1..IndexType'Last loop
      pragma Loop_Invariant ((for all N in IndexType range IndexType'First..(I-1) => (A(N) <= Max)) and
                       (for some N in IndexType range IndexType'First..(I-1) => (A(N) = Max)));
      --# assert (for all N in IndexType range IndexType'First..I-1 => (A(N) <= Max))
      --#   and  (for some N in IndexType range IndexType'First..I-1 => (A(N) = Max));
      if A(I) > Max then
        Max := A(I);
      end if;
    end loop;
  end MaxElement_P1B2;

  procedure MaxElement_P2B2 (A: in ArrayType; Max: out ElementType)
  is
  begin
    Max := A(IndexType'First);
    for I in IndexType range IndexType'First+1..IndexType'Last loop
      pragma Loop_Invariant (Max = The_Max(A, IndexType'First, I-1));
      --# assert Max = the_max(A, IndexType'First, I-1);
      if A(I) > Max then
        Max := A(I);
      end if;
    end loop;
  end MaxElement_P2B2;

  procedure MaxElement_P3B2 (A: in ArrayType; Max: out ElementType)
  is
  begin
    Max := A(IndexType'First);
    for I in IndexType range IndexType'First+1..IndexType'Last loop
      if A(I) > Max then
        Max := A(I);
      end if;
    end loop;
  end MaxElement_P3B2;

  procedure MaxElement_P1B3 (A: in ArrayType; Max: out ElementType)
  is
    I: IndexType := IndexType'First + 1;
  begin
    Max := A(IndexType'First);
    loop
      if A(I) > Max then
        Max := A(I);
      end if;
      pragma Loop_Invariant ((for all N in IndexType range IndexType'First..I => (A(N) <= Max)) and
                       (for some N in IndexType range IndexType'First..I => (A(N) = Max)));
      --# assert (for all N in IndexType range IndexType'First..I => (A(N) <= Max))
      --#   and  (for some N in IndexType range IndexType'First..I => (A(N) = Max));
      exit when I = IndexType'Last;
      I := I + 1;
    end loop;
  end MaxElement_P1B3;

end T2Q5;
