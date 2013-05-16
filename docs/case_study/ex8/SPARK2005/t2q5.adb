package body T2Q5
is

  procedure MaxElement_P1B1 (A: in ArrayType; Max: out ElementType)
  is
  begin
    Max := A(IndexType'First);
    for I in IndexType loop
      if A(I) > Max then
        Max := A(I);
      end if;
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
      --# assert (for all N in IndexType range IndexType'First..I => (A(N) <= Max))
      --#   and  (for some N in IndexType range IndexType'First..I => (A(N) = Max));
      exit when I = IndexType'Last;
      I := I + 1;
    end loop;
  end MaxElement_P1B3;

end T2Q5;
