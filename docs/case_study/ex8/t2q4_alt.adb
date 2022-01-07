package body T2Q4_Alt
is

  procedure Clear_RTConly (A: in out ArrayType; L,U: in IndexType)
  is
  begin
    for I in IndexType range L..U loop
      --# assert U = U%;
      A(I) := 0;
    end loop;
  end Clear_RTConly;

end T2Q4_Alt;
