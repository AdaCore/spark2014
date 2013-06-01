package body R is
    procedure Half (A : in out Arr) is
       H : Integer;
       A_Old : constant Arr := A;
    begin
       H := A'Last / 2;
       pragma Assert (2 * H <= A'Last);
       pragma Assert (A'First + H <= A'Last);
       for Q in A'First .. H loop
          pragma Assert (A'First = A_Old'First and A'Last = A_Old'Last);
          A(Q + H) := 0;
       end loop;
    end Half;
end R;
