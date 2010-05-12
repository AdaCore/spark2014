package body Anon_Type
is
   procedure exchange(A1 : out Array1; A2 : out Array2)
   is
   begin
        A1 := (0,1,2,3,4);
        A2 := (5,6,7,8,9);
          for I in Integer range 1 .. 9 loop
             A2(I) := A1(I);
          end loop;
	null;
   end exchange;
end Anon_Type;
