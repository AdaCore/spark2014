package body Anon_Type
is
   procedure exchange(A1 : out Array1; A2 : out Array2;
                     A3 : out Array3; A4 : out Array4)
   is
   begin
        A1 := (0,0,0,0,0);
        A2 := (1,1,1,1,1);
        A3 := (0,1,2,3,4,5,6,7,8,9);
        A4 := (9,8,7,6,5,4,3,2,1,0);
      for I in 1 .. 9 loop
         A2(I) := A1(I);
      end loop;
      for I in Array3'Range loop
         A4(I) := A3(I);
      end loop;
      for I in Array5'Range (2) loop
         null;
      end loop;
   end exchange;
end Anon_Type;
