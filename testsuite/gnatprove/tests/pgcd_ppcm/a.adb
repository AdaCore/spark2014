package body A is

   function Pgcd (A, B : in Integer) return Integer is
      Ao : Integer;
      An : Integer := A;
      Bn : Integer := B;
   begin
      while Bn /= 0 loop
         pragma Assert (An /= Integer'First);
         pragma Assert (Bn /= Integer'First);
         pragma Assert (abs An <= abs A or else abs An <= abs B);
         pragma Assert (abs Bn <= abs A or else abs Bn <= abs B);
         Ao := An;
         An := Bn;
         Bn := Ao rem Bn;
      end loop;

      return abs An;
   end Pgcd;

   -------------------------------------------------------

   function Ppcm (A, B : in Integer) return Integer is
      R : Integer := Pgcd (A, B);
   begin
      if R /= 0 then
         R := (A * B) / R;
      end if;

      return abs R;
   end Ppcm;

end A;
