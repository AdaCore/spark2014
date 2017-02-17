package body Math is

   function Sqrt (X : Integer) return Integer is
      Res : Integer := 0;
   begin
      while (Res + 1) * (Res + 1) <= X loop
         Res := Res + 1;
      end loop;
      return Res;
   end Sqrt;

   function Bad (X : Integer) return Integer is (0);

end Math;
