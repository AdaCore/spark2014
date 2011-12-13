package body Sat is

   function Add (X , Y : My_Int) return My_Int is
      Res : My_Int;
   begin
      if X + Y < 10_000 then
         Res := X + Y;
      else
         Res := 10_000;
      end if;
      return Res;
   end Add;

end Sat;
