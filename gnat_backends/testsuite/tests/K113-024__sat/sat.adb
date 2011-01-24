package body Sat is

   function Add (X , Y : My_Int) return My_Int is
   begin
      if X + Y < 10_000 then
         return X + Y;
      else
         return 10_000;
      end if;
   end Add;

end Sat;
