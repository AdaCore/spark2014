package body Term with SPARK_Mode is
   function Loop_Except_On_Zero (X : Natural) return Natural is
   begin
      if X = 0 then
         return 0;
      else
         while True loop
            null;
         end loop;
         return 0;
      end if;
   end Loop_Except_On_Zero;

   procedure Do_Not_Loop (X : in out Natural) is
   begin
      if X = 0 then
         X := Loop_Except_On_Zero (X);
      end if;
   end Do_Not_Loop;

   function Loop_If_C_Is_Neg return Empty_If_C_Is_Neg is
   begin
      if C < 0 then
         loop
            null;
         end loop;
      else
         return C;
      end if;
   end Loop_If_C_Is_Neg;

   procedure Still_Do_Not_Loop is
      X : Empty_If_C_Is_Neg;
   begin
      if C >= 0 then
         X := Loop_If_C_Is_Neg;
      end if;
   end Still_Do_Not_Loop;

end Term;
