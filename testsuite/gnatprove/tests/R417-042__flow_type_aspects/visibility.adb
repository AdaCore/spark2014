package body Visibility with SPARK_Mode => Off is

   function Infinite_Loop2 return Boolean
   is
      Result : Boolean := True;
   begin
      loop
         Result := not Result;
      end loop;
      return Result;
   end Infinite_Loop2;

end Visibility;
