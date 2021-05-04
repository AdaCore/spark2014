package body Termination with SPARK_Mode is

   function Infinite_Loop return Boolean
   is
      Result : Boolean := True;
   begin
      loop
         Result := not Result;
      end loop;
      return Result;
   end Infinite_Loop;

   function Infinite_Loop2 return Boolean
   is (Infinite_Loop);

   function Rec_Func return Boolean is
   begin
      if not Rec_Func then
         return Rec_Func;
      else
         return Rec_Func;
      end if;
   end Rec_Func;

   function Another_Nonterminating_Func return Boolean is (Infinite_Loop);

end Termination;
