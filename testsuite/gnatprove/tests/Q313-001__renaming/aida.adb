package body Aida is
   pragma SPARK_Mode (On);

   procedure Get (Source  : String;
                  Pointer : in out Positive;
                  Value   : out Integer)
   is
   begin
      null;
   end Get;

   function To_Lowercase (Value : String) return String is
      Result : String (1..Value'Length);
      From   : Integer := Value'First;
      Code   : Integer;
   begin
      while From <= Value'Last loop
         Get (Value, From, Code);
      end loop;
      return Result;
   end To_Lowercase;

end Aida;
