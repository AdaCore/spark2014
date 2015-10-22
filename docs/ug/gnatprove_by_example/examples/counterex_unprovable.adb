package body Counterex_Unprovable with
  SPARK_Mode
is

   function Double (X : Int) return Int is
   begin
      return 2 * X;
   end Double;

   procedure Double_In_Call (X : in out Int) is
   begin
      X := Double (X);
   end Double_In_Call;

   procedure Double_In_Loop (X : in out Int) is
      Result : Int := 0;
   begin
      for J in 1 .. 2 loop
         Result := Result + X;
      end loop;
      X := Result;
   end Double_In_Loop;

end Counterex_Unprovable;
