package Private_Discr with SPARK_Mode is

   type P_No_Default   (C : Natural) is private;
   type P_With_Default (C : Natural := 0) is private;
   type P_Holder is record
      Content : P_With_Default;
   end record;

   function New_No_Default (C : Natural) return P_No_Default with
     Post => New_No_Default'Result.C = C;

   function New_With_Default (C : Natural) return P_With_Default with
     Post => New_With_Default'Result.C = C;

private
   pragma SPARK_Mode (Off);

   type P_No_Default   (C : Natural) is null record;
   type P_With_Default (C : Natural := 0) is null record;

   function New_No_Default (C : Natural) return P_No_Default is (C => C);

   function New_With_Default (C : Natural) return P_With_Default is (C => C);

end;
