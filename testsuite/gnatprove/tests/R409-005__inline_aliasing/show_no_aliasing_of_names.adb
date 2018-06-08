procedure Show_No_Aliasing_Of_Names
  with SPARK_Mode => On
is

   Total : Natural := 0;

   procedure Move_To_Total (Source : in out Natural) is
   begin
      Total  := Total + Source;
      Source := 0;
   end Move_To_Total;

   X : Natural := 3;

begin
   Move_To_Total (X); -- OK
   Move_To_Total (Total); -- Error
end Show_No_Aliasing_Of_Names;
