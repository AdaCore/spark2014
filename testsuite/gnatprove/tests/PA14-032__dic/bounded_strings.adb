pragma SPARK_Mode(On);

package body Bounded_Strings is

   function Make(Upper_Bound : Index_Type; Initializer : Character) return Bounded_String is
      Result : Bounded_String(Upper_Bound); --@DEFAULT_INITIAL_CONDITION:PASS
   begin
      Result.Text := (others => ' ');
      Result.Text(1) := Initializer;
      Result.Length := 1;
      return Result;
   end Make;


end Bounded_Strings;
