package body Exclude_Generic_Unit_Body with
  SPARK_Mode => Off
is
   --  this package body is not analyzed
   procedure Process (X : in out T) is
   begin
      null;
   end Process;
end Exclude_Generic_Unit_Body;
