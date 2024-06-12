package Bad_Output with SPARK_Mode is
   pragma Elaborate_Body;
   type E is private;
   type Root is abstract tagged null record;
   procedure P (X : Root; Y : out E) is abstract;
   procedure Fail_At_Runtime;
private
   type Child is new Root with null record;
   procedure P (X : Child; Y : out E); -- @INVARIANT_CHECK:FAIL
   type E is new Integer with Type_Invariant => E >= 0, Default_Value => 0;
end Bad_Output;
