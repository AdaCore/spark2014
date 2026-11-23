procedure Direct_Read with SPARK_Mode is
   package Nested is
      type T is private
        with Default_Initial_Condition => True, Relaxed_Initialization;
      procedure Read_Value;
   private
      type T is array (Boolean) of Boolean;
   end Nested;

   package body Nested is
      procedure Read_Value is
         X : T;
         V : Boolean;
      begin
         V := X (False);
         pragma Assert (V);
      end Read_Value;
   end Nested;
begin
   Nested.Read_Value;
end Direct_Read;
