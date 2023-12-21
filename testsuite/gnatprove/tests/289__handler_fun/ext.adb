package body Ext with SPARK_Mode is
   function Reset return Integer is
      Read : constant Integer := Counter;
   begin
      Counter := 0;
      return Read;
   end Reset;
end Ext;
