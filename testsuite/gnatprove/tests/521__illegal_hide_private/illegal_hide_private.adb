package body Illegal_Hide_Private with Spark_Mode is

   package body Nested is
      procedure P is null;
   end Nested;

   procedure Proc is null;

end Illegal_Hide_private;
