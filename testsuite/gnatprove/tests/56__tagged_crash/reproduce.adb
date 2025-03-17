package body Reproduce with SPARK_Mode is

   procedure Foo (X : in out T1) is
   begin
      T2 (X.Z.all).Bar;              --  Error.
   end Foo;

   procedure Bar (Y : in out T2) is  --  Removing "out" will finish the analysis.
   begin
      null;
   end Bar;

end Reproduce;
