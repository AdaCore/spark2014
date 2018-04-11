package Priv_Disp with SPARK_Mode is
   type Child is private;
private
   type Root is tagged record
      F : Integer;
   end record;

   function Get_F (X : Root) return Integer is (X.F) with
     Post'Class => Get_F'Result = X.F; --@POSTCONDITION:FAIL

   type Child is new Root with record
      G : Integer;
   end record;

   overriding
   function Get_F (X : Child) return Integer is (X.G);
end Priv_Disp;
