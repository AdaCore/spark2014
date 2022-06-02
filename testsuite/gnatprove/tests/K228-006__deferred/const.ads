package Const is
   type R is record
      D : Integer;
   end record;
   C : constant R;
   function Get return Integer with Post => Get'Result = C.D;
   pragma Annotate (GNATprove, Always_Return, Get);
   function Get2 return Integer with Post => Get2'Result = 10_000;
   pragma Annotate (GNATprove, Always_Return, Get2);
private
   pragma SPARK_Mode (Off);
   C : constant R := (D => 10_000);
   function Get return Integer is (C.D);
   function Get2 return Integer is (Get);
end Const;
