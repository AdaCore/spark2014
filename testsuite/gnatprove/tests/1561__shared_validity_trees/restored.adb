procedure Restored with SPARK_Mode is
   package T is
      type R is record
         F : Positive;
      end record;
      for R use record
         F at 0 range 0 .. 31;
      end record;
      function Read return R with
        Import, Global => null, Potentially_Invalid => Read'Result,
        Post => not Read'Result'Valid_Scalars;
      type D is new R;
      for D use record
         F at 0 range 0 .. 63;
      end record;
      type DD is new D;
      for DD use record
         F at 0 range 0 .. 31;
      end record;
   end T;
   package body T is
   end T;
   use T;
   X : DD := Read with Potentially_Invalid;
begin
   pragma Assert (not X'Valid_Scalars);
end Restored;
