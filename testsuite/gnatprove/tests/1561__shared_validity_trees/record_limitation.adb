procedure Record_Limitation with SPARK_Mode is
   package T is
      type R is record
         F : Positive;
      end record;
      function Read return R with
        Import, Global => null, Potentially_Invalid => Read'Result;
      procedure Fill (X : out R) with
        Import, Global => null, Always_Terminates, Potentially_Invalid => X;
      procedure Update (X : in out R) with
        Import, Global => null, Always_Terminates, Potentially_Invalid => X;
      function Is_Valid (X : R) return Boolean with
        Import, Global => null, Potentially_Invalid => X;
      type D is new R;
      for D use record
         F at 0 range 0 .. 63;
      end record;
   end T;
   package body T is
   end T;
   use T;
   X : D with Import, Potentially_Invalid;
   Result : D := Read with Potentially_Invalid;
   pragma Unreferenced (Result);
   B : Boolean;
begin
   Fill (X);
   Update (X);
   B := Is_Valid (X);
end Record_Limitation;
