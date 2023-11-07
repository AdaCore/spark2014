package Illegal with SPARK_Mode is

   type R1 is record X : Integer; end record;

   function "=" (A, B : R1) return Boolean
     with Volatile_Function;

   type R2 is record X : Integer; end record;

   function "=" (A, B : R2) return Boolean
     with Side_Effects;

   type R3 is record X : Integer; end record;

   function "=" (A, B : R3) return Boolean
     with Ghost;

   --  limited types

   type L1 is limited record X : Integer; end record;

   function "=" (A, B : L1) return Boolean -- ok
     with Volatile_Function;

   type L2 is limited record X : Integer; end record;

   function "=" (A, B : L2) return Boolean -- ok
     with Side_Effects;

   type L3 is limited record X : Integer; end record;

   function "=" (A, B : L3) return Boolean -- ok
     with Ghost;

   --  limited views of nonlimited types

   type LV1 is limited private;

   function "=" (A, B : LV1) return Boolean
     with Volatile_Function;

   type LV2 is limited private;

   function "=" (A, B : LV2) return Boolean
     with Side_Effects;

   type LV3 is limited private;

   function "=" (A, B : LV3) return Boolean
     with Ghost;

   --  limited views of types not in SPARK

   package Inner is

      type LV1 is limited private;

      function "=" (A, B : LV1) return Boolean
        with Volatile_Function;

      type LV2 is limited private;

      function "=" (A, B : LV2) return Boolean
        with Side_Effects;

      type LV3 is limited private;

      function "=" (A, B : LV3) return Boolean
        with Ghost;

   private
      pragma SPARK_Mode (Off);

      type LV1 is record X : Integer; end record;
      type LV2 is record X : Integer; end record;
      type LV3 is record X : Integer; end record;

   end Inner;

private

   type LV1 is record X : Integer; end record;
   type LV2 is record X : Integer; end record;
   type LV3 is record X : Integer; end record;

end Illegal;
