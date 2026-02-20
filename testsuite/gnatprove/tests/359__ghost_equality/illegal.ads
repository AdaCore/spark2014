package Illegal with SPARK_Mode is

   type R3 is record X : Integer; end record;

   function "=" (A, B : R3) return Boolean
     with Ghost;

   type LV3 is limited private;

   function "=" (A, B : LV3) return Boolean
     with Ghost;

   package Inner is

      type LV3 is limited private;

      function "=" (A, B : LV3) return Boolean
        with Ghost;

   private
      pragma SPARK_Mode (Off);

      type LV3 is record X : Integer; end record;

   end Inner;

private

  type LV3 is record X : Integer; end record;

end Illegal;
