procedure Float_Bounds with SPARK_Mode is
   function Id (X : Float) return Float is (X);
   subtype Dyn_Float is Float range Id (1.0) .. Id (100.0);
   type Rec is record
      F : Dyn_Float;
   end record;

   function fn (y, x, v : Dyn_Float; a : Rec) return Float is
     ((y - a.F * x) ** 2 / v)
   with Pre => v > 0.0;

begin
   null;
end Float_Bounds;
