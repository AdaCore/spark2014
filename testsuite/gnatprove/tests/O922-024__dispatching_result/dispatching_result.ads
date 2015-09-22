package Dispatching_Result with SPARK_Mode is
   type Root is tagged record
      F1 : Natural;
   end record;
   function Init (V : Natural) return Root with
     Post'Class => Init'Result.F1 = V;
   function Init (V : Natural) return Root is
      (F1 => V);

   type Child is new Root with record
      F2 : Natural;
   end record;
   function Init (V : Natural) return Child is
      (others => V);
end Dispatching_Result;
