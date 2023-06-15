package Terminating_Annotations with SPARK_Mode is

   function F_Rec (X : Natural) return Natural;

   function F_While (X : Natural) return Natural;

   function F_Not_SPARK (X : Natural) return Natural;

   procedure Not_SPARK (X : Natural);
   function F_Call (X : Natural) return Natural;

   function F_Term (X : Natural) return Natural;
end Terminating_Annotations;
