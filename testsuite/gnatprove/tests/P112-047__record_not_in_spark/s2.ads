with Not_In_SPARK;

package S2 with SPARK_Mode is

   type I_Ptr is access Integer;

   type Bad_R is record
      C1 : access I_Ptr;
   end record;

   type Very_Bad_R is record
      V1 : Bad_R;
   end record;

   type Another_Rec is record
      V1 : Not_In_SPARK.T;
   end record;

end;
