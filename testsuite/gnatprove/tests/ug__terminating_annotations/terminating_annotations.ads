package Terminating_Annotations with SPARK_Mode is

   procedure P_Rec (X : Natural) with
     Always_Terminates;

   procedure P_While (X : Natural) with
     Always_Terminates;

   procedure P_Not_SPARK (X : Natural) with
     Always_Terminates;

   procedure Not_SPARK (X : Natural);
   procedure P_Call (X : Natural) with
     Always_Terminates;

   procedure P_Term (X : Natural) with
     Always_Terminates,
     Subprogram_Variant => (Decreases => X);
end Terminating_Annotations;
