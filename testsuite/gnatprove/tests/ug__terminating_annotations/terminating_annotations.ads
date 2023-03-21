package Terminating_Annotations with SPARK_Mode is

   procedure P_Rec (X : Natural) with
     Annotate => (GNATprove, Always_Return);

   procedure P_While (X : Natural) with
     Annotate => (GNATprove, Always_Return);

   procedure P_Not_SPARK (X : Natural) with
     Annotate => (GNATprove, Always_Return);

   procedure Not_SPARK (X : Natural);
   procedure P_Call (X : Natural) with
     Annotate => (GNATprove, Always_Return);

   procedure P_Term (X : Natural) with
     Annotate => (GNATprove, Always_Return),
     Subprogram_Variant => (Decreases => X);
end Terminating_Annotations;
