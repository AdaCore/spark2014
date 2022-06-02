package Terminating_Annotations with SPARK_Mode is

   function F_Rec (X : Natural) return Natural with
     Annotate => (GNATprove, Always_Return);

   function F_While (X : Natural) return Natural with
     Annotate => (GNATprove, Always_Return);

   function F_Not_SPARK (X : Natural) return Natural with
     Annotate => (GNATprove, Always_Return);

   procedure Not_SPARK (X : Natural);
   function F_Call (X : Natural) return Natural with
     Annotate => (GNATprove, Always_Return);

   function F_Term (X : Natural) return Natural with
     Annotate => (GNATprove, Always_Return),
     Subprogram_Variant => (Decreases => X);
end Terminating_Annotations;
