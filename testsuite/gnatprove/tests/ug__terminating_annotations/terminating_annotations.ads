package Terminating_Annotations with SPARK_Mode is

   function F_Rec (X : Natural) return Natural with
     Annotate => (GNATprove, Terminating);

   function F_While (X : Natural) return Natural with
     Annotate => (GNATprove, Terminating);

   function F_Not_SPARK (X : Natural) return Natural with
     Annotate => (GNATprove, Terminating);

   procedure Not_SPARK (X : Natural);
   function F_Call (X : Natural) return Natural with
     Annotate => (GNATprove, Terminating);

   function F_Term (X : Natural) return Natural with
     Annotate => (GNATprove, Terminating),
     Subprogram_Variant => (Decreases => X);
end Terminating_Annotations;
