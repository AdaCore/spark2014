package Terminating_Annotations with SPARK_Mode is

   function F_Rec (X : Natural) return Natural;
   pragma Annotate (GNATprove, Always_Return, F_Rec);

   function F_While (X : Natural) return Natural;
   pragma Annotate (GNATprove, Always_Return, F_While);

   function F_Not_SPARK (X : Natural) return Natural;
   pragma Annotate (GNATprove, Always_Return, F_Not_SPARK);

   procedure Not_SPARK (X : Natural);
   function F_Call (X : Natural) return Natural;
   pragma Annotate (GNATprove, Always_Return, F_Call);

   function F_Term (X : Natural) return Natural;
   pragma Annotate (GNATprove, Always_Return, F_Term);
end Terminating_Annotations;
