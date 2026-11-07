package DIC_Guarded with SPARK_Mode is
   type T is private with Default_Initial_Condition => Ready (T);
   function Ready (X : T) return Boolean with Ghost;
private
   type R is new Integer with Relaxed_Initialization;
   type T is record
      Top : Natural := 0;
      Value : R;
   end record;
   function Ready (X : T) return Boolean is
     (X.Top = 0 or else (X.Value'Initialized and then X.Value = 0));
end DIC_Guarded;
