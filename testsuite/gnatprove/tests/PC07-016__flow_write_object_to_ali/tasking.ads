package Tasking is
   protected type PT is
      entry E;
   private
      G : Boolean := True;
   end PT;

   task type T1;
   task type T2;

   type R is record
      C1 : PT;
      C2 : PT;
   end record with Volatile;

   RO1 : R;

   TO1 : T1;
   TO2 : T2;

end;
