package P is
   protected type PT is
      entry E;
   private
      G : Boolean := True;
   end PT;

   type R is record
      C : PT;
   end record with Volatile;

   RO1 : R;

   task type T;

   TO1 : T;

end;
