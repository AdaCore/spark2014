package P with SPARK_Mode is

   Ctx : Boolean := True;

   type T is record
      C : Integer;
   end record;

   function "=" (X, Y : T) return Boolean with Global => (Input => Ctx);

end P;
