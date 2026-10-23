package Constants with SPARK_Mode is
   type Int_Access is access Integer;
   function Make return Int_Access with Import, Global => null;

   --  Exercise assumptions for an access constant initialized by a call
   Value : constant Int_Access := Make;
   procedure Check with Global => (Input => Value);
end Constants;
