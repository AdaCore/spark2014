procedure Good with SPARK_Mode, Global => null is

   X : Boolean;

   procedure Callee with Import, Post => X;

   procedure Caller
      with Global => (Proof_In => X)
   is
   begin
      Callee;
   end Caller;
begin
   null;
end;
