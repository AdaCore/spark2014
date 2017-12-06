package P is

   X : Integer := 0;

   protected type PO is
      procedure Dummy with Global => (Proof_In => X);
   private
      Y : Integer := 0;
   end;

end;
