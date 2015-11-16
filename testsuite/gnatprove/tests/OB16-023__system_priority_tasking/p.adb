package body P
  with Refined_State => (State => PO)
is

   protected PO is
      procedure Dummy;
   private
      X : Boolean := False;
   end;

   protected body PO is
      procedure Dummy is
      begin
         X := not X;
      end;
   end;

   procedure Hidden is
   begin
      PO.Dummy;
   end;

end;
