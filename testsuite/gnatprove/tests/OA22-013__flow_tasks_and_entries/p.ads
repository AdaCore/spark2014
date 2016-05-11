package P is

   task T2;

   protected PO is
      entry Dummy;
   private
      X : Boolean := False;
   end;

--   procedure Wrapper
--      with Global => (In_Out => PO);

   procedure A;
   procedure B;
   procedure C;

end;
