package P is

   task T2 with Global => null;

   protected PO is
      entry Dummy;
   private
      X : Boolean := False;
   end;

end;
