package P is

   task T1;
   task T2;

   protected PO is
      entry Dummy;
   private
      X : Boolean := False;
   end;

end;
