package P is

   protected PO is
      procedure Proc;
   private
      X : Integer := 0;
   end;

   task TO;

   X : Integer := 0 with Part_Of => TO;

end;
