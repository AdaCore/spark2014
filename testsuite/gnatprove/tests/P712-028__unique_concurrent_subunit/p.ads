package P is

   protected PO is
      procedure Proc;
   end PO;

   protected type PT is
      procedure Proc;
   end;

   task TO;

   task type TT;

end P;
