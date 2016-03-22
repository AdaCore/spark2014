package body Task_Param is

   task body TT is
   begin
      loop
         null;
      end loop;
   end;

   procedure P (X : TT) is
   begin
      null;
   end P;

   function F (X : TT) return Boolean is (True);

end Task_Param;
