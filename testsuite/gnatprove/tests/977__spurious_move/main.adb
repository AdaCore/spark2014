procedure Main with SPARK_Mode is
   package A is
      type List is private;
      procedure Test (X : List);
   private
      type List is access Integer;
   end A;
   package body A is
      procedure Test (X : List) is
      begin
         goto L;
         <<L>>
      end Test;
   end A;
begin
   null;
end Main;
