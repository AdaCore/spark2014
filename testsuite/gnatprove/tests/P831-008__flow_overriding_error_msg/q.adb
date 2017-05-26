package body Q
is
   function Heap return Boolean
     with SPARK_Mode => Off
   is
      type T_Ref is access Integer;

      O : T_Ref;

   begin
      O.all := 0;
      return True;
   end;

   procedure Proc (A : S) is
   begin
      if Heap then
         null;
      end if;
   end;
end;
