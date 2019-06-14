package body Loop_Exit is
   pragma SPARK_Mode (On);

   function Cond1 return Boolean with Pre => True;
   function Cond2 return Boolean with Pre => True;
   function Cond3 return Boolean with Pre => True;
   function Cond1 return Boolean is (True);
   function Cond2 return Boolean is (True);
   function Cond3 return Boolean is (True);

   procedure P is
      Advance : Boolean := True;
   begin
      while Advance loop
         if Cond1 then
            null;
         elsif Cond2 then
            if Cond3 then
               Advance := False;
               exit;
            end if;
            exit;
         end if;
      end loop;
   end P;

end Loop_Exit;
