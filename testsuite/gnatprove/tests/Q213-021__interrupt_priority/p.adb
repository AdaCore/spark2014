package body P is

   protected body PT is
      procedure Proc is
      begin
         null;
      end;
   end;

   task body TT is
   begin
      while True loop
         PO.Proc;
      end loop;
   end;
end;
