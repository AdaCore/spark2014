package body P is

   procedure Wrapper
      with Pre => True;
--           Global => (In_Out => PO)

   procedure Wrapper
   is
   begin
      PO.Dummy;
   end;

   task body T1 is
   begin
      loop
         PO.Dummy;
      end loop;
   end;

   task body T2 is
   begin
      loop
         Wrapper;
      end loop;
   end;

   protected body PO is
      entry Dummy when True is
      begin
         X := not X;
      end;
   end;

end;
