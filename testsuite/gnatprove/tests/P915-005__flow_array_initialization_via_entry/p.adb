package body P is

   protected body PO is
      entry Init_Element (A : out Boolean) when True is
      begin
         A := True;
      end Init_Element;
   end PO;

   procedure Init_Array (My_Array : out Array_Type) is
   begin
      for Index in My_Array'Range loop
         if Index > 2 then
            PO.Init_Element (My_Array (Index));
         else
            PO.Init_Element (My_Array (Index));
         end if;
      end loop;
   end Init_Array;

end P;
