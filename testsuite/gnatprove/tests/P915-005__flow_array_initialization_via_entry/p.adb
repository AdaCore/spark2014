package body P is

   protected body PO1 is
      entry Init_Element (A : out Boolean) when True is
      begin
         A := True;
      end Init_Element;
   end PO1;

   protected body PO2 is
      entry Init_Elements (A : out Array_Type) when True is
      begin
         A := (others => True);
      end Init_Elements;
   end PO2;

   procedure Init_Array (My_Array : out Array_Type) is
   begin
      for Index in My_Array'Range loop
         if Index > 2 then
            PO2.Init_Elements (My_Array (Index .. My_Array'Last));
         else
            PO1.Init_Element (My_Array (Index));
         end if;
      end loop;
   end Init_Array;

end P;
