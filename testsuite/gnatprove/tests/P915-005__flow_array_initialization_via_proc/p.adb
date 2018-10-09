package body P is

   procedure Init_Element (A : out Boolean) is
   begin
      A := True;
   end Init_Element;

   procedure Init_Array (My_Array : out Array_Type) is
   begin
      for Index in My_Array'Range loop
         if Index < 3 then
            My_Array (Index) := Boolean'First;
         elsif Index > 3 then
            Init_Array (My_Array (Index .. My_Array'Last));
         else
            Init_Element (My_Array (Index));
         end if;
      end loop;
   end Init_Array;

end P;
