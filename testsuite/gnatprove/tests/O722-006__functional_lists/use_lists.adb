package body Use_Lists with SPARK_Mode is
   procedure Add_1 (L1 : List; L2 : out List) is
      Cu : Cursor := First (L1);
   begin
      Clear (L2);
      while Has_Element (L1, Cu) loop
        pragma Loop_Invariant
           (Cursor_Sequence.Find (Get_Cursor_Model (L1), Cu) = Length (L2));
         pragma Loop_Invariant
           (for all N in 0 .. Natural (Length (L2)) - 1 =>
                 Is_Incr (Get (Get_Element_Model (L1), N),
                          Get (Get_Element_Model (L2), N)));
         if Element (L1, Cu) < Integer'Last then
            Append (L2, Element (L1, Cu) + 1);
         else
            Append (L2, Element (L1, Cu));
            pragma Assert
              (Get (Get_Element_Model (L2), Length (L2) - 1) =
                 Element (L1, Cu));
         end if;
         pragma Assert (Is_Incr (Element (L1, Cu),
                        Get (Get_Element_Model (L2), Length (L2) - 1)));
         Next (L1, Cu);
      end loop;
   end Add_1;
end Use_Lists;
