package body Sorted_Lists is

   procedure My_Insert (Container : in out List;
                        New_Item  :        Element_Type;
                        Position  :    out Cursor) is
      Current : Cursor := First (Container);
   begin
      
      while Has_Element (Container, Current) and then
        Element (Container, Current) < New_Item loop
         pragma Loop_Invariant 
           (Current = First (Container) or else
            Element (Container, Previous (Container, Current)) < New_Item);
         Next (Container, Current);
      end loop;
      
      Insert (Container, Current, New_Item, Position);
      
   end My_Insert;

end Sorted_Lists;
