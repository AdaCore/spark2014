package body Sorted_Vectors is pragma SPARK_Mode (On);

   procedure My_Insert (Container : in out Vector;
                        New_Item  :        Element_Type;
                        Position  :    out Index_Type) is
   begin
      Position := First_Index (Container);

      while Position <= Integer (Length (Container)) and then
        Element (Container, Position) < New_Item loop
         pragma Loop_Invariant
           (Position = First_Index (Container) or else
            Element (Container, Position - 1) < New_Item);
         Position := Position + 1;
      end loop;

      Insert (Container, Position, New_Item);

   end My_Insert;

end Sorted_Vectors;
