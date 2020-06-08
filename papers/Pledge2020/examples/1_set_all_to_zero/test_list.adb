package body Test_List with SPARK_Mode is
   procedure Set_All_To_Zero (X : List) is
      C : My_Nat := 0 with Ghost;
      --  Ghost variable to register the number of elements already processed

      Y : access List_Cell := X;
   begin
      while Y /= null loop

         --  C is the number of elements processed

         pragma Loop_Invariant (C = Length (Y)'Loop_Entry - Length (Y));

         --  X is a sequence of C zeros followed by elements of Y

         pragma Loop_Invariant
           (Pledge (Y, Length (X) = Length (Y) + C));
         pragma Loop_Invariant
           (Pledge (Y, (for all I in 1 .. Length (X) =>
                (if I <= C then Nth (X, I) = 0 else Nth (X, I) = Nth (Y, I - C)))));

         Y.Data := 0;
         Y := Y.Next;
         C := C + 1;
      end loop;
   end Set_All_To_Zero;
end Test_List;
