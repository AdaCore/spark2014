package body Test_List with SPARK_Mode is
   procedure Set_All_To_Zero (X : List) is
      C : Big_Natural := 0 with Ghost;
      --  Ghost variable to register the number of elements already processed

      Y : access List_Cell := X;
   begin
      while Y /= null loop

         --  C is the number of elements processed

         pragma Loop_Invariant (C = Length (Y)'Loop_Entry - Length (Y));

         --  X is a sequence of C zeros followed by elements of Y

         pragma Loop_Invariant
           (Length (At_End (X)) = Length (At_End (Y)) + C);
         pragma Loop_Invariant
           (for all I in Interval'(1, Length (At_End (X))) =>
                (if I <= C then Nth (At_End (X), I) = 0 else Nth (At_End (X), I) = Nth (At_End (Y), I - C)));

         Y.Data := 0;
         Y := Y.Next;
         C := C + 1;
      end loop;
   end Set_All_To_Zero;
end Test_List;
