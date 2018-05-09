package body Higher_Order with SPARK_Mode is

   function Map_F (A : Array_1) return Array_2 is
      pragma Annotate
        (GNATprove, False_Positive,
         """R"" might not be initialized", "Array initialized in loop");
   begin
      return R : Array_2 (A'First .. A'Last) do
         for I in A'Range loop
            R (I) := F (A (I));
            pragma Loop_Invariant (for all K in A'First .. I =>
                                     R (K) = F (A (K)));
         end loop;
      end return;
   end Map_F;

   procedure Proc_Map_F (A : in out Array_Type) is
   begin
      for I in A'Range loop
         A (I) := F (A (I));
         pragma Loop_Invariant (for all K in A'First .. I =>
                                  A (K) = F (A'Loop_Entry (K)));
      end loop;
   end Proc_Map_F;

   package body Fold is
      function Acc_F (A : Array_Type; Init : Element_2) return Acc_Array is
         pragma Annotate
           (GNATprove, False_Positive,
            """R"" might not be initialized", "Array initialized in loop");
         Acc : Element_2 := Init;
      begin
         return R : Acc_Array (A'First .. A'Last) do
            for I in A'Range loop
               R (I) := F (A (I), Acc);
               pragma Loop_Invariant
                 (for all K in A'First .. I =>
                    Ind_Prop (A, R (K), Natural (K - A'First) + 1)
                  and then
                    R (K) = F (A (K),
                      (if K = A'First then Init else R (K - 1))));
               Acc := R (I);
            end loop;
         end return;
      end Acc_F;


      function Fold_F (A : Array_Type; Init : Element_2) return Element_2 is
      begin
         return R : Element_2 := Init do
            for I in A'Range loop
               R := F (A (I), R);
               pragma Loop_Invariant (R = Acc_F (A, Init) (I));
            end loop;
         end return;
      end Fold_F;
   end Fold;

end Higher_Order;
