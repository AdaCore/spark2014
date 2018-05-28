package body Higher_Order.Fold with SPARK_Mode is

   package body Fold_Left_Acc is
      function Fold (A : Array_Type; Init : Element_Out) return Acc_Array is
         pragma Annotate
           (GNATprove, False_Positive,
            """R"" might not be initialized", "Array initialized in loop");
         pragma Annotate
           (GNATprove, Intentional,
            """R"" is not initialized",
            "Prev_Val only looks at previous indices");
         Acc : Element_Out := Init;
      begin
         return R : Acc_Array (A'First .. A'Last) do
            for I in A'Range loop
               R (I) := F (A (I), Acc);
               pragma Loop_Invariant
                 (for all K in A'First .. I =>
                    Ind_Prop (A, Prev_Val (R, K, Init), K)
                  and then
                    R (K) = F (A (K), Prev_Val (R, K, Init)));
               Acc := R (I);
            end loop;
         end return;
      end Fold;
   end Fold_Left_Acc;

   package body Fold_Left is
      function Fold (A : Array_Type; Init : Element_Out) return Element_Out is
      begin
         return R : Element_Out := Init do
            for I in A'Range loop
               R := F (A (I), R);
               pragma Loop_Invariant (R = Acc.Fold (A, Init) (I));
            end loop;
         end return;
      end Fold;
   end Fold_Left;

   package body Fold_Right_Acc is
      function Fold (A : Array_Type; Init : Element_Out) return Acc_Array is
         pragma Annotate
           (GNATprove, False_Positive,
            """R"" might not be initialized", "Array initialized in loop");
         pragma Annotate
           (GNATprove, Intentional,
            """R"" is not initialized",
            "Prev_Val only looks at previous indices");
         Acc : Element_Out := Init;
      begin
         return R : Acc_Array (A'First .. A'Last) do
            for I in reverse A'Range loop
               R (I) := F (A (I), Acc);
               pragma Loop_Invariant
                 (for all K in I .. A'Last =>
                    Ind_Prop (A, Prev_Val (R, K, Init), K)
                  and then
                    R (K) = F (A (K), Prev_Val (R, K, Init)));
               Acc := R (I);
            end loop;
         end return;
      end Fold;
   end Fold_Right_Acc;

   package body Fold_Right is
      function Fold (A : Array_Type; Init : Element_Out) return Element_Out is
      begin
         return R : Element_Out := Init do
            for I in reverse A'Range loop
               R := F (A (I), R);
               pragma Loop_Invariant (R = Acc.Fold (A, Init) (I));
            end loop;
         end return;
      end Fold;
   end Fold_Right;

   package body Fold_2 is
      function Acc_F (A : Array_Type; Init : Element_Out) return Acc_Array is
         pragma Annotate
           (GNATprove, False_Positive,
            """R"" might not be initialized", "Array initialized in loop");
         pragma Annotate
           (GNATprove, Intentional,
            """R"" is not initialized",
            "Prev_Val only looks at previous indices");
         Acc : Element_Out := Init;
      begin
         return R : Acc_Array (A'Range (1), A'Range (2)) do
            for I in A'Range (1) loop
               pragma Loop_Invariant (Acc = Prev_Val (R, I, A'First (2), Init));
               pragma Loop_Invariant
                 (if I > A'First (1) then
                      (for all K in A'First (1) .. I - 1 =>
                         (for all L in A'Range (2) =>
                              Ind_Prop (A, Prev_Val (R, K, L, Init), K, L)
                          and then
                          R (K, L) = F (A (K, L), Prev_Val (R, K, L, Init)))));
               for J in A'Range (2) loop
                  pragma Assert (Ind_Prop (A, Acc, I, J));
                  R (I, J) := F (A (I, J), Acc);
                  Acc := R (I, J);
                  pragma Loop_Invariant
                    (for all K in A'First (1) .. I - 1 =>
                         (for all L in A'Range (2) =>
                                Ind_Prop (A, Prev_Val (R, K, L, Init), K, L)
                          and then
                          R (K, L) = F (A (K, L), Prev_Val (R, K, L, Init))));
                  pragma Loop_Invariant
                    (for all L in A'First (2) .. J =>
                         Ind_Prop (A, Prev_Val (R, I, L, Init), I, L)
                     and then
                     R (I, L) = F (A (I, L), Prev_Val (R, I, L, Init)));
                  pragma Loop_Invariant (Acc = R (I, J));
               end loop;
            end loop;
         end return;
      end Acc_F;


      function Fold (A : Array_Type; Init : Element_Out) return Element_Out is
      begin
         return R : Element_Out := Init do
            if A'Length (2) > 0 then
               for I in A'Range loop
                  pragma Loop_Invariant
                    (if I = A'First then R = Init
                     else R = Acc_F (A, Init) (I - 1, A'Last (2)));
                  for J in A'Range (2) loop
                     R := F (A (I, J), R);
                     pragma Loop_Invariant (R = Acc_F (A, Init) (I, J));
                  end loop;
               end loop;
            end if;
         end return;
      end Fold;
   end Fold_2;

end Higher_Order.Fold;
