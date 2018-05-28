package body Higher_Order with SPARK_Mode is

   function Map (A : Array_In) return Array_Out is
      pragma Annotate
        (GNATprove, False_Positive,
         """R"" might not be initialized", "Array initialized in loop");
   begin
      return R : Array_Out (A'Range) do
         for I in A'Range loop
            R (I) := F (A (I));
            pragma Loop_Invariant (for all K in A'First .. I =>
                                     R (K) = F (A (K)));
         end loop;
      end return;
   end Map;

   procedure Map_Proc (A : in out Array_Type) is
   begin
      for I in A'Range loop
         A (I) := F (A (I));
         pragma Loop_Invariant (for all K in A'First .. I =>
                                  A (K) = F (A'Loop_Entry (K)));
      end loop;
   end Map_Proc;


   function Map_I (A : Array_In) return Array_Out is
      pragma Annotate
        (GNATprove, False_Positive,
         """R"" might not be initialized", "Array initialized in loop");
   begin
      return R : Array_Out (A'Range) do
         for I in A'Range loop
            R (I) := F (I, A (I));
            pragma Loop_Invariant (for all K in A'First .. I =>
                                     R (K) = F (K, A (K)));
         end loop;
      end return;
   end Map_I;

   procedure Map_I_Proc (A : in out Array_Type) is
   begin
      for I in A'Range loop
         A (I) := F (I, A (I));
         pragma Loop_Invariant (for all K in A'First .. I =>
                                  A (K) = F (K, A'Loop_Entry (K)));
      end loop;
   end Map_I_Proc;

end Higher_Order;
