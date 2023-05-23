procedure Test_HO_Arrays with SPARK_Mode is

   type My_Array is array (Positive range <>) of Natural;

   function Map (A : My_Array; F : not null access function (E : Natural) return Natural) return My_Array with
     Annotate => (GNATprove, Higher_Order_Specialization),
     Post => Map'Result'First = A'First and then Map'Result'Last = A'Last
     and then (for all I in A'Range => Map'Result (I) = F (A (I)));


   function Map (A : My_Array; F : not null access function (E : Natural) return Natural) return My_Array is
   begin
      return Res : My_Array (A'Range) with Relaxed_Initialization do
         for I in A'Range loop
            Res (I) := F (A (I));
            pragma Loop_Invariant (for all K in A'First .. I => Res (K)'Initialized);
            pragma Loop_Invariant (for all K in A'First .. I => Res (K) = F (A (K)));
         end loop;
      end return;
   end Map;

   function Add_To_All (A : My_Array; N : Natural) return My_Array with
     Pre => (for all E of A => E <= Natural'Last - N),
     Post => Add_To_All'Result'First = A'First and then Add_To_All'Result'Last = A'Last
     and then (for all I in A'Range => Add_To_All'Result (I) = A (I) + N);

   function Add_To_All (A : My_Array; N : Natural) return My_Array is
      function Safe_Add_N (E : Natural) return Natural is
        (if E <= Natural'Last - N then E + N else 0);
   begin
      return Map (A, Safe_Add_N'Access);
   end Add_To_All;

   function Add_To_All_Bad (A : My_Array; N : Natural) return My_Array with
     Pre => (for all E of A => E <= Natural'Last - N),
     Post => Add_To_All_Bad'Result'First = A'First and then Add_To_All_Bad'Result'Last = A'Last
     and then (for all I in A'Range => Add_To_All_Bad'Result (I) = A (I) + N);

   function Add_To_All_Bad (A : My_Array; N : Natural) return My_Array is
      function Bad_Add_N (E : Natural) return Natural is (E + N) with
        Pre =>  E <= Natural'Last - N;
   begin
      return Map (A, Bad_Add_N'Access); --@WEAKER_PRE_ACCESS:FAIL
   end Add_To_All_Bad;

begin
   null;
end Test_HO_Arrays;
