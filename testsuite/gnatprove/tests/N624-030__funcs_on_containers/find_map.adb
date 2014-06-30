package body Find_Map with SPARK_Mode is

   function Find_All (A : Nat_Array) return Index_Map is
      Result : Index_Map;
   begin
      Clear (Result);

      for K in A'Range loop
         if not Contains (Result, A (K)) then
            Insert (Result, A (K), K);
         end if;

         pragma Loop_Invariant (Length (Result) <= Count_Type (K));
         pragma Loop_Invariant
           (for all I in A'First .. K =>
              Contains (Result, A (I)) and then
            Element (Result, A (I)) in A'First .. I and then
            A (Element (Result, A (I))) = A (I));
         pragma Loop_Invariant
           (for all E in Natural =>
              (if Contains (Result, E) then
                    Element (Result, E) in A'First .. K and then
               Equivalent_Keys (A (Element (Result, E)), E)));
      end loop;

      return Result;
   end Find_All;


   function Find_Upto (A : Nat_Array; E : Natural; Last : Index)
                       return Natural is

      --  Test that we do not generate call to the program function of Element
      --  in EW_Term domain. If we do, we have a task with no tracability label
      --  here (we need the precondition of Element to fail for that).
      function Find_Map_Bad (M : Index_Map) return Natural is
        (if Element (M, E) <= Last then Element (M, E)
         else 0)
        with Pre  => A'Length > 0 and then
        (if Contains (M, E) then Element (M, E) in A'Range) and then
        (for all I in Index range A'First .. Element (M, E) - 1 => --@PRECONDITION:FAIL
             A (I) /= E) and then Contains (M, E),
        Post => (if Find_Map_Bad'Result = 0 then
                   (for all I in Index range A'First .. Last => A (I) /= E));

      M : constant Index_Map := Find_All (A);
   begin
      if Contains (M, E) then
         return Find_Map_Bad (M);
      else
         return 0;
      end if;
   end Find_Upto;
end;
