package body Array_Algorithms
is

   procedure Mismatch (A, B     : in     Generic_Array;
                       Found    :    out Boolean;
                       Location :    out Index_Type)
   is
   begin
      Found := False;
      Location := A'First;

      for I in Index_Type range A'First .. A'Last loop
         if A(I) /= B(I) then
            Found := True;
            Location := I;
            exit;
         end if;

         pragma Loop_Invariant ((for all J in Index_Type range A'First..I =>
                                   A(J) = B(J))
                                and Found = False);
      end loop;

   end Mismatch;


   procedure Find (A        : in     Generic_Array;
                   Val      : in     Value_Type;
                   Found    :    out Boolean;
                   Location :    out Index_Type)
   is
   begin
      Found    := False;
      Location := A'First;

      for I in Index_Type range A'First .. A'Last loop
         if A(I) = Val then
            Found := True;
            Location := I;
            exit;
         end if;

         pragma Loop_Invariant ((for all J in Index_Type range A'First..I =>
                                   A(J) /= Val)
                                and Found = False);
      end loop;

   end Find;

end Array_Algorithms;
