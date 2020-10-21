procedure Test_Variant with SPARK_Mode is

   type Nat_Array is array (Positive range <>) of Natural;

   subtype Sorted_Array is Nat_Array with
     Predicate =>
       (for all I in Sorted_Array'Range =>
          (for all J in Sorted_Array'Range =>
             (if I < J then Sorted_Array (I) < Sorted_Array (J))));

   procedure Find_Closest (A : Sorted_Array; L, H : in out Positive; E : Natural) with
     Subprogram_Variant => (Increases => L, Decreases => H),
     Pre     => L in A'Range and then H in A'Range
     and then E in A (L) .. A (H),
     Post    => L in A'Range and then H in A'Range
     and then ((L = H and A (L) = E)
               or else (H - 1 = L and A (L) < E and A (H) > E));

   procedure Find_Closest (A : Sorted_Array; L, H : in out Positive; E : Natural)
   is
   begin
      if L = H then
         return;
      elsif A (L) = E then
         H := L;
      elsif A (H) = E then
         L := H;
      elsif L = H - 1 then
         return;
      else
         declare
            M : constant Positive := L + (H - L) / 2;
         begin
            if A (M) = E then
               L := M;
               H := M;
            elsif A (M) > E then
               H := M;
               Find_Closest (A, L, H, E); --@SUBPROGRAM_VARIANT:PASS
            else
               L := M;
               Find_Closest (A, L, H, E); --@SUBPROGRAM_VARIANT:PASS
            end if;
         end;
      end if;
   end Find_Closest;
begin
   null;
end Test_Variant;
