package body Dynamic_Ranges with SPARK_Mode is

   function Search (A : Int_Array; E : Integer) return Natural is
   begin
      for I in A'Range loop
         if A (I) = E then
            return I;
         end if;
      end loop;

      return 0;
   end Search;

   function Resize (A : Int_Array) return Dyn_Int_Array is
      A2 : constant Int_Array := A (1 .. Dyn_Int_Array'Last);
   begin
      pragma Assert (A2'First = Dyn_Int_Array'First);
      pragma Assert (A2'Last = Dyn_Int_Array'Last);
      return Dyn_Int_Array (A2);
   end Resize;

   function Search_0 (A : Int_Array) return Natural is
      subtype Dyn1 is Natural range 0 .. A'Last;
      subtype Dyn2 is Dyn1 range 0 .. Dyn1'Last - 1;
      C : constant Dyn2 := Dyn2'Last - 1;
      subtype Dyn3 is Dyn2 range 0 .. C;

      function Nested return Dyn3 with
      --  The precondition should not be needed as it is implied by
      --  Search_0's precondition.
        Pre  => C <= A'Last and then
           A'First <= A'Last and then A'Last - A'First >= 2,
        Post => (Nested'Result = 0
                 and then (for all I in A'First .. C => A (I) /= 0))
        or else (Nested'Result >= A'First and then A (Nested'Result) = 0);

      function Nested return Dyn3 is
      begin
         for I in A'First .. Dyn3'Last loop
            declare
               E : constant Integer := A (I);
            begin
               if E = 0 then
                  return I;
               end if;
            end;
            pragma Loop_Invariant
              (for all J in A'First .. I => A (J) /= 0);
         end loop;
         return 0;
      end Nested;

   begin
      if A (A'Last) = 0 then
         return A'Last;
      elsif A (A'Last - 1) = 0 then
         return A'Last - 1;
      else
         return Nested;
      end if;
   end Search_0;

   procedure Store_Zero (A : in out Int_Array; I : Positive) is
   begin
      A (I) := 0;
   end Store_Zero;

   procedure All_Zeros (A : in out Int_Array) is
   begin
      for I in A'Range loop
         Store_Zero (A, I);
         pragma Loop_Invariant
           (for all J in A'First .. I => A (J) = 0);
      end loop;
   end;

end Dynamic_Ranges;
