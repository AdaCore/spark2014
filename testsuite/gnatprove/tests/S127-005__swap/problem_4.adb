package body Problem_4 with SPARK_Mode => On is

   -------------------
   -- Same_Elements --
   -------------------

   function Same_Elements (Left, Right : List_Type) return Boolean is

      function Count (List : List_Type; Element : Integer) return Natural is
         C : Natural := 0;
      begin
         for I in List'Range loop
            if List (I) = Element then
               C := C + 1;
            end if;
         end loop;
         return C;
      end Count;

   begin
      return
        (for all I in Left'Range =>
           Count (Left, Left (I)) = Count (Right, Left (I)));
   end Same_Elements;

   ----------
   -- Swap --
   ----------

   procedure Swap (List : in out List_Type; I, J : Integer)
   is
      Temp : Integer;
   begin
      Temp     := List (I);
      List (I) := List (J);
      List (J) := Temp;
   end Swap;

end Problem_4;