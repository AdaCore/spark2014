package body Searches
with Spark_Mode
is

   procedure Find_First  (List     : in Array_Type;
                          Value    : in Integer;
                          Position : out Positive) is
   begin
      Position := List'First;
      loop
         exit when List (Position) = Value;
         Position := Position + 1;
         pragma Loop_Invariant
           (Position in List'Range and then
            (for all J in List'First .. Position - 1 => List (J) /= Value));
      end loop;
   end Find_First;

   procedure Find_Only  (List     : in Array_Type;
                         Value    : in Integer;
                         Found    : out Boolean;
                         Position : out Positive) is
   begin
      Position := List'First;
      loop
         exit when Position > List'Last or else List (Position) = Value;
         Position := Position + 1;
         pragma Loop_Invariant
           (Position in List'First .. List'Last + 1 and then
            (for all J in List'First .. Position - 1 => List (J) /= Value));
      end loop;
      Found := Position <= List'Last;
      if not Found then
         Position := List'Last;
      end if;
   end Find_Only;

end Searches;
