package body Loops with SPARK_Mode is

   procedure Loop1 (A : in out Nat_Array)is
   begin
      for I in A'Range loop
         A (I) := 0;
         declare
            A_Begins : constant Nat_Array := A (A'First .. I);
         begin
            pragma Loop_Invariant
              (for all I in A_Begins'Range => A_Begins (I) = 0);
         end;
      end loop;
   end Loop1;

   procedure Loop2 (A : in out Nat_Array) is
   begin
      for I in A'Range loop
         A (I) := 0;
         declare
            A_Length : constant Natural := I - A'First + 1;
         begin
            pragma Loop_Invariant
              (for all I in 1 .. A_Length => A (A'First + I) = 0);
         end;
      end loop;
   end Loop2;

   procedure Loop3 (A : in out Nat_Array; Bad : out Boolean) is
   begin
      Bad := False;
      for I in A'Range loop
         A (I) := 0;
         for J in A'First .. I loop
            if A (J) /= 0 then
               Bad := True;
            end if;
         end loop;
         pragma Loop_Invariant
           (for all J in A'First .. I => A (J) = 0);
      end loop;
   end Loop3;

   procedure Loop4 (A : in out Nat_Array; Bad : out Boolean) is
   begin
      for I in A'Range loop
         A (I) := 0;
         pragma Loop_Invariant
           (for all J in A'First .. I => A (J) = 0);
         declare
            A_Begins : constant Nat_Array := A (A'First .. I);
         begin
            for J in A_Begins'Range loop
               if A (J) /= 0 then
                  Bad := True;
               end if;
            end loop;
         end;
      end loop;
   end Loop4;

end Loops;
