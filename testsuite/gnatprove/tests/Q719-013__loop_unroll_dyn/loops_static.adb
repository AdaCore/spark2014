package body Loops_Static with SPARK_Mode is

   procedure Loop1 (A : in out Nat_Array)is
   begin
      for I in 1 .. 2 loop
         A (I) := 0;
         declare
            A_Begins : constant Nat_Array := A (A'First .. I);
         begin
            pragma Assert
              (for all I in A_Begins'Range => A_Begins (I) = 0);
         end;
      end loop;
      pragma Assert (False); --  @ASSERT:FAIL
   end Loop1;

   procedure Loop11 (A : in out Nat_Array)is
   begin
      for I in 1 .. 2 loop
         for J in 1 ..2 loop
            A (I) := 0;
            declare
               A_Begins : constant Nat_Array := A (A'First .. I);
            begin
               pragma Assert
                 (for all I in A_Begins'Range => A_Begins (I) = 0);
            end;
         end loop;
      end loop;
      pragma Assert (False); --  @ASSERT:FAIL
   end Loop11;

   procedure Loop2 (A : in out Nat_Array) is
   begin
      for I in 1 .. 2 loop
         A (I) := 0;
         declare
            A_Length : constant Natural := I - A'First + 1;
         begin
            pragma Assert
              (for all I in 1 .. A_Length => A (A'First + I) = 0);
         end;
      end loop;
      pragma Assert (False); --  @ASSERT:FAIL
   end Loop2;

   procedure Loop3 (A : in out Nat_Array; Bad : out Boolean) is
   begin
      Bad := False;
      for I in 1 .. 2 loop
         A (I) := 0;
         for J in A'First .. I loop
            if A (J) /= 0 then
               Bad := True;
            end if;
         end loop;
         pragma Assert
           (for all J in A'First .. I => A (J) = 0);
      end loop;
      pragma Assert (False); --  @ASSERT:FAIL
   end Loop3;

   procedure Loop4 (A : in out Nat_Array; Bad : out Boolean) is
   begin
      for I in 1 .. 2 loop
         A (I) := 0;
         pragma Assert
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
      pragma Assert (False); --  @ASSERT:FAIL
   end Loop4;

   procedure Loop5 (A : in out Nat_Array; Bad : out Boolean) is
   begin
      Bad := False;
      for I in 1 .. 2 loop
         A (I) := 0;
         if I > A'First then
            for J in A'First .. I loop
               if A (J) /= 0 then
                  Bad := True;
               end if;
            end loop;
         end if;
         pragma Assert
           (for all J in A'First .. I => A (J) = 0);
      end loop;
      pragma Assert (False); --  @ASSERT:FAIL
   end Loop5;

   procedure Loop6 (A : in out Nat_Array; Bad : out Boolean) is
   begin
      Bad := False;
      for I in 1 .. 2 loop
         A (I) := 0;
         if I = A'First then
            Bad := False;
         elsif I = A'Last then
            for J in A'First .. I loop
               if A (J) /= 0 then
                  Bad := True;
               end if;
            end loop;
         end if;
         pragma Assert
           (for all J in A'First .. I => A (J) = 0);
      end loop;
      pragma Assert (False); --  @ASSERT:FAIL
   end Loop6;

   procedure Loop7 (A : in out Nat_Array; Bad : out Boolean) is
   begin
      Bad := False;
      for I in 1 .. 2 loop
         A (I) := 0;
         if I = A'First then
            Bad := False;
         else
            for J in A'First .. I loop
               if A (J) /= 0 then
                  Bad := True;
               end if;
            end loop;
         end if;
         pragma Assert
           (for all J in A'First .. I => A (J) = 0);
      end loop;
      pragma Assert (False); --  @ASSERT:FAIL
   end Loop7;

   procedure Loop8 (A : in out Nat_Array; Bad : out Boolean) is
   begin
      Bad := False;
      for I in 1 .. 2 loop
         A (I) := 0;
         case I is
            when 1 => Bad := False;
            when others =>
               for J in A'First .. I loop
                  if A (J) /= 0 then
                     Bad := True;
                  end if;
               end loop;
         end case;
         pragma Assert
           (for all J in A'First .. I => A (J) = 0);
      end loop;
      pragma Assert (False); --  @ASSERT:FAIL
   end Loop8;

   function Loop9 (A : Nat_Array) return Boolean is
      R   : Nat_Array := A;
   begin
      for I in 1 .. 2 loop
         R (I) := 0;
         if I = A'Last then
            return Bad : Boolean do
               Bad := False;
               for J in A'First .. I loop
                  if R (J) /= 0 then
                     Bad := True;
                  end if;
               end loop;
            end return;
         end if;
         pragma Assert
           (for all J in A'First .. I => R (J) = 0);
      end loop;
      pragma Assert (False); --  @ASSERT:FAIL

      return False;
   end Loop9;

   function Loop10 (A : Nat_Array) return Nat_Array is
      R   : Nat_Array := A;
   begin
      for I in 1 .. 2 loop
         R (I) := 0;
         if I = A'Last then
            return Res : Nat_Array (A'Range) do
               Res := R;
            end return;
         end if;
         pragma Assert
           (for all J in A'First .. I => R (J) = 0);
      end loop;
      pragma Assert (False); --  @ASSERT:FAIL

      return A;
   end Loop10;

end Loops_Static;
