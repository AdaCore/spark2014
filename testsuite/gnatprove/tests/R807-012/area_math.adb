with Ada.Text_IO; use Ada.Text_IO;
with Ada.Strings.Fixed;
with Ada.Strings; use Ada.Strings;

package body Area_Math
with SPARK_Mode => On
is

   function E (From, To : Address_Type) return Ensemble is
   begin
      return (Max => 1, Size => 1, From => (1 => From), To => (1 => To));
   end E;

   procedure Put_Line (E : Ensemble)
     with SPARK_Mode => Off
   is
   begin
      Put ("{");

      for I in 1 .. E.Size loop
         if I > 1 then
            Put (", ");
         end if;

         Put (Ada.Strings.Fixed.Trim(E.From(I)'Img, Both) & " .. " & Ada.Strings.Fixed.Trim(E.To(I)'Img, Both));
      end loop;

      Put_Line ("}");
   end Put_Line;

   ----------
   -- "or" --
   ----------

   function "or"
     (A1, A2 : Ensemble)
      return Ensemble
     with SPARK_Mode => Off
   is
      Result : Ensemble (A1.Max + A2.Max);
      It : array (1 .. 2) of Integer := (1, 1);
      Size : array (1 .. 2) of Integer := (A1.Size, A2.Size);
      Cur : Integer;
      Sec : Integer;

      Found : Boolean;

   begin
      Result.Size := 0;

      loop
         Result.Size  := Result.Size  + 1;

         if It (2) > A2.Size or else (It (1) <= A1.Size and then A1.From (It(1)) < A2.From (It(2))) then
            Cur := 1;
            Sec := 2;

            Result.From (Result.Size) := A1.From (It (Cur));
            Result.To (Result.Size) := A1.To (It (Cur));

            It (1) := It (1) + 1;
         else
            Cur := 2;
            Sec := 1;

            Result.From (Result.Size) := A2.From (It (Cur));
            Result.To (Result.Size) := A2.To (It (Cur));

            It (2) := It (2) + 1;
         end if;


         -- include everything from the second array that is crossing the first
         -- array

         loop
            Found := False;

            loop
               if Sec = 1 then
                  exit when It (1) > A1.Size;

                  if A1.From (It (1)) in Result.From (Result.Size) .. Result.To (Result.Size) then
                     if A1.To (It (1)) in Result.From (Result.Size) .. Result.To (Result.Size) then
                        -- Just increment secondary array here, the secondary array
                        -- is included in the first one.
                        null;
                     else
                        Result.To (Result.Size) := A1.To (It (1));
                     end if;

                     Found := True;
                     It (1) := It (1) + 1;
                  else
                     Sec := 2;
                     exit;
                  end if;
               else
                  exit when It (2) > A2.Size;

                  if A2.From (It (2)) in Result.From (Result.Size) .. Result.To (Result.Size) then
                     if A2.To (It (2)) in Result.From (Result.Size) .. Result.To (Result.Size) then
                        -- Just increment secondary array here, the secondary array
                        -- is included in the first one.
                        null;
                     else
                        Result.To (Result.Size) := A2.To (It (2));
                     end if;

                     Found := True;
                     It (2) := It (2) + 1;
                  else
                     Sec := 1;
                     exit;
                  end if;
               end if;
            end loop;

            exit when Found = False;
         end loop;

         exit when It (1) > A1.Size and then It (2) > A2.Size;
      end loop;

      return Result;
   end "or";

   -----------
   -- "and" --
   -----------

   function "and"
     (A1, A2 : Ensemble)
      return Ensemble
     with SPARK_Mode => Off
   is
      Result : Ensemble (A1.Max + A2.Max);
      It : array (1 .. 2) of Integer := (1, 1);
      Size : array (1 .. 2) of Integer := (A1.Size, A2.Size);
      Cur : Integer;
      Sec : Integer;
   begin
      Result.Size := 0;

      loop
         if It (2) > A2.Size or else (It (1) <= A1.Size and then A1.From (It(1)) < A2.From (It(2))) then
            Cur := 1;
            Sec := 2;
         else
            Cur := 2;
            Sec := 1;
         end if;


         -- include everything from the second array that is crossing the first
         -- array

         loop
            if Sec = 1 then
               exit when It (1) > A1.Size;

               if A1.From (It (1)) in A2.From(It(2)) .. A2.To(It(2)) then
                  Result.Size := Result.Size + 1;
                  Result.From (Result.Size) := A1.From (It (1));

                  if A1.To (It (1)) in A2.From(It(2)) .. A2.To(It(2)) then
                     -- The secondary region is all included in the primary one, this is a intersect

                     Result.To (Result.Size) := A1.To (It (1));
                     It (1) := It (1) + 1;
                  else
                     -- Only the beginning is included

                     Result.To (Result.Size) := A2.To (It (2));
                     exit;
                  end if;
               end if;
            else
               exit when It (2) > A2.Size;

               if A2.From (It (2)) in A1.From(It(1)) .. A1.To(It(1)) then
                  Result.Size := Result.Size + 1;
                  Result.From (Result.Size) := A2.From (It (2));

                  if A2.To (It (2)) in A1.From(It(1)) .. A1.To(It(1))  then
                     -- The secondary region is all included in the primary one, this is a intersect

                     Result.To (Result.Size) := A2.To (It (2));
                     It (2) := It (2) + 1;
                  else
                     -- Only the beginning is included

                     Result.To (Result.Size) := A1.To (It (1));
                     exit;
                  end if;
               end if;
            end if;
         end loop;

         It (Cur) := It (Cur) + 1;

         exit when It (1) > A1.Size and then It (2) > A2.Size;
      end loop;

      return Result;
   end "and";

   -----------
   -- "not" --
   -----------

   function "not"
     (E : Ensemble)
      return Ensemble
   is
      Result : Ensemble (E.Size + 1);
      Prev, Next : Address_Type := 0;
      Skip : Boolean;
   begin
      Result.Size := 0;
      Result.From := (others => 0);
      Result.To := (others => 0);

      for I in 0 .. E.Size loop
         Skip := False;

         if I = 0 then
            if E.Size /= 0 and then E.From (I + 1) = Address_Type'First then
               Skip := True;
            else
               Prev := Address_Type'First;
            end if;
         else
            Prev := E.To (I) + 1;
         end if;

         if I = E.Size then
            if E.Size /= 0 and then E.To (I) = Address_Type'Last then
               Skip := True;
            else
               Next := Address_Type'Last;
            end if;
         else
            Next := E.From (I + 1) - 1;
         end if;

         if not Skip then
            pragma Assert (Prev <= Next);
            pragma Assert (if Result.Size > 0 then Prev > Result.To (Result.Size));
            --pragma Assert (if Result.Size >= 1 then Result.To (Result.Size) - Prev > 1);

            Result.Size := Result.Size + 1;
            Result.From (Result.Size) := Prev;
            Result.To (Result.Size) := Next;

            pragma Assert (for all B in Prev .. Next => B < Result);
            --pragma Assert (for all B in Prev .. Next => not B < E);

            pragma Assert (Result.From (Result.Size) = Address_Type'First or else (I /= 0 and then Result.From (Result.Size) = E.To (I) + 1));
            pragma Assert (Result.To (Result.Size) = Address_Type'Last or else Result.To (Result.Size) = E.From (I + 1) - 1);
         end if;

         pragma Loop_Invariant (Result.Size <= I + 1);
         pragma Loop_Invariant (if not Skip then Result.Size > 0);
         pragma Loop_Invariant (if not Skip then Result.From (Result.Size) = Address_Type'First or else (I /= 0 and then Result.From (Result.Size) = E.To (I) + 1));
         pragma Loop_Invariant (if not Skip then Result.To (Result.Size) = Address_Type'Last or else (I < E.Size and then Result.To (Result.Size) = E.From (I + 1) - 1));
         pragma Loop_Invariant
           (if Skip then
              (I = 0 and then E.Size /= 0 and then E.From (I + 1) = Address_Type'First)
               or (I = E.Size and then E.Size /= 0 and then E.To (I) = Address_Type'Last));

         --         pragma Loop_Invariant (if I < E.Size and then E.Size > 0 and then Result.Size > 0 then Result.To (Result.Size) = E.From (I + 1) - 1);

         pragma Loop_Invariant (Is_Consistent (E));
         pragma Loop_Invariant (if Result.Size > 0 then
                                  (if I < E.Size and then E.Size > 0 then

                                      Result.To (Result.Size) = E.From (I + 1) - 1 and Result.To (Result.Size) < E.To (I + 1) + 1
                                   else I = E.Size));

--           pragma Loop_Invariant (if Result.Size > 0 then
--                                    (if I > 0 I and then E.Size > 0 then Result.From (Result.Size) = E.To (I) + 1
--                                     else I = E.Size));

         pragma Loop_Invariant (Is_Consistent (Result));

      end loop;

      return Result;
   end "not";

end Area_Math;
