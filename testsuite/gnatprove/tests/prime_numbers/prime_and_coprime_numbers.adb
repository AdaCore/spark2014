with Ada.Numerics.Elementary_Functions;

package body Prime_And_Coprime_Numbers with
  Refined_State => (Prime_Data => Set.Is_Prime)
is

   No_Number_Error : exception;

   -----------------------------------------------------------------------------

   package Set is
      Is_Prime : Number_List_Type;
   end Set;

   function Valid_Prime_Data return Boolean is
     (for all V in Number_List_Type'Range => Set.Is_Prime (V) = Is_Prime (V));

   function Has_Prime (Low, High : Value_Type) return Boolean is
     (for some V in Low .. High => Is_Prime (V));

   -----------------------------------------------------------------------------

   function Initialize_Coprime_List
      (Value : in Value_Type)
      return Number_List_Type
   is
      Result : Number_List_Type;

      function Euclid
         (Left  : in Value_Type;
          Right : in Value_Type)
         return Value_Type
      with
        Pre => Left >= 2 and Right >= 0,
        Contract_Cases =>
          (Are_Coprime (Left, Right) => Euclid'Result = 1,
           others                    => Euclid'Result > 1)
      is
         A : Value_Type range 1 .. Value_Type'Last;
         B : Value_Type range 1 .. Value_Type'Last;
         R : Value_Type range 0 .. Value_Type'Last;
      begin
         if Left = 0
         then
            return Right;

         elsif Right = 0
         then
            return Left;
         end if;

         A := Left;
         B := Right;

         loop
            pragma Loop_Invariant (A > 0 and B > 0);
            pragma Loop_Invariant (not (A = 1 and B = 1));
            pragma Loop_Invariant
              (Are_Coprime (A, B) = Are_Coprime (Left, Right));

            R := A mod B;

            exit when R = 0;

            pragma Assume (Are_Coprime (A, B) = Are_Coprime (B, R));

            A := B;
            B := R;
         end loop;

         pragma Assert (not (A = 1 and B > 0));

         return B;
      end Euclid;

   begin
      for Index in Result'Range
      loop
         Result (Index) := Euclid (Value, Index) = 1;
         pragma Loop_Invariant
           (for all V in Result'First .. Index =>
              Result (V) = Are_Coprime (Value, V));
         pragma Annotate (GNATprove, False_Positive, """Result"" might not be initialized",
                          "Result accessed in loop invariant only for indexes previously initialized");
      end loop;

      return Result;
   end Initialize_Coprime_List;

   -----------------------------------------------------------------------------

   function Nearest_Number
      (Number_List : in Number_List_Type;
       Mode        : in Nearest_Mode;
       Value       : in Value_Type)
      return Value_Type
   is
      Right        : Value_Type'Base := Value_Type'First;
      Left         : Value_Type'Base := Value_Type'First;
      Right_Is_Out : Boolean;
      Left_Is_Out  : Boolean;
   begin
      if Number_List (Value)
      then
         return Value;
      end if;

      -- Search a number larger or equal to Value

      if Mode = Up or else Mode = Absolute
      then
         Right := Value_Type'Succ (Value);

         loop
            Right_Is_Out := Right > Number_List'Last;

            exit when
               Right_Is_Out
               or else Number_List (Right);
            pragma Loop_Invariant (Right in Value + 1 .. Number_List'Last);
            pragma Loop_Invariant
              (for all V in Value .. Right => Number_List (V) = False);

            Right := Value_Type'Succ (Right);
         end loop;

      else
         Right_Is_Out := True;
      end if;

      -- Search a number lower than Value

      if Mode = Down or else Mode = Absolute
      then
         Left := Value_Type'Pred (Value);

         loop
            Left_Is_Out := Left < Number_List'First;

            exit when
               Left_Is_Out
               or else Number_List (Left);
            pragma Loop_Invariant (Left in Number_List'First .. Value - 1);
            pragma Loop_Invariant
              (for all V in Left .. Value => Number_List (V) = False);

            Left := Value_Type'Pred (Left);
         end loop;

      else
         Left_Is_Out := True;
      end if;

      -- Select nearest prime

      if not Right_Is_Out
      then
         if not Left_Is_Out
         then
            if abs (Left - Value) <= abs (Right - Value)
            then
               return Left;

            else
               return Right;
            end if;

         else
            return Right;
         end if;

      else
         if not Left_Is_Out
         then
            return Left;

         else
            raise No_Number_Error;
         end if;
      end if;
   end Nearest_Number;

   -----------------------------------------------------------------------------

   function Nearest_Prime_Number
      (Value : in Value_Type;
       Mode  : in Nearest_Mode)
      return Value_Type
   is
   begin
      return Nearest_Number (Set.Is_Prime, Mode, Value);
   end Nearest_Prime_Number;

   -----------------------------------------------------------------------------

   procedure Eratosthenes with
     Global => (Output => Set.Is_Prime),
     Post   => Valid_Prime_Data
   is
      Index_1 : Value_Type;
      Index_3 : Value_Type'Base;

      use Ada.Numerics.Elementary_Functions;
   begin
      Set.Is_Prime := (others => True);
      Set.Is_Prime (0) := False;
      Set.Is_Prime (1) := False;

      for Index_2 in 2 .. Value_Type (Sqrt (Float (Max_Value)))
      loop
         pragma Loop_Invariant (Index_2 in 2 .. Max_Value);
         pragma Loop_Invariant
           (for all V in 0 .. Index_2 => Set.Is_Prime (V) = Is_Prime (V));
         pragma Loop_Invariant
           (for all V in Index_2 .. Set.Is_Prime'Last =>
              Set.Is_Prime (V) =
                (for all Div in 2 .. Index_2 - 1 => V mod Div /= 0));

         if Set.Is_Prime (Index_2)
         then
            Index_1 := Index_2;
            Index_3 := 2 * Index_1;

            while Index_3 <= Max_Value
            loop
               Set.Is_Prime (Index_3) := False;

               pragma Loop_Invariant
                 (for all V in 0 .. Index_2 => Set.Is_Prime (V) = Is_Prime (V));
               pragma Loop_Invariant
                 (for all V in Index_2 .. Set.Is_Prime'Last =>
                    Set.Is_Prime (V) =
                      ((for all Div in 2 .. Index_2 - 1 => V mod Div /= 0)
                         and
                       (if V in Index_2 + 1 .. Index_3 then V mod Index_2 /= 0)));
               pragma Loop_Invariant (Index_3 in Index_2 .. Max_Value);
               pragma Loop_Invariant (Index_3 mod Index_2 = 0);

               Index_3 := Index_3 + Index_1;
            end loop;
         end if;
      end loop;
   end Eratosthenes;

   -----------------------------------------------------------------------------

begin
   Eratosthenes;
end Prime_And_Coprime_Numbers;
