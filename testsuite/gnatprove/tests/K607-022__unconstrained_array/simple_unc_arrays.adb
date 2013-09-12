package body Simple_Unc_Arrays is pragma SPARK_Mode (On); 
  ---------
   -- Add --
   ---------

   function Add (A, B : Table) return Table is
   begin
      return C : Table (A.Last) do
         for I in 1 .. A.Last loop
            pragma Loop_Invariant
              ((for all J in 1 .. I-1 => C.V (J) = A.V (J) + B.V (J))
--              and then
--                 (for all K in I .. A.Last => C.V (K) = C.V'Old (K))
               );

            C.V (I) := A.V (I) + B.V (I);
         end loop;
      end return;
   end Add;

   -------------
   -- Reverse --
   -------------

  procedure Inverse (A : in out Table) is
      AV_Old : constant Values := A.V;
      Low  : Positive := 1;
      High : Natural := A.Last;

   begin
      while Low < High loop
         pragma Loop_Invariant
           ((for all J in 1 .. Low - 1  => (A.V (J) = AV_Old (A.Last - J + 1)))
--            and then
--              (for all J in Low -1 .. A.Last => (A.V (J) = A.V'Old (J)))
            );

         Swap (A.V (Low), A.V (High));
         Low  := Low + 1;
         High := High - 1;
      end loop;
   end Inverse;

   ---------
   -- Min --
   ---------

   function Min (A : Table) return Value is
     Res : Value := A.V (1);
   begin
      for I in 2 .. A.Last loop
         pragma Loop_Invariant (for all J in 1 .. I - 1 => Res <= A.V (J));

         if Res > A.V (I) then
            Res := A.V (I);
         end if;
      end loop;

      return Res;
   end Min;

  ---------
   -- Max --
   ---------

   function Max (A : Table) return Value is
   begin
     return Res : Value := A.V (1) do
       for I in 2 .. A.Last loop
          pragma Loop_Invariant (for all J in 1 .. I - 1 => Res >= A.V (J));

         if Res < A.V (I) then
            Res := A.V (I);
         end if;
       end loop;
     end return;
   end Max;

   -------------
   -- Average --
   -------------

   function Average (A : Table) return Value is
      Sum     : Value := 0;

   begin
      for I in 1 .. A.Last loop
        Sum := Sum + A.V (I);
      end loop;

      return Sum / Value (A.Last);
   end Average;

   ------------
   -- Search --
   ------------

   function Search (A : Table; V : Value) return Natural is
      Pos : Natural := 0;
   begin
      for I in A.V'range loop
         pragma Loop_Invariant (for all J in 1 .. I - 1 => A.V (J) /= V);

         if A.V (I) = V then
            Pos := I;
            exit;
         end if;
      end loop;

      return Pos;
   end Search;

   -----------------
   -- Bubble_Sort --
   -----------------

   function Bubble_Sort (A: Table) return Table is
      Bull : Boolean  := True;
      Res  : Table := A;
   begin
      while Bull loop
         Bull := False;
         for I in 1 .. Res.Last - 1 loop
            if Res.V (I + 1) < Res.V (I) then
               Swap (Res.V (I), Res.V (I+1));
               Bull := True;
            end if;
         end loop;
      end loop;
      return Res;
   end Bubble_Sort;

   ----------------
   -- Quick_Sort --
   ----------------

   procedure Quick_Sort (A : in out Table) is

      procedure Q_S (First, Last : Natural);
      -- for the recursive call

      procedure Q_S (First, Last : Natural) is
         Pivot_Index, Right, Left : Natural;
         Pivot_Value: Value;
      begin
         if First < Last then
            Pivot_Index := (First + Last + 1) / 2;
            Pivot_Value := A.V (Pivot_Index);
            Left  := First;
            Right := Last;
            loop
--               pragma Assert
--                 (  (for all J in First .. Left - 1 => A.V (J) <= A.V (J+1))
--                  and then
--                    (for all J in Right + 1 .. Last => A.V (J) <= A.V (J+1)));

               while Left < Last and then A.V (Left) < Pivot_Value loop
                  Left := Left + 1;
               end loop;

               while Right > First and then A.V (Right) > Pivot_Value loop
                  Right := Right - 1;
               end loop;

               exit when Left >= Right;

               Swap (A.V (Left), A.V (Right));

               if Left < Last and Right > First then
                  Left := Left + 1;
                  Right := Right - 1;
               end if;
            end loop;

            if Right > First then
               Q_S (First, Right - 1);
            end if;

            if Left < Last then
               Q_S (Left, Last);
            end if;
         end if;
     end Q_S;

   begin
      Q_S (1, A.Last);
   end Quick_Sort;

procedure Swap (V, W : in out Value) is pragma SPARK_Mode (On); 
      Tmp : Value;
   begin
      Tmp := V;
      V   := W;
      W   := Tmp;
   end Swap;

end Simple_Unc_Arrays;
