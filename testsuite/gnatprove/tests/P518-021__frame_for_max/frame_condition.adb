package body Frame_Condition with SPARK_Mode is

   procedure Update_Max (A : in out Cell_Array) is
      K   : Positive;
      Max : Natural;
   begin
      if A'Length = 0 then
         return;
      end if;

      K := A'First;
      Max := 0;

      loop
         if A (K).Value > Max then
            Max := A (K).Value;
         end if;
         A (K).Max_Left := Max;
         pragma Loop_Invariant (K in A'Range);
         pragma Loop_Invariant
           (for all I in A'First .. K => A (I).Value <= Max);
         pragma Loop_Invariant
           (for all I in A'First .. K =>
              (for all J in I .. K =>
                   A (I).Value <= A (J).Max_Left));
         exit when K = A'Last;
         K := K + 1;
      end loop;

      K := A'Last;
      Max := 0;

      loop
         if A (K).Value > Max then
            Max := A (K).Value;
         end if;
         A (K).Max_Right := Max;
         pragma Loop_Invariant (K in A'Range);
         pragma Loop_Invariant
           (for all I in K .. A'Last => A (I).Value <= Max);
         pragma Loop_Invariant
           (for all I in K .. A'Last =>
              (for all J in I .. A'Last =>
                   A (J).Value <= A (I).Max_Right));
         exit when K = A'First;
         K := K - 1;
      end loop;
   end Update_Max;

   procedure Update_Max_2 (A : in out Cell_Array) is
   begin
      if A'Length = 0 then
         return;
      end if;

      declare
         First : constant Positive := A'First;
         Last  : constant Positive := A'Last;
         generic
            First, Last : Positive;
            with procedure Increment (Index : in out Positive);
            with procedure Set_Max (Index : Positive; Value : Natural);
            with function Get_Max (Index : Positive) return Natural;
            with function Frame (Old_A : Cell_Array) return Boolean;
         procedure Update_One_Max with
           Pre => A'Length > 0,
           Post =>
               ((for all I in First .. Last =>
                       (for all J in I .. Last =>
                          A (I).Value <= Get_Max (J)))
                  and
                    (for all I in Last .. First =>
                         (for all J in I .. First =>
                              A (J).Value <= Get_Max (I))))
           and Frame (A'Old), Global => (Input => (First, Last), In_Out => A);

         procedure Update_One_Max is
            K   : Positive := First;
            Max : Natural := 0;
         begin
            loop
               if A (K).Value > Max then
                  Max := A (K).Value;
               end if;
               Set_Max (K, Max);
               pragma Loop_Invariant (K in A'Range);
               pragma Loop_Invariant
                 ((for all I in First .. K => A (I).Value <= Max)
                  and (for all I in K .. First => A (I).Value <= Max));
               pragma Loop_Invariant
                 ((for all I in First .. K =>
                       (for all J in I .. K =>
                          A (I).Value <= Get_Max (J)))
                  and
                    (for all I in K .. First =>
                         (for all J in I .. First =>
                              A (J).Value <= Get_Max (I))));
               pragma Loop_Invariant (Frame (A'Loop_Entry));
               exit when K = Last;
               Increment (K);
            end loop;
         end Update_One_Max;

         procedure Increment_Left (Index : in out Positive) is
         begin
            Index := Index + 1;
         end Increment_Left;

         procedure Set_Max_Left (Index : Positive; Value : Natural) is
         begin
            A (Index).Max_Left := Value;
         end Set_Max_Left;

         function Get_Max_Left (Index : Positive) return Natural is
           (A (Index).Max_Left)
         with Pre => Index in A'Range;

         function Frame_Left (Old_A : Cell_Array) return Boolean is
           (for all I in A'Range => A (I).Value = Old_A (I).Value)
         with Pre => Old_A'First = A'First and Old_A'Last = A'Last;

         procedure Update_Max_Left is new Update_One_Max
           (First     => First,
            Last      => Last,
            Increment => Increment_Left,
            Set_Max   => Set_Max_Left,
            Get_Max   => Get_Max_Left,
            Frame     => Frame_Left);

         procedure Increment_Right (Index : in out Positive) is
         begin
            Index := Index - 1;
         end Increment_Right;

         procedure Set_Max_Right (Index : Positive; Value : Natural) is
         begin
            A (Index).Max_Right := Value;
         end Set_Max_Right;

         function Get_Max_Right (Index : Positive) return Natural is
           (A (Index).Max_Right)
         with Pre => Index in A'Range;

         function Frame_Right (Old_A : Cell_Array) return Boolean is
           (for all I in A'Range =>
               A (I).Value = Old_A (I).Value
            and A(I).Max_Left = Old_A (I).Max_Left)
         with Pre => Old_A'First = A'First and Old_A'Last = A'Last;

         procedure Update_Max_Right is new Update_One_Max
           (First     => Last,
            Last      => First,
            Increment => Increment_Right,
            Set_Max   => Set_Max_Right,
            Get_Max   => Get_Max_Right,
            Frame     => Frame_Right);

      begin
         Update_Max_Left;
         Update_Max_Right;
      end;
   end Update_Max_2;

   procedure Update_Max_3 (A : in out Cell_Array) is
      type Max_Kind is (Left, Right);

      procedure Increment (Kind : Max_Kind; Index : in out Positive) is
      begin
         case Kind is
            when Left  => Index := Index + 1;
            when Right => Index := Index - 1;
         end case;
      end Increment;

      procedure Set_Max (Kind : Max_Kind; Index : Positive; Value : Natural) is
      begin
         case Kind is
            when Left  => A (Index).Max_Left := Value;
            when Right => A (Index).Max_Right := Value;
         end case;
      end Set_Max;

      procedure Update_One_Max (Kind : Max_Kind) is
         Not_Kind : constant Max_Kind :=
           (case Kind is
               when Left  => Right,
               when Right => Left);
         First : constant Positive :=
           (case Kind is
               when Left  => A'First,
               when Right => A'Last);
         Last  : constant Positive :=
           (case Kind is
               when Left  => A'Last,
               when Right => A'First);

         K   : Positive := First;
         Max : Natural := 0;
      begin
         loop
            if A (K).Value > Max then
               Max := A (K).Value;
            end if;
            Set_Max (Kind, K, Max);
            pragma Loop_Invariant (K in A'Range);
            pragma Loop_Invariant
              ((for all I in First .. K => A (I).Value <= Max)
               and (for all I in K .. First => A (I).Value <= Max));
            pragma Loop_Invariant
              (if Kind = Left then
                  (for all I in A'First .. K =>
                       (for all J in I .. K =>
                            A (I).Value <= A (J).Max_Left)));
            pragma Loop_Invariant
              (if Kind = Right then
                 (for all I in K .. A'Last =>
                      (for all J in I .. A'Last =>
                           A (J).Value <= A (I).Max_Right)));
            pragma Loop_Invariant
              (if Kind = Right then
                 (for all I in A'Range =>
                      A (I).Max_Left = A'Loop_Entry (I).Max_Left));
            exit when K = Last;
            Increment (Kind, K);
         end loop;
      end Update_One_Max;

   begin
      if A'Length = 0 then
         return;
      end if;

      Update_One_Max (Left);
      Update_One_Max (Right);
   end Update_Max_3;

end Frame_Condition;
