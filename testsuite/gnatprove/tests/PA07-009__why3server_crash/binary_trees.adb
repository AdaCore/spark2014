package body Binary_Trees with SPARK_Mode is

   function Tree_Structure (T : Tree) return Boolean is
     ((if T.Top /= 0 then T.C (T.Top).Parent = 0
       and then T.C (T.Top).Position = Top)
      and then
        (for all I in Index_Type =>
             (if T.C (I).Left /= 0 then T.C (T.C (I).Left).Position = Left
              and then T.C (T.C (I).Left).Parent = I))
      and then
        (for all I in Index_Type =>
             (if T.C (I).Right /= 0 then T.C (T.C (I).Right).Position = Right
              and then T.C (T.C (I).Right).Parent = I))
      and then
        (for all I in Index_Type =>
             (if T.C (I).Parent /= 0 then T.C (I).Position in Left .. Right))
      and then
        (for all I in Index_Type =>
             (if T.C (I).Parent /= 0 and then T.C (I).Position = Left
              then T.C (T.C (I).Parent).Left = I))
      and then
        (for all I in Index_Type =>
             (if T.C (I).Parent /= 0 and then T.C (I).Position = Right
              then T.C (T.C (I).Parent).Right = I)));

   function Top (T : Tree) return Extended_Index_Type is (T.Top);

   function Parent (T : Tree; I : Index_Type) return Extended_Index_Type is
     (T.C (I).Parent);

   function Position (T : Tree; I : Index_Type) return Direction is
     (T.C (I).Position);

   function Model (T : Tree) return Model_Type is
      type Boolean_Array is array (Index_Type) of Boolean;

      function Next (ToDo : Boolean_Array) return Extended_Index_Type with
        Post =>
          (if Next'Result = 0 then (for all I in ToDo'Range => not ToDo (I))
           else ToDo (Next'Result))
      is
      begin
         for I in ToDo'Range loop
            pragma Loop_Invariant (for all J in 1 .. I - 1 => not ToDo (J));
            if ToDo (I) then
               return I;
            end if;
         end loop;
         return 0;
      end Next;

      R    : Model_Type;
      ToDo : Boolean_Array := (others => False);
      I    : Extended_Index_Type := T.Top;
      N    : Extended_Index_Type := 0 with Ghost;
   begin
      if T.Top = 0 then
         return R;
      end if;

      ToDo (T.Top) := True;
      R (T.Top) := (0, (1 .. 0 => Left), True);

      while I /= 0 loop
         pragma Loop_Invariant (ToDo (I));
         pragma Loop_Invariant
           (for all J in Index_Type =>
              (if ToDo (J) then R (J).K));
         pragma Loop_Invariant (R (T.Top).K and R (T.Top).L = 0);
         pragma Loop_Invariant
           (for all J in Index_Type =>
              (if R (J).K and J /= T.Top then T.C (J).Parent /= 0
               and then R (T.C (J).Parent).K
               and then R (J).L = R (T.C (J).Parent).L + 1
               and then R (J).A = R (T.C (J).Parent).A & T.C (J).Position));
         pragma Loop_Invariant
           (for all J in Index_Type =>
              (if T.C (J).Parent /= 0 and then R (T.C (J).Parent).K then
                    R (J).K or ToDo (T.C (J).Parent)));
         pragma Loop_Invariant
           (for all J in Index_Type =>
              (if R (J).K and then J /= T.Top then not ToDo (T.C (J).Parent)));
         pragma Loop_Invariant (for all J in Index_Type => R (J).L <= N);
         pragma Loop_Invariant (N < Max);
         pragma Loop_Variant (Increases => N);

         pragma Assert (if T.C (I).Left /= 0 then T.C (I).Left /= T.C (I).Right);
         pragma Assert (T.C (I).Left /= I);

         declare
            J : Extended_Index_Type;
         begin
            J := T.C (I).Left;
            if J /= 0 then
               pragma Assert (T.C (J).Parent = I);
               pragma Assert (T.C (J).Position = Left);
               pragma Assert (not R (J).K);
               R (J) := (R (I).L + 1, R (I).A & Left, True);
               ToDo (J) := True;
               pragma Assert (R (J).A = R (I).A & Left);
               pragma Assert (R (J).A = R (T.C (J).Parent).A & T.C (J).Position);
            end if;
            J := T.C (I).Right;
            if J /= 0 then
               pragma Assert (T.C (J).Parent = I);
               pragma Assert (T.C (J).Position = Right);
               pragma Assert (not R (J).K);
               R (J) := (R (I).L + 1, R (I).A & Right, True);
               ToDo (J) := True;
               pragma Assert (R (J).A = R (I).A & Right);
               pragma Assert (R (J).A = R (T.C (J).Parent).A & T.C (J).Position);
            end if;
         end;
         ToDo (I) := False;
         I := Next (ToDo);
         N := N + 1;
         pragma Assume (if I /= 0 then N < Max);
         pragma Assert
           (for all J in Index_Type =>
              (if R (J).K and J /= T.Top then T.C (J).Parent /= 0
               and then R (T.C (J).Parent).K
               and then R (J).A = R (T.C (J).Parent).A & T.C (J).Position));
      end loop;
      pragma Assert (for all I in ToDo'Range => not ToDo (I));
      return R;
   end Model;

   function Peek (T : Tree; I : Index_Type; D : Direction) return Extended_Index_Type is (0);

   procedure Extract (T : in out Tree; I : Index_Type; D : Direction; V : out Tree) is null;

   procedure Plug (T : in out Tree; I : Index_Type; D : Direction; V : Tree) is null;

   procedure Plug (T : in out Tree; I : Index_Type; D : Direction) is null;

   procedure Init (T : in out Tree) is null;

end Binary_Trees;
