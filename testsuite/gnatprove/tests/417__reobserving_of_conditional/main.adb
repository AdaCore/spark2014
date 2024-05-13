
procedure Main with SPARK_Mode is
   type Cell;
   type Tree is access Cell;
   type Cell is record
      Value : Integer;
      Left  : Tree;
      Right : Tree;
   end record;
   function Good (X : access constant Cell) return access constant Cell
     with Subprogram_Variant => (Structural => X);
   function Bad (X : access constant Cell) return access constant Cell
     with Subprogram_Variant => (Structural => X);
   function Bad2 (X : access constant Cell) return access constant Cell
     with Subprogram_Variant => (Structural => X);
   function Bad3 (X : access constant Cell) return access constant Cell
     with Subprogram_Variant => (Structural => X);
   function Good_Loop (X : access constant Cell) return access constant Cell;
   function Bad_Loop (X : access constant Cell) return access constant Cell;
   function Bad_Loop2 (X : access constant Cell) return access constant Cell;
   function Bad_Loop3 (X : access constant Cell) return access constant Cell;

   function Rand (X : Integer) return Boolean with Import, Global => null;

   function Good (X : access constant Cell) return access constant Cell is
   begin
      if X = null then
         return null;
      end if;
      declare
         Result : access constant Cell := X;
      begin
         case X.Value is
            when 0 =>
               Result :=
                 (if Result.Left = null then Result.Right else Result.Left);
            when 1 =>
               Result := (if Result.Right = null then Result.Left else
                            (case Result.Right.Value is
                                when 42 => Result.Right.Left,
                                when 36 => Result.Right.Right,
                                when 13 => Result.Left,
                                when others => Result.Right));
            when 42 =>
               Result := Result.Left;
               Result := (if Result = null then Result else Result.Left);
            when others =>
               Result := (case Result.Value is
                             when 37 => Result.Right,
                             when others => Result.Left);
         end case;
         return (if Result = null or else Rand (Result.Value) then Result
                 else Good (Result));
      end;
   end Good;

   function Bad (X : access constant Cell) return access constant Cell is
   begin
      if X = null then
         return null;
      end if;
      declare
         Result : access constant Cell := X;
      begin
         case X.Value is
            when 0 =>
               Result :=
                 (if Result.Left = null then Result.Right else Result.Left);
            when 1 =>
               Result := (if Result.Right = null then Result.Left else
                            (case Result.Right.Value is
                                when 42 => Result.Right.Left,
                                when 36 => Result.Right.Right,
                                when 13 => Result.Left,
                                when others => Result.Right));
            when 42 =>
               Result := (if Result = null then Result else Result.Left);
            when others =>
               Result := (case Result.Value is
                             when 37 => Result.Right,
                             when others => Result.Left);
         end case;
         return (if Result = null or else Rand (Result.Value) then Result
                 else Bad (Result)); -- @SUBPROGRAM_VARIANT:FAIL
      end;
   end Bad;

   function Bad2 (X : access constant Cell) return access constant Cell is
   begin
      if X = null then
         return null;
      end if;
      declare
         Result : access constant Cell := X;
      begin
         case X.Value is
            when 0 =>
               Result :=
                 (if Result.Left = null then Result.Right else Result.Left);
            when 1 =>
               Result := (if Result.Right = null then Result.Left else
                            (case Result.Right.Value is
                                when 42 => Result.Right.Left,
                                when 36 => Result.Right.Right,
                                when 13 => Result,
                                when others => Result.Right));
            when 42 =>
               Result := Result.Left;
               Result := (if Result = null then Result else Result.Left);
            when others =>
               Result := (case Result.Value is
                             when 37 => Result.Right,
                             when others => Result.Left);
         end case;
         return (if Result = null or else Rand (Result.Value) then Result
                 else Bad2 (Result)); -- @SUBPROGRAM_VARIANT:FAIL
      end;
   end Bad2;

   function Bad3 (X : access constant Cell) return access constant Cell is
   begin
      if X = null then
         return null;
      end if;
      declare
         Result : access constant Cell := X;
      begin
         case X.Value is
            when 0 =>
               Result :=
                 (if Result.Left = null then Result.Right else Result);
            when 1 =>
               Result := (if Result.Right = null then Result.Left else
                            (case Result.Right.Value is
                                when 42 => Result.Right.Left,
                                when 36 => Result.Right.Right,
                                when 13 => Result.Left,
                                when others => Result.Right));
            when 42 =>
               Result := Result.Left;
               Result := (if Result = null then Result else Result.Left);
            when others =>
               Result := (case Result.Value is
                             when 37 => Result.Right,
                             when others => Result.Left);
         end case;
         return (if Result = null or else Rand (Result.Value) then Result
                 else Bad3 (Result)); -- @SUBPROGRAM_VARIANT:FAIL
      end;
   end Bad3;

   function Good_Loop (X : access constant Cell) return access constant Cell is
      Result : access constant Cell := X;
   begin
      loop
         pragma Loop_Variant (Structural => Result);
         if Result = null then
            return null;
         end if;
         case Result.Value is
            when 0 =>
               Result :=
                 (if Result.Left = null then Result.Right else Result.Left);
            when 1 =>
               Result := (if Result.Right = null then Result.Left else
                            (case Result.Right.Value is
                                when 42 => Result.Right.Left,
                                when 36 => Result.Right.Right,
                                when 13 => Result.Left,
                                when others => Result.Right));
            when 42 =>
               Result := Result.Left;
               Result := (if Result = null then Result else Result.Left);
            when others =>
               Result := (case Result.Value is
                             when 37 => Result.Right,
                             when others => Result.Left);
         end case;
         exit when Result = null;
         exit when Rand (Result.Value);
      end loop;
      return Result;
   end Good_Loop;

   function Bad_Loop (X : access constant Cell) return access constant Cell is
      Result : access constant Cell := X;
   begin
      loop
         pragma Loop_Variant (Structural => Result); -- @LOOP_VARIANT:FAIL
         if Result = null then
            return null;
         end if;
         case Result.Value is
            when 0 =>
               Result :=
                 (if Result.Left = null then Result.Right else Result.Left);
            when 1 =>
               Result := (if Result.Right = null then Result.Left else
                            (case Result.Right.Value is
                                when 42 => Result.Right.Left,
                                when 36 => Result.Right.Right,
                                when 13 => Result.Left,
                                when others => Result.Right));
            when 42 =>
               Result := (if Result = null then Result else Result.Left);
            when others =>
               Result := (case Result.Value is
                             when 37 => Result.Right,
                             when others => Result.Left);
         end case;
         exit when Result = null;
         exit when Rand (Result.Value);
      end loop;
      return Result;
   end Bad_Loop;

   function Bad_Loop2 (X : access constant Cell) return access constant Cell is
      Result : access constant Cell := X;
   begin
      loop
         pragma Loop_Variant (Structural => Result); -- @LOOP_VARIANT:FAIL
         if Result = null then
            return null;
         end if;
         case Result.Value is
            when 0 =>
               Result :=
                 (if Result.Left = null then Result.Right else Result);
            when 1 =>
               Result := (if Result.Right = null then Result.Left else
                            (case Result.Right.Value is
                                when 42 => Result.Right.Left,
                                when 36 => Result.Right.Right,
                                when 13 => Result.Left,
                                when others => Result.Right));
            when 42 =>
               Result := Result.Left;
               Result := (if Result = null then Result else Result.Left);
            when others =>
               Result := (case Result.Value is
                             when 37 => Result.Right,
                             when others => Result.Left);
         end case;
         exit when Result = null;
         exit when Rand (Result.Value);
      end loop;
      return Result;
   end Bad_Loop2;

   function Bad_Loop3 (X : access constant Cell) return access constant Cell is
      Result : access constant Cell := X;
   begin
      loop
         pragma Loop_Variant (Structural => Result); -- @LOOP_VARIANT:FAIL
         if Result = null then
            return null;
         end if;
         case Result.Value is
            when 0 =>
               Result :=
                 (if Result.Left = null then Result.Right else Result.Left);
            when 1 =>
               Result := (if Result.Right = null then Result.Left else
                            (case Result.Right.Value is
                                when 42 => Result.Right.Left,
                                when 36 => Result,
                                when 13 => Result.Left,
                                when others => Result.Right));
            when 42 =>
               Result := Result.Left;
               Result := (if Result = null then Result else Result.Left);
            when others =>
               Result := (case Result.Value is
                             when 37 => Result.Right,
                             when others => Result.Left);
         end case;
         exit when Result = null;
         exit when Rand (Result.Value);
      end loop;
      return Result;
   end Bad_Loop3;

begin
   null;
end Main;
