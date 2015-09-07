procedure Aggregates is
   type Float_Array is array (Positive range <>) of Float;
   subtype Small_Array is Float_Array (1 .. 10);

   type Row_Range is range -1 .. 1;
   type Col_Range is range  1 .. 4;
   type Table_Array is array (Row_Range, Col_Range) of Integer;

   function Sqrt (X : in Float) return Float is
      Approx    : Float;  -- An approximation of the square root of X
      Tolerance : constant Float := 0.000001 * X;
   begin
      Approx := X / 2.0;
      while abs (X - Approx ** 2) > Tolerance loop
         Approx := 0.5 * (Approx + X / Approx);
      end loop;
      return Approx;
   end Sqrt;

   Small : Small_Array;
   Table : Table_Array;    -- 2D array with 12 elements
   A     : Float := 23.4;
   B     : Float := 19.9;
begin
   Small := (0.0, 1.0, 2.0, 3.0, 4.0, 5.0, 4.0, 3.0, 2.0, 1.0);  -- by position
   Small := (1 .. 10 => 0.0);                                    -- by name
   Small := (1 .. 5 => 0.0, 6 .. 10 => 1.0);
   Small := (1 | 3 | 5 | 7 | 9 => 0.0, others => 1.0);
   Small := (others => A + Sqrt (B));

   -- Assign all elements by position
   Table := ((1, 2, 3, 4),
             (5, 6, 7, 8),
             (9, 8, 7, 6));
   -- Assign rows by name, columns by position
   Table := (-1 => (1, 2, 3, 4),
              0 => (5, 6, 7, 8),
              1 => (9, 8, 7, 6));
   -- Assign all elements by name
   Table := (-1 => (1 .. 4 => 2),
              0 => (1 .. 3 => 3, 4 => 6),
              1 => (2 => 5, others => 7));
   Table := (-1 .. 1 => (1 .. 4 => 0));
   Table := (others => (others => 0));

end Aggregates;
