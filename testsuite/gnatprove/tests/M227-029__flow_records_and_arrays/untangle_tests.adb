package body Untangle_Tests is

   type Coordinate is record
     X : Float;
     Y : Float;
     Z : Float;
     W : Float;
   end record;

   type Coordinate_List is array (Positive range 1 .. 3) of Coordinate;

   type Triangle is record
      Vertices : Coordinate_List;
      Normal   : Coordinate;
   end record;

   type Triangle_List is array (Positive range 1 .. 100) of Triangle;

   type Bitfield is array (Positive range 1 .. 1000) of Boolean;

   --  Tests R.X
   function New_Coordinate (X, Y, Z : Float) return Coordinate
   is
      R : Coordinate;
   begin
      R.X := X;
      R.Y := Y;
      R.Z := Z;
      R.W := 1.0;
      return R;
   end New_Coordinate;

   --  Tests A (...)
   procedure Swap_Triangle (L    : in out Triangle_List;
                            A, B : Positive)
   is
      Tmp : Triangle := L (A);
   begin
      L (A) := L (B);
      L (B) := Tmp;
   end Swap_Triangle;

   --  Tests A (...)
   procedure Sieve (P : out Bitfield)
   is
      N : Positive;
   begin
      P := (1      => False,
            others => True);

      for I in Positive range Bitfield'Range loop
         if P (I) then
            N := 2 * I;
            while N <= Bitfield'Last loop
               P (N) := False;
               N := N + I;
            end loop;
         end if;
      end loop;
   end Sieve;

   --  Tests A (...) . B (...) . C
   procedure Transform (TL : in out Triangle_List;
                        O  : Coordinate)
   is
   begin
      for T in Positive range Triangle_List'Range loop
         for V in 1 .. 3 loop
            TL (T).Vertices (V).X := TL (T).Vertices (V).X + O.X;
            TL (T).Vertices (V).Y := TL (T).Vertices (V).Y + O.Y;
            TL (T).Vertices (V).Z := TL (T).Vertices (V).Z + O.Z;
         end loop;
      end loop;
   end Transform;

   --  Tests R.X.{subcomponents} := {record}
   procedure Set_Normal (T : in out Triangle;
                         N : Coordinate)
   is
   begin
      T.Normal := N;
   end Set_Normal;


end Untangle_Tests;
