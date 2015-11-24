package Road_Traffic
  with SPARK_Mode
is

   type Path is (North, South, East, West);

   type Light is (Red, Yellow, Green);

   type Lights_Type is array (Path) of Light;

   Lights : constant Lights_Type :=
     (North | South => Red, others => Green);

   type Conflict is record
      Left, Right : Path;
   end record;

   type Conflicts_Type is array (Integer range <>) of Conflict;

   Conflicts : Conflicts_Type (1.. 8);

   function Safety_Property (L : Lights_Type) return Boolean is
       (for all C of Conflicts =>
          (L (C.Left) = Red or L (C.Right) = Red));

   procedure To_Green (L : in out Lights_Type; P : Path)
     with Pre =>
     Safety_Property (L) and L (P) = Red and
     (for all C of Conflicts => C.Left /= C.Right and
                               (if C.Left = P then L (C.Right) = Red) and
                                (if C.Right = P then L (C.Left) = Red)),
          Post => Safety_Property (L);

   procedure To_Red (L : in out Lights_Type; P : Path)
     with Pre => Safety_Property (L) and L (P) = Yellow,
          Post => Safety_Property (L) and
                  L = L'Old'Update (P => Red);


   procedure To_Yellow (L : in out Lights_Type; P : Path)
     with Pre => Safety_Property (L) and L (P) = Green,
          Post => Safety_Property (L) and
                  L = L'Old'Update (P => Yellow);

end Road_Traffic;
