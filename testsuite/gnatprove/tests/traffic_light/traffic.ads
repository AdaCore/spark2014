package Traffic
  with SPARK_Mode
is

   type Path is (A1North, A1South, A66East, A66West);

   type Light is (Red, Amber, Green);

   type Lights_Type is array (Path) of Light;

   Lights : constant Lights_Type :=
     (A1North | A1South => Red, others => Green);

   type Conflict is record
      Left, Right : Path;
   end record;

   type Conflicts_Type is array (Integer range <>) of Conflict;

   Conflicts : Conflicts_Type (1.. 8);

   function Contains (Cs : Conflicts_Type; C : Conflict) return Boolean
     is ((for Some A of Cs => A = C));

   function Is_Valid (L : Lights_Type) return Boolean is
       (for all C of Conflicts =>
          (L (C.Left) = Red or L (C.Right) = Red));

   procedure To_Green (L : in out Lights_Type; P : Path)
     with Pre =>
       (for all C of Conflicts => L (C.Left) = Red or L (C.Right) = Red) and L (P) = Red and
     (for all C of Conflicts => (if C.Left = P then L (C.Right) = Red)),
          Post => (for all C of Conflicts => L (C.Left) = Red or L (C.Right) =
             Red);

   procedure To_Red (L : in out Lights_Type; P : Path)
     with Pre => Is_Valid (L) and L (P) = Amber,
          Post => Is_Valid (L) and
                  L = L'Old'Update (P => Red);


   procedure To_Amber (L : in out Lights_Type; P : Path)
     with Pre => Is_Valid (L) and L (P) = Green,
          Post => Is_Valid (L) and
                  L = L'Old'Update (P => Amber);

end Traffic;
