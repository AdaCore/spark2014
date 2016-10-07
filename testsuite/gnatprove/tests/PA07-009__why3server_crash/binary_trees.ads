package Binary_Trees with SPARK_Mode is
   pragma Unevaluated_Use_Of_Old (Allow);

   Max : constant := 100;

   type Index_Type is range 1 .. Max;
   subtype Extended_Index_Type is Index_Type'Base range 0 .. Max;
   type Position_Type is (Left, Right, Top);
   subtype Direction is Position_Type range Left .. Right;

   type Pos_Array is array (Index_Type range <>) of Direction;
   type Path_Type (L : Extended_Index_Type := 0) is record
      A : Pos_Array (1 .. L) := (others => Left);
      K : Boolean := False;
   end record;

   type Model_Type is array (Index_Type) of Path_Type;

   type Tree is private with Default_Initial_Condition => True;

   function Top (T : Tree) return Extended_Index_Type;

   function Parent (T : Tree; I : Index_Type) return Extended_Index_Type with
     Pre  => I /= Top (T);

   function Position (T : Tree; I : Index_Type) return Direction with
     Pre  => I /= Top (T) and then Parent (T, I) /= 0;

   function Model (T : Tree) return Model_Type with
     Post => (if Top (T) /= 0 then Model'Result (Top (T)).K
                  and then Model'Result (Top (T)).L = 0)
     and then
       (for all I in Index_Type =>
          (if I /= Top (T) then
               (if Parent (T, I) /= 0
                and then Model'Result (Parent (T, I)).K
                then Model'Result (I).K
                and then Model'Result (I).L =
                      Model'Result (Parent (T, I)).L + 1
                and then Model'Result (I).A =
                      Model'Result (Parent (T, I)).A & Position (T, I)
                else not Model'Result (I).K)));

   function Peek (T : Tree; I : Index_Type; D : Direction) return Extended_Index_Type with
     Pre  => Model (T) (I).K,
     Post => (if Peek'Result /= 0 then
                Position (T, Peek'Result) = D
              and then Parent (T, Peek'Result) = I);

   procedure Extract (T : in out Tree; I : Index_Type; D : Direction; V : out Tree) with
     Pre  => Model (T) (I).K,
     Post => Top (V) = Peek (T, I, D) and then Top (T) = Top (T)'Old
     and then
     (for all J in Index_Type =>
        Model (T)'Old (J).K = (Model (T) (J).K or Model (V) (J).K)
      and then not (Model (T) (J).K and Model (V) (J).K))
     and then Model (T) (I).K
     and then (for all J in Index_Type =>
                 (if Model (T) (J).K then Model (T) (J).A = Model (T)'Old (J).A))
     and then (for all J in Index_Type =>
                 (if Model (V) (J).K
                  then Model (T) (I).A & D & Model (V) (J).A = Model (T)'Old (J).A));

   procedure Plug (T : in out Tree; I : Index_Type; D : Direction; V : Tree) with
     Pre =>  Model (T) (I).K and then Peek (T, I, D) = 0 and then
     (for all J in Index_Type => not (Model (T) (J).K and Model (V) (J).K)),
     Post => Top (V) = Peek (T, I, D) and then Top (T) = Top (T)'Old
     and then
       (for all J in Index_Type =>
        Model (T) (J).K = (Model (T)'Old (J).K or Model (V) (J).K))
     and then (for all J in Index_Type =>
                 (if Model (T)'Old (J).K then Model (T) (J).A = Model (T)'Old (J).A))
     and then (for all J in Index_Type =>
                 (if Model (V) (J).K
                  then Model (T)'Old (I).A & D & Model (V) (J).A = Model (T) (J).A));

   procedure Plug (T : in out Tree; I : Index_Type; D : Direction) with
     Pre =>  Model (T) (I).K and then Peek (T, I, D) = 0 and then
     (for some J in Index_Type => not (Model (T) (J).K)),
     Post => Top (T) = Top (T)'Old and then Peek (T, I, D) /= 0
     and then
       (for all J in Index_Type =>
        Model (T) (J).K = (Model (T)'Old (J).K or J = Peek (T, I, D)))
     and then (for all J in Index_Type =>
                 (if Model (T)'Old (J).K then Model (T) (J).A = Model (T)'Old (J).A))
     and then Model (T)'Old (I).A & D = Model (T) (Peek (T, I, D)).A;

   procedure Init (T : in out Tree) with
     Pre  => Top (T) = 0,
     Post => Top (T) /= 0
     and (for all I in Index_Type => (if I /= Top (T) then not Model (T) (I).K));
private

   type Cell is record
      Left, Right, Parent : Extended_Index_Type := 0;
      Position            : Position_Type := Top;
   end record;
   type Cell_Array is array (Index_Type) of Cell;
   type Index_Array is array (Index_Type range <>) of Index_Type;

   type Tree is record
      Top : Extended_Index_Type := 0;
      C   : Cell_Array;
   end record
     with Type_Invariant => Tree_Structure (Tree);

   function Tree_Structure (T : Tree) return Boolean;
end Binary_Trees;
