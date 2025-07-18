package Prunt with
  SPARK_Mode => On
is

   type Dimensioned_Float is new Long_Float with
     Dimension_System =>
      ((Unit_Name => Millimeter, Unit_Symbol => "mm", Dim_Symbol => "Length"),
       (Unit_Name => Second, Unit_Symbol => "s", Dim_Symbol => "Time"));

   subtype Length is Dimensioned_Float with
       Dimension => (Symbol => "mm", Millimeter => 1, others => 0);

   subtype Time is Dimensioned_Float with
       Dimension => (Symbol => "s", Second => 1, others => 0);

   pragma Warnings (Off, "assumed to be");
   mm        : constant Length      := 1.0;
   s         : constant Time        := 1.0;
   pragma Warnings (On, "assumed to be");

   subtype Crackle is Dimensioned_Float with
       Dimension => (Symbol => "mm/s⁵", Millimeter => 1, Second => -5);

   type Feedrate_Profile_Times_Index is range 1 .. 4;
   type Feedrate_Profile_Times is array (Feedrate_Profile_Times_Index) of Time with
     Dynamic_Predicate => (for all T of Feedrate_Profile_Times => T <= 1.0E10 * s and T >= 0.0 * s);

   function Crackle_At_Time (T1 : Time; T : Time) return Crackle;

end Prunt;
