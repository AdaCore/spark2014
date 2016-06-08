--  TU: 1. The aspect Type_Invariant’Class is not in SPARK.

package Type_Invariant_Illegal_2 is

   type T1 is tagged private with Type_Invariant'Class => True;
   type T2 is tagged private with Invariant'Class => True;

   type R is tagged null record;

   type T3 is new R with private with Type_Invariant'Class => True;
   type T4 is new R with private with Invariant'Class => True;

   type T5 is abstract tagged private with Type_Invariant'Class => True;
   type T6 is tagged private with Type_Invariant'Class => True;
   type T7 is tagged limited private with Type_Invariant'Class => True;

   type T8 is interface with Type_Invariant'Class => True;

private
   type T1 is tagged null record;
   type T2 is tagged null record;

   type T3 is new R with null record;
   type T4 is new R with null record;

   type T5 is abstract tagged null record;
   type T6 is tagged null record;
   type T7 is tagged limited null record;

end Type_Invariant_Illegal_2;
