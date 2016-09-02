--  TU: 1. The aspect Type_Invariant may be specified in SPARK, but only for
--  the completion of a private type.

package Type_Invariant_Illegal is

   type T1 is private with Type_Invariant => True;
   type T2 is private with Invariant => True;

   type R is tagged null record;

   type T3 is new R with private with Type_Invariant => True;
   type T4 is new R with private with Invariant => True;

   type T5 is abstract tagged private with Type_Invariant'Class => True;
   type T6 is tagged private with Type_Invariant => True;
   type T7 is limited private with Type_Invariant => True;

   type T8 is new R with private;
   type T9 is new R with private;

   subtype T10 is T9;
   type T11 is new T9 with private;

private
   type T1 is new Integer;
   type T2 is new Integer;

   type T3 is new R with null record;
   type T4 is new R with null record;

   type T5 is abstract tagged null record;
   type T6 is tagged null record;
   type T7 is limited null record;

   type T8 is new R with null record with Type_Invariant => True;
   type T9 is new R with null record with Invariant => True;

   type T11 is new T9 with null record;

end Type_Invariant_Illegal;
