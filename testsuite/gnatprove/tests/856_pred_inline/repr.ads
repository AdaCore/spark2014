with Interfaces;
package Repr
with SPARK_Mode
is

   type Zero_Ten is range 0 .. 10;
   subtype One_Ten is Zero_Ten range Zero_Ten'First + 1 .. Zero_Ten'Last;

   type Ar1 is array (One_Ten) of Zero_Ten;

   type Rec2_Base is record
      R1s  : Ar1;
   end record;

   subtype Rec2 is Rec2_Base
   with Predicate =>
     (for all S of Rec2.R1s =>
        S in One_Ten and then
        S > 5);

   subtype Int8 is Interfaces.Unsigned_8;

   type Rec3_Base is record
      R16 : Rec2_Base;
      R17 : Interfaces.Unsigned_8;
   end record;

   subtype Rec3 is Rec3_Base
   with Predicate =>
     Rec3.R16 in Rec2 and
     Rec3.R17 in Int8;

   type Meter_Type_Base is record
      R26 :   Rec3_Base;
   end record;

   subtype Meter_Type is Meter_Type_Base
   with Predicate => Meter_Type.R26 in Rec3;

   procedure My_Procedure (Meter : in out Meter_Type_Base)
   with Post => (Meter in Meter_Type);

end Repr;
