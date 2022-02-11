with Ada.Numerics.Big_Numbers.Big_Integers;

package Nouse is

   package BI renames Ada.Numerics.Big_Numbers.Big_Integers;
   subtype Big_Integer is BI.Big_Integer with Ghost;
   subtype Big_Natural is BI.Big_Natural with Ghost;
   subtype Big_Positive is BI.Big_Positive with Ghost;
   use type BI.Big_Integer;

   procedure P;

end Nouse;
