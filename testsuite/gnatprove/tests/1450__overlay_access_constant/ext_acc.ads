--  Inner holds a named access-to-constant component, so Outer is not deep:
--  named access-to-constant types are not subjected to ownership rules. The
--  fields of these types must not be touched when marking the overlay below,
--  as the designated type might not be marked yet. Such an overlay is never
--  precisely supported anyway.

package Ext_Acc with SPARK_Mode is
   type U8 is mod 2 ** 8 with Size => 8;

   type Cst is access constant Integer;

   type Inner is record
      P : Cst;
   end record with Alignment => 8;

   type Outer is record
      K : Inner;
   end record with Alignment => 8;

   type Buf is array (1 .. 8) of U8 with Alignment => 8;
end Ext_Acc;
