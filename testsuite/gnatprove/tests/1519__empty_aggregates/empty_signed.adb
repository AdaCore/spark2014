procedure Empty_Signed (Hi : Integer) with SPARK_Mode is
   subtype Index is Integer range Integer'First .. Hi;
   type Vector is array (Index range <>) of Integer;
   --  The dynamic upper bound keeps the aggregate in the frontend tree;
   --  the static lower bound has no representable predecessor.
   V : constant Vector := []; --@RANGE_CHECK:FAIL
   pragma Unreferenced (V);
begin
   null;
end Empty_Signed;
