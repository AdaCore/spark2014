
procedure Test with SPARK_Mode is
   type List_Cell;
   type List is access List_Cell;
   type List_Cell is record
      V : Integer;
      N : List;
   end record;

   Y : List := new List_Cell'(2, null) with Relaxed_Initialization;
   X : List := new List_Cell'(3, Y) with Relaxed_Initialization;
begin
   null;
end Test;
