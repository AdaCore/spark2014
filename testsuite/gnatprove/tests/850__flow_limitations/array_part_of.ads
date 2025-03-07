package Array_Part_Of with Initializes => B
is
   type My_Arr is array (Positive range <>) of Integer;

   protected PO is
   end PO;

   B : My_Arr (1 .. 5) := (others => 0)
     with Part_Of => PO;

end;
