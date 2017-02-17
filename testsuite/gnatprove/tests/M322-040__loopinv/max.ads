package Max is
   type Index is range 1 .. 10;
   type Arr is array (Index) of Integer;

   procedure Step (A: in Arr; I : Index; Max: in out Integer);
   procedure MaxElement_P1B1_A (A: in Arr; Max: out Integer);
end Max;
