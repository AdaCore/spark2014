procedure Test_Bad_Extended_Access with SPARK_Mode is
   type Int_Array is array (Positive range <>) of Integer;
   type Arr_Access is access all Int_Array with Extended_Access;

   X : aliased Int_Array (1 .. 100) := (others => 1);

   function Get (L, F : Positive) return Arr_Access with
     Pre => L in X'Range and F in X'Range;

   function Get (L, F : Positive) return Arr_Access is
   begin
      return X (L .. F)'Access; --  This is a move; it should be rejected
   end Get;
begin
   null;
end;
