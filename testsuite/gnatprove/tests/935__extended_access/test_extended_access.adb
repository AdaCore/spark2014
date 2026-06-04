procedure Test_Extended_Access with SPARK_Mode is
   type Int_Array is array (Positive range <>) of Integer;
   type Cst_Arr_Access is access constant Int_Array with Extended_Access;

   C : aliased constant Int_Array (1 .. 100) := (others => 1);

   function Get (L, F : Positive) return Cst_Arr_Access with
     Pre => L in C'Range and F in C'Range;

   function Get (L, F : Positive) return Cst_Arr_Access is
   begin
      return C (L .. F)'Access;
   end Get;

   type Arr_Access is access all Int_Array with Extended_Access;

   X : aliased Int_Array (1 .. 100) := (others => 1);
   Y : Arr_Access := X (15 .. 30)'Access;
   --  Here a slice of X is moved, so the rest is lost. There is no way to
   --  observe or borrow a slice using Extended_Access for now.
begin
   null;
end;
