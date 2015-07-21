package Dynamic_Preds_RTE
  with SPARK_Mode
is
   subtype Small is Natural with Dynamic_Predicate => 2 * Small < 100_000;
   subtype Very_Small is Natural with Dynamic_Predicate => Very_Small ** 2 < 100_000;

   type Small_Pair is record
      A : Small;
      B : Very_Small;
   end record;

   type Small_Array is array (1 .. 2) of Small;

   subtype Ordered_Small_Pair is Small_Pair
     with Dynamic_Predicate =>
       Ordered_Small_Pair.A / Ordered_Small_Pair.B = 0;
   subtype Ordered_Small_Array is Small_Array
     with Dynamic_Predicate =>
       Ordered_Small_Array(1) / Ordered_Small_Array(2) = 0;

   procedure Create_Small_Pair (X : out Small_Pair; Y : Integer);
   function Add_Small_Pair (X : Small_Pair) return Integer;

   procedure Create_Small_Array (X : out Small_Array; Y : Integer);
   function Add_Small_Array (X : Small_Array) return Integer;

   procedure Create_Ordered_Small_Pair (X : out Ordered_Small_Pair);
   procedure Create_Ordered_Small_Array (X : out Ordered_Small_Array);

end Dynamic_Preds_RTE;
