procedure Test with SPARK_Mode is

   package P is
      type E is private;

      type Root is tagged null record;

      procedure Bad (X : Root; Y : out E);

   private
      type E is new Integer with Type_Invariant => E >= 0, Default_Value => 0;

      type Child is new Root with null record;

      --  Dispatching operations are always considered to be boundary

      procedure Bad (X : Child; Y : out E); -- @INVARIANT_CHECK:FAIL

      package Nested is

         type P_Child is private;

         --  Hidden dispatching operations are also considered to be boundary

         procedure Bad (X : P_Child; Y : out E) with Pre => True; -- @INVARIANT_CHECK:FAIL
      private
         type P_Child is new Root with null record;
      end Nested;
   end P;

   package body P is

      procedure Bad (X : Root; Y : out E) is
      begin
         Y := 0;
      end Bad;

      procedure Bad (X : Child; Y : out E) is
      begin
         Y := -1;
      end Bad;

      package body Nested is

         procedure Bad (X : P_Child; Y : out E) is
         begin
            Y := -1;
         end Bad;

      end Nested;
   end P;

begin
   null;
end Test;
