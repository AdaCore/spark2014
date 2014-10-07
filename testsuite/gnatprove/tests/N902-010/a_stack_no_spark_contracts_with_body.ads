pragma SPARK_Mode (On);
package A_Stack_No_SPARK_Contracts_With_Body is
   Stack_Size : constant := 100;
   subtype Item is Integer range 0 .. 20;

   function Is_Empty return Boolean;
   function Is_Full return Boolean;
   function Top return Item with
     Pre => not Is_Empty;

   procedure Push (It : in Item) with
     Pre => not Is_Full;

   procedure Pop (It : out Item) with
     Pre => not Is_Empty;

end A_Stack_No_SPARK_Contracts_With_Body;
