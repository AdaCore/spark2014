pragma SPARK_Mode (On);
package body A_Stack_No_SPARK_Contracts_With_Body is

   subtype Stack_Pointer is Natural range 0 .. Stack_Size;
   subtype Index is Stack_Pointer range 1 .. Stack_Size;
   type Vector is array (Index) of Item;

   SP  : Stack_Pointer;-- := 0;
   Vec : Vector; -- := (others => 0);

   function Is_Empty return Boolean is (SP = 0);

   function Is_Full return Boolean is (SP = Stack_Size);

   function Top return Item is (Vec (SP));

   procedure Push (It : in Item) is
   begin
      SP := SP + 1;
      Vec (SP) := It;
   end Push;

   procedure Pop (It : out Item) is
   begin
      It := Vec (SP);
      SP := SP - 1;
   end Pop;

end A_Stack_No_SPARK_Contracts_With_Body;
