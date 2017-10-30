package body State
with Refined_State => (State => (Ext_Value, Local_Value))
is

   Ext_Value : Natural := 0
   with
      Atomic,
      Async_Writers;

   Local_Value : Natural := 0;

   procedure Update
   is
   begin
      Local_Value := Ext_Value;
   end Update;

   function Get return Natural is (Local_Value);

end State;
