package body Unbound_Symbol
with
   SPARK_Mode
is
   function Read (State_Ext : in GCounter_Type) return State_Type
   is
      Counter : constant U64 := State_Ext.Counter;
   begin
      return State_Type'(Counter => Counter);
   end Read;

   function Is_Active (State_Ext : in GCounter_Type) return Boolean
   is
      State_Read : constant State_Type := Read (State_Ext);
   begin
      return True; -- Anything goes;
   end Is_Active;

end Unbound_Symbol;
