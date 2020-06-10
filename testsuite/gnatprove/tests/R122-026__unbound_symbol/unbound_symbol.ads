package Unbound_Symbol
with
   SPARK_Mode
is
   type U64 is mod 2**64;

   type GCounter_Type is limited record
      Counter : U64;
   end record
   with
      Volatile;
      -- Async_Writers

   type State_Type    is limited record
      Counter : U64;
   end record;

   pragma Warnings (GNATprove, Off, "volatile function ""Is_Active"" has no volatile effects",
                    reason => "False_Positive: Is_Active IS a Volatile_Function");
   function Is_Active (State_Ext : in GCounter_Type) return Boolean
   with
      Global => null,
      Pre => True,
      Volatile_Function;

   pragma Warnings (GNATprove, Off, "volatile function ""Read"" has no volatile effects",
                    reason => "False_Positive: Read IS a Volatile_Function");
   function Read (State_Ext : GCounter_Type)
      return State_Type
   with
      Global => null,
      Pre => True,
      Volatile_Function;

end Unbound_Symbol;
