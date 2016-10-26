package body Entities
with
   SPARK_Mode,
   Refined_State => (State => (Current_ID, Current_Cycles))
is

   Current_ID     : ID_Index;
   Current_Cycles : Positive;

   -------------------------------------------------------------------------

   procedure Init
   with
      Refined_Global  => (Output => (Current_ID, Current_Cycles)),
      Refined_Depends => ((Current_ID, Current_Cycles) => null)
   is
   begin
      Current_ID     := ID_Index'First;
      Current_Cycles := Positive'Last;
   end Init;

   -------------------------------------------------------------------------

   function Get_Current_ID return ID_Index
   with
      Refined_Global => (Input => Current_ID),
      Refined_Post   => Get_Current_ID'Result = Current_ID
   is
   begin
      return Current_ID;
   end Get_Current_ID;

   -------------------------------------------------------------------------

   procedure Set_Current_ID (Value : ID_Index)
   with
      Refined_Global => (Output => Current_ID, Proof_In => Current_Cycles),
      --  Refined_Depends => (Current_Id => Value),
      Refined_Post   => Current_ID = Value
         and Current_Cycles = Current_Cycles'Old
   is
   begin
      Current_ID := Value;
   end Set_Current_ID;

   -------------------------------------------------------------------------

   function Get_Current_Cycles return Positive
   with
      Refined_Global => (Input => Current_Cycles),
      Refined_Post   => Get_Current_Cycles'Result = Current_Cycles
   is
   begin
      return Current_Cycles;
   end Get_Current_Cycles;

   -------------------------------------------------------------------------

   procedure Set_Current_Cycles (Value : Positive)
   is
   begin
      Current_Cycles := Value;
   end Set_Current_Cycles;

end Entities;
