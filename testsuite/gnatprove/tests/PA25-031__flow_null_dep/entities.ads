package Entities
with
   SPARK_Mode,
   Abstract_State => State
is

   subtype ID_Index is Positive range 1 .. 10;

   procedure Init
   with
      Global  => (Output => State),
      Depends => (State => null),
      Post    => Get_Current_ID = ID_Index'First
         and then Get_Current_Cycles = Positive'Last;

   procedure Set_Current_ID (Value : ID_Index)
   with
      Global  => (In_Out => State),
      Depends => (State =>+ Value),
      Post    => Get_Current_ID = Value
         and Get_Current_Cycles = Get_Current_Cycles'Old;

   function Get_Current_ID return ID_Index
   with
      Global => (Input => State);

   procedure Set_Current_Cycles (Value : Positive)
   with
      Global  => (In_Out => State),
      Depends => (State  =>+ Value),
      Post    => Get_Current_Cycles = Value;

   function Get_Current_Cycles return Positive
   with
      Global => (Input => State);

end Entities;
