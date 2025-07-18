package Abrupt_Program_Exit with
  SPARK_Mode,
  Abstract_State => Error_State,
  Initializes => Error_State
is

   type Error_Message_Type is tagged null record;

   function To_String (E : Error_Message_Type) return String with
     Global => null;

   procedure Do_Exit (Status : Integer; Msg : Error_Message_Type'Class) with
     Global => (In_Out => Error_State),
     No_Return,
     Always_Terminates,
     Program_Exit => Error_Status = Status and Error_Message = Msg;

   function Error_Status return Integer with
     Ghost,
     Global => Error_State;

   function Error_Message return Error_Message_Type'Class with
     Ghost,
     Global => Error_State;

end Abrupt_Program_Exit;
