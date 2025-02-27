with Ada.Text_IO;
with GNAT.OS_Lib;

package body Abrupt_Program_Exit with
  SPARK_Mode => Off,
  Refined_State => (Error_State => (Ghost_Error_Status, Ghost_Error_Message))
is

   Ghost_Error_Status  : Integer := 0 with Ghost;
   Ghost_Error_Message : access Error_Message_Type'Class with Ghost;

   function To_String (E : Error_Message_Type) return String is ("");

   function Error_Status return Integer is
     (Ghost_Error_Status);

   function Error_Message return Error_Message_Type'Class is
     (if Ghost_Error_Message = null then Error_Message_Type'(null record)
      else Ghost_Error_Message.all);

   procedure Do_Exit (Status : Integer; Msg : Error_Message_Type'Class) is

      procedure Register_Exit_Info with Ghost is
      begin
         Ghost_Error_Status := Status;
         Ghost_Error_Message := new Error_Message_Type'Class'(Msg);
      end Register_Exit_Info;

   begin
      Register_Exit_Info;
      Ada.Text_IO.Put_Line (Ada.Text_IO.Standard_Error, To_String (Msg));
      GNAT.OS_Lib.OS_Exit (Status);
   end Do_Exit;

end Abrupt_Program_Exit;
