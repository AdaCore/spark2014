with Abrupt_Program_Exit; use Abrupt_Program_Exit;

package Use_Abrupt_Program_Exit with SPARK_mode is

   type Error_Kind is (Input_Error, Overflow_Error);

   type My_Error_Message is new Error_Message_Type with record
      Kind : Error_Kind;
   end record;

   function To_String (E : My_Error_Message) return String is
     (case E.kind is
         when Input_Error    => "Input is incorrect",
         when Overflow_Error => "Numeric computation overflows");

   procedure Get_Digit (X : out Integer) with
     Post => X in 0 .. 9,
     Program_Exit => Error_Status = 1
     and then Error_Message in My_Error_Message
     and then My_Error_Message (Error_Message).Kind = Input_Error;

   function Add (X, Y : Integer) return Integer with
     Side_Effects,
     Pre  => X in 0 .. 9 and Y in 0 .. 9,
     Post => Add'Result in 0 .. 9,
     Program_Exit => X + Y > 9
     and then Error_Status = 2
     and then Error_Message in My_Error_Message
     and then My_Error_Message (Error_Message).Kind = Overflow_Error;

   procedure Play with
     Program_Exit => Error_Status in 1 | 2
     and then Error_Message in My_Error_Message
     and then
       (if Error_Status = 1
        then My_Error_Message (Error_Message).Kind = Input_Error
        else My_Error_Message (Error_Message).Kind = Overflow_Error);

   procedure Auto_Play;

end Use_Abrupt_Program_Exit;
