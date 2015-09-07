with Ada.Characters.Latin_1;
package body Terminal
   with Spark_Mode => On
is
   use type Serial_Port.Status_Type;

   procedure Get_Line (Buffer : out String;
                       Count  : out Natural;
                       Status : out Status_Type) is
      Value       : Serial_Port.Byte;
      Port_Status : Serial_Port.Status_Type;
   begin
      Buffer := (others => ' ');
      Count  := 0;
      Status := Success;
      loop
         pragma Loop_Invariant (Count <= Buffer'Length);

         -- Check to be sure there is space remaining in the buffer.
         if Count = Buffer'Length then
            Status := Insufficient_Space;
            exit;
         end if;

         Serial_Port.Read (Value, Port_Status);

         -- Check to be sure a byte was successfully read.
         if Port_Status /= Serial_Port.Success then
            Status := Port_Failure;
            exit;
         end if;

         -- We are done if a carriage return is read.
         exit when Character'Val (Value) = Ada.Characters.Latin_1.CR;

         -- Convert Value (a Byte) to a character and append to Buffer
         Buffer (Buffer'First + Count) := Character'Val (Value);
         Count := Count + 1;
      end loop;
   end Get_Line;

end Terminal;
