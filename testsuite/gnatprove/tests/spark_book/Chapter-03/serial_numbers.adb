package body Serial_Numbers is

   Next_Number : Serial_Number := Serial_Number'First;

   procedure Get_Next (Number : out Serial_Number) is
   begin
      Number := Next_Number;
      Next_Number := Next_Number + 1;
   end Get_Next;

end Serial_Numbers;
