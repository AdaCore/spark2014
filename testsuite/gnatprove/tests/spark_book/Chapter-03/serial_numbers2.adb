package body Serial_Numbers2 is

   Next_Number : Serial_Number;

   procedure Get_Next (Number : out Serial_Number) is
   begin
      Number := Next_Number;
      Next_Number := Next_Number + 1;
   end Get_Next;

begin -- package initialization code
   Next_Number := Serial_Number'First;
end Serial_Numbers2;
