package Serial_Numbers is
   type Serial_Number is range 1000 .. Integer'Last;
   procedure Get_Next (Number : out Serial_Number);
end Serial_Numbers;
