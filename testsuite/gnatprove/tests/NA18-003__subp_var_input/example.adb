procedure Example is

   X : Integer;

   procedure Try_It (Y : Integer) is
      subtype Sample_Type is Integer range X .. Y;
      Sample : Sample_Type;
   begin
      Sample := 10;
   end Try_It;

begin
   X := 5;
   Try_It (20);
end Example;
