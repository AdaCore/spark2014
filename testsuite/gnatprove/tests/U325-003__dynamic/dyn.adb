procedure Dyn (X : Integer) is

   subtype T is Integer range 1 .. X;

   Y : Integer;
   Z : T with Address => Y'Address, Import;
begin
   null;
end Dyn;
