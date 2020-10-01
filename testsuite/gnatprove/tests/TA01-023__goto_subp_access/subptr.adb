procedure Subptr is
   G : Integer := 0;

   procedure Iterate
     (Process : not null access procedure (Name, Value : String))
   is null;

   procedure Check_It (Name, Value : in String) is
   begin
      G := G + 1;
   end Check_It;

begin
   goto Leave;
   Iterate (Check_It'Access);
<<Leave>>
   Iterate (Check_It'Access);
end;
