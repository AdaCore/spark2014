procedure Fake is
   X : Integer := 0;

   generic
   package P is
      Y : constant Integer := X;
   end;

   package Q is new P;

begin
   null;
end;
