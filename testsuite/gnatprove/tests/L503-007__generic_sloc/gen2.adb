package body Gen2 is

   procedure B (X : T) is
   begin
      pragma Assert (T'Last = X);
      null;
   end B;

end Gen2;
