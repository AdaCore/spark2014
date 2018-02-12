package body P is
   function Dummy return String is
   begin
      return X : String (1 .. V) do -- reference to V should be rejected
         X := (others => ' ');
      end return;
   end;
end;
