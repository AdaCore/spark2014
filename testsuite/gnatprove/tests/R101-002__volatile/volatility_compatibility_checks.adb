package body Volatility_Compatibility_Checks is
   package body Pkg4 is
      procedure Op (X : in out Aaa.T1) is
         use Aaa;
      begin
         X := X + 1;
      end Op;
   begin
      Op (Aaa.T1 (X2));
   end Pkg4;

end Volatility_Compatibility_Checks;
