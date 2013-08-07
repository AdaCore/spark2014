package body Contract_Cases
   with SPARK_Mode
is
   X, Y : Natural;

   procedure Square (Num_In  : in     Natural;
                     Num_Out :    out Natural)
      with Contract_Cases => (Num_Out < 10 => Num_Out <  100, --  uninitialized
                              Num_Out > 10 => Num_Out >= 81,  --  uninitialized
                              others       => Num_Out =  100)
   is
   begin
      Num_Out := Num_In * Num_In;
   end Square;

   procedure Double is
      pragma Global ((Input  => X,
                      Output => Y));
      pragma Contract_Cases ((Y < 5  => Y <  10,  --  uninitialized
                              Y > 5  => Y >= 12,  --  uninitialized
                              others => Y =  10));
   begin
      Y := 2 * X;
   end Double;
end Contract_Cases;
