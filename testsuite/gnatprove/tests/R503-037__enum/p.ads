package P with SPARK_Mode => On is

   package Bad with SPARK_Mode => Off is

      type T is (One, Two, Three);

   end;

   use type Bad.T;

   X : constant Boolean := (Bad.One = Bad.One);

end;
