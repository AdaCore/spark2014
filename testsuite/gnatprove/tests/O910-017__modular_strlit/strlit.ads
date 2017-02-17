package Strlit with SPARK_Mode is

   type Mod_8 is mod 2 ** 8;
   type Mod_String is array (Mod_8 range <>) of Character;
   type Five is new Mod_String(1..5);
   function DoSome return Integer
      with Post => (DoSome'Result = 10);
end Strlit;
