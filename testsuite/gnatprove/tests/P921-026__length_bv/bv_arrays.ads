package BV_Arrays with SPARK_Mode is
   type Mod_8 is mod 2 ** 8;
   type Mod_16 is mod 2 ** 16;

   type My_Array is array (Mod_16 range <>) of Natural;

   function Zero return Mod_16 is (0);

   function Create (C : Mod_16) return My_Array with
     Post => Create'Result'First = 0 and then Create'Result'Last = C;
end BV_Arrays;
