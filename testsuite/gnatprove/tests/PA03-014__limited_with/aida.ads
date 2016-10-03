package Aida with SPARK_Mode is
   pragma Pure;

   type Int64_T is range -2**63 .. (2**63 - 1);
   for Int64_T'Size use 64;

   type Char_T is new Character;

   type String_T is array (Positive range <>) of Char_T;
   pragma Pack (String_T);

end Aida;
