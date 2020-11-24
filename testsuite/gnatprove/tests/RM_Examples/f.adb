function F (S : String) return Integer
  with SPARK_Mode,
       Post => F'Result in 0 .. 999
is
   subtype Control_Chars is Character range '0' .. '3';
   Control_Char : Control_Chars with Relaxed_Initialization;
   Valid        : Boolean with Relaxed_Initialization;
begin
   if S'Length >= 6 then
      Valid := S (S'First .. S'First + 3) = "ABCD";
      if Valid and then S (S'First + 4) in Control_Chars then
         Valid := True;
         Control_Char := S (S'First + 4);
      else
          Valid := False;
      end if;
   else
      Valid := False;
   end if;

   if Valid then
      case Control_Char is
         when '0' => return 0;
         when '1' => return 7;
         when '2' => return 42;
         when '3' => return 99;
      end case;
   else
      return 999;
   end if;
end F;
