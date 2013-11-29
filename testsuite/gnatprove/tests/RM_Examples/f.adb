function F (S : String) return Integer
  with SPARK_Mode,
       Post => F'Result in 0 .. 999
is
   subtype Control_Chars is Character range '0' .. '3';
   Control_Char : Control_Chars ;
   Valid : Boolean;
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

   pragma Assert_And_Cut (if Valid then Control_Char in Control_Chars);

   -- A conditional flow error will be reported when it used in the following
   -- case as statement flow analysis techniques cannot determine that
   -- Control_Char is initialized when Valid is True.
   -- The Assert_And_Cut verifies that Control_Char is initialized if Valid
   -- is True and the conditional flow which raised the error cannot occur.
   -- The complicated decision process and the details of the string S are
   -- not required to prove the postcondition and so the Assert_And_Cut
   -- cuts out all of the unnecessary complex information gathered from this
   -- process from the proof tool and the eye of the human viewer.

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
