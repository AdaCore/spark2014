package body Test is

   procedure Init (C : out Container; Value : in out String_Pointer) is
   begin
      C := (Elem => Value);
      Value := null;
   end Init;

   function Init_Test return Container is
      S : String_Pointer := new String'("TEST");
      C : Container;
   begin
      Init (C, S);
      return C;
   end Init_Test;

end Test;
