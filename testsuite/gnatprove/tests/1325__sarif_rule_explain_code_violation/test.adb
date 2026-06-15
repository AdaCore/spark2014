with Interfaces.C.Strings; use Interfaces.C.Strings;

procedure Test with SPARK_Mode is
   function F return chars_ptr with Post => True is
      C : chars_ptr := New_String ("toto");
   begin
      return C;
   end F;

begin
   null;
end Test;
