package body Parser_Utilities is

   function Foo (I : Integer) return Boolean
   is
      Val : Boolean := (I = 0);
   begin
      return Val;
   end Foo;

   procedure P
   is
   begin
      if True then null;
      elsif Foo (0) then null;
      end if;
   end P;

end Parser_Utilities;
