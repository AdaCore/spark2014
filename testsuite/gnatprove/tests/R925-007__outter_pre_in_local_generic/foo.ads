with Types;

generic
   Buffer : in out Types.Buffer;
package Foo
is
   function Get (Pos : Natural) return Integer;
--     with
--        Pre => Buffer'First <= Buffer'Last;

private
   function Get (Pos : Natural) return Integer
   is (Buffer ((if Pos in Buffer'Range then Pos else Buffer'First)));
end Foo;
