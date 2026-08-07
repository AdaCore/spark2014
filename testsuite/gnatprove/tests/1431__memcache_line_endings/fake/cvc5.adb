--  Fake prover printing a cvc5-like answer through Ada.Text_IO, so that its
--  line endings are native to the platform, like those of a real prover. The
--  statistics line not namespaced with "resource::" is expected to be filtered
--  out by the memcached wrapper.

with Ada.Text_IO;

procedure Cvc5 is
begin
   Ada.Text_IO.Put_Line ("unsat");
   Ada.Text_IO.Put_Line ("resource::resourceUnitsUsed = 42");
   Ada.Text_IO.Put_Line ("noise::foo = 1");
end Cvc5;
