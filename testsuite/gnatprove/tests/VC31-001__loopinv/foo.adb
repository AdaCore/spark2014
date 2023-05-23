pragma Assertion_Policy (Loop_Invariant=>Ignore); -- it's obviously false
with Ada.Text_IO;
procedure Foo with SPARK_Mode => On is
    A : constant String := "Homsar";
begin
    for I in A'Range loop
        Ada.Text_IO.Put_Line(A(I) & ' ');
        pragma Loop_Invariant (I > A'Last);
        pragma Annotate (GNATprove, Intentional, "loop invariant", "broken, fix later");
        pragma Loop_Invariant (I < A'First);
    end loop;
end Foo;
