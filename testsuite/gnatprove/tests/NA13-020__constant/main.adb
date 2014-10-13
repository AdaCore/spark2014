with Sink;
with Skp.Subjects;
with SK;
use type SK.Word64;

procedure Main
with
   Global  => (Output        => Sink.The_Sink),
   Depends => (Sink.The_Sink => null)
is
begin
   Sink.The_Sink := Skp.Subjects.Get_PML4_Address (0);
   Sink.The_Sink := SK.Word64 (Skp.Subjects.Get_Event (0, 0).Dst_Subject);
end Main;
