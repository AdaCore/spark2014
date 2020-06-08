package body Parent is
   procedure Focus (Cam : in out Remote_Camera) is
   begin
      Cam.FStop := Sixteen;
   end Focus;
end Parent;
