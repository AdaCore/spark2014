package Parent is
   type Remote_Camera is tagged private;
   type Aperture is (Eight, Sixteen);
   procedure Focus (Cam : in out Remote_Camera);

private
   type Remote_Camera is tagged record
      FStop : Aperture := Eight;
   end record;
end Parent;
