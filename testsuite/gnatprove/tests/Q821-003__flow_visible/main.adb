with P;

procedure Main (Dummy : Float) is
   procedure My_Flip is new P.Flip;
   --  At this instance the refinement of P.State is not visible
begin
   My_Flip;
end;
