with taxi;

procedure Req_n522 is

   xa : Integer := 1;

   xb : Integer := 2;

   xc : Integer := 3;

   procedure yellow is new taxi (thing => Integer);

begin -- Req_n522

   yellow (xa, xb, xc);

end Req_n522;
