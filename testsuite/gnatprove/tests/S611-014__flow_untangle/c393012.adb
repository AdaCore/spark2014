procedure C393012 is

   type Ticket is abstract tagged record
      Flight : Natural;
   end record;

   type Tix is access Ticket'Class;
   type Itinerary is array (Positive range 1 .. 3) of Tix;

   procedure TC_Convert (I : Itinerary) is
      T : Ticket'Class := Ticket (I (1).all);
   begin
      null;
   end TC_Convert;

begin
   null;
end C393012;
