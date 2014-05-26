package body Valleys is

   function Create (rG, oG : Gap) return Valley is
   begin
      return (risingGap => rG, otherGap => oG);
   end Create;

end Valleys;
