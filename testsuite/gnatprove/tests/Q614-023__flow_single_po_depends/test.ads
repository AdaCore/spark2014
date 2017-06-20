package Test is

   protected PO is

      procedure Increment
        with Global => null,
             Depends => (PO => PO);

   private

      Count : Natural := 0;

   end PO;

end Test;
