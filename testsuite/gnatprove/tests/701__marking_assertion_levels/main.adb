pragma Assertion_Level (Silver);
pragma Assertion_Level (Gold, Depends => Silver);

procedure Main  with spark_mode is

   --  Reject multiple Subprogram_Variant aspects

   procedure Subprogram_Variant is

      procedure Do_Smthg (X, Y : Natural) with
        Subprogram_Variant =>
          (Silver => (Decreases => X),
           Gold   => (Decreases => Y));

      procedure Do_Smthg (X, Y : Natural) is
      begin
         if X > 0 and Y > 0 then
            Do_Smthg (X - 1, Y - 1);
         end if;
      end Do_Smthg;


   begin
      null;
   end Subprogram_Variant;

begin
   null;
end Main;
