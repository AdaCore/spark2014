procedure P is

   subtype One_to_Ten is Integer range 1 .. 10;

   procedure Inner (X : Integer);

   procedure Inner (X : Integer) is
      pragma Annotate (GNATprove, Intentional, "range check might fail", "just to demonstrate");
      Dummy : constant One_to_Ten := X; --  the above pragma should justify this range check
   begin
      pragma Assert (Dummy in 1 .. 10);
   end;

   Eleven : Integer := 11;

begin
   Inner (Eleven);
end;
