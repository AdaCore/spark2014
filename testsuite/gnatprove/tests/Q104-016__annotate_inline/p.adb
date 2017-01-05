procedure P is

   subtype One_to_Ten is Integer range 1 .. 10;

   procedure Inner (X : Integer);

   procedure Inner (X : Integer) is
      Dummy : constant One_to_Ten := X;  --  @RANGE_CHECK:NONE
      pragma Annotate (GNATprove, Intentional, "range check might fail", "just to demonstrate");
   begin
      pragma Assert (Dummy in 1 .. 10);
   end;

   Eleven : Integer := 11;

begin
   Inner (Eleven);
end;
