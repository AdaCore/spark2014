procedure Flow with SPARK_Mode is

   type T is record
      C1, C2 : Integer;
   end record;

   procedure Test (X1, X2 : Integer; Y1, Y2 : out Integer)
     with Post    => Y1 = X1 and Y2 = X2,
          Depends => (Y1 => X1, Y2 => X2)
   is
      Proxy : T;
   begin
      Proxy :=
        (declare
            Local : constant T := (C1 => X1, C2 => X2);
         begin
            Local);

      Y1 := Proxy.C1;
      Y2 := Proxy.C2;
      --  A convoluted way to assign Y1 with X1 and Y2 with X2
   end Test;

   V1, V2 : Integer;

begin
   Test (1, 2, V1, V2);
end;
