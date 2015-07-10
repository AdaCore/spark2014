package body P2 is
   protected body Protected_Type is
      function Foo return Integer is (5);

      entry Dummy when True is
         X : Integer := Foo;
      begin
         null;
      end Dummy;

      procedure Bar is
      begin
         Something := 1;
      end Bar;

      procedure Baz is
         procedure Nested
           with Pre => True
         is
         begin
            Something_Else := 10;
         end Nested;
      begin
         Nested;
      end Baz;

      procedure Wibble is
      begin
         Baz;
      end Wibble;

      procedure Wobble (X : out Integer) is
      begin
         X := Foo;
      end Wobble;
   end Protected_Type;

   procedure Outside_Caller (X : out Integer) is
   begin
      X := Protected_Object.Foo;
      Protected_Object.Bar;
   end Outside_Caller;

   procedure Call_Caller (Y : out Integer) is
   begin
      Outside_Caller (Y);
   end Call_Caller;
end P2;
