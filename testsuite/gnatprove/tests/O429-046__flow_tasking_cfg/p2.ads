package P2 is
   protected type Protected_Type is
      function Foo return Integer;

      entry Dummy;

      procedure Bar
        with Pre => True;

      procedure Baz
        with Pre => True;

      procedure Wibble
        with Pre => True;

      procedure Wobble (X : out Integer);
   private
      Something      : Integer := 0;
      Something_Else : Integer := 0;
   end Protected_Type;

   Protected_Object : Protected_Type;

   procedure Outside_Caller (X : out Integer);

   procedure Call_Caller (Y : out Integer);
end P2;
