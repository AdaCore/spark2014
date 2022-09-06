procedure Empty is

   ---------
   -- 1-D --
   ---------

   procedure Signed with Pre => True is
      type T is array (Integer range <>) of Integer;
      X : T := [];  --  @RANGE_CHECK:FAIL
   begin
      null;
   end;

   procedure Unsigned with Pre => True is
      type Index is mod 4;
      type T is array (Index range <>) of Integer;
      X : T := [];  --  @RANGE_CHECK:FAIL
   begin
      null;
   end;

   procedure Enum with Pre => True is
      type Index is (A,B,C);
      type T is array (Index range <>) of Integer;
      X : T := [];  --  @RANGE_CHECK:FAIL
   begin
      null;
   end;

   ---------
   -- 2-D --
   ---------

   procedure Signed2 with Pre => True is
      type T is array (Natural range <>, Integer range <>) of Integer;
      X : T := [];  --  @RANGE_CHECK:FAIL
   begin
      null;
   end;

   procedure Unsigned2 with Pre => True is
      type Index is mod 4;
      type T is array (Natural range <>, Index range <>) of Integer;
      X : T := [];  --  @RANGE_CHECK:FAIL
   begin
      null;
   end;

   procedure Enum2 with Pre => True is
      type Index is (A,B,C);
      type T is array (Natural range <>, Index range <>) of Integer;
      X : T := [];  --  @RANGE_CHECK:FAIL
   begin
      null;
   end;

begin
   Signed;
   Unsigned;
   Enum;
   Signed2;
   Unsigned2;
   Enum2;
end;
